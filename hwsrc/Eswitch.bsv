package Eswitch;

import Vector::*;
import FIFOF::*;
import GetPut::*;
import ConfigReg::*;
import RegIf::*;
import RmiiTx::*;
import RmiiRx::*;
import Cam::*;
import EswitchRegs::*;

// 本包不认识任何总线：对外只给中立的 RegIf，接哪种总线由 wrap 或装配决定。
//
// 直通式转发：读完 12 字节的两个 MAC 地址就决定去哪，不等整帧。定下来之前的字节
// 存在入口缓冲里，定了再从头放出去，所以转出去的帧与收到的逐字节相同，FCS 原样带着；
// 坏帧照样被转出去（FCS 要到帧尾才知道），换来的是不必给每个口配一整帧的缓冲——
// 那是 SRAM 宏的量级。
//
// 出口按帧归属：一个出口同一时刻只归一个入口，占着的出口不再授给别的帧，那一帧在
// 那个出口上丢掉并记数，不和正在发的帧交错。
//
// 结构上有一条要守住：**一条规则只调一次某个动作方法**。入口规则若直接调
// `tab.learn` 或往所有出口 `enq`，bsc 会把所有入口规则判成互斥，几个口退化成
// 一个口，而且规则冲突分析本身就会炸开（实测编了十五分钟没出来）。所以入口只往
// 自己的暂存线上放，出口各自去取——那也正是交叉开关本来的样子。
typedef struct {
  Bool vlan;
} EswitchCfg;

typedef struct {
  Bit#(8) dat;
  Bool    last;
} Cell deriving (Bits, FShow);

typedef struct {
  Cell    body;
  Bit#(8) target;
} Staged deriving (Bits, FShow);

interface EswitchPins#(numeric type ports);
  interface Vector#(ports, RmiiTxPins) tx;
  interface Vector#(ports, RmiiRxPins) rx;
endinterface

interface EswitchIfc#(numeric type aw, numeric type dw,
                      numeric type ports, numeric type macEntries);
  interface RegIf#(aw, dw) regs;
  interface EswitchPins#(ports) pins;
endinterface

function RmiiTxPins getTxPins(RmiiTxIfc i) = i.pins;
function RmiiRxPins getRxPins(RmiiRxIfc i) = i.pins;

module mkEswitch#(EswitchCfg cfg)(EswitchIfc#(aw, dw, ports, macEntries))
    provisos (Mul#(TDiv#(dw, 8), 8, dw), Add#(_a, 12, aw), Add#(_b, 1, dw),
              Add#(_c, ports, dw), Add#(_d, 32, dw), Add#(_e, 12, dw),
              Add#(_f, ports, 8), Log#(TAdd#(macEntries, 1), _g), Add#(_h, 20, dw));

  EswitchRegsIfc#(aw, dw, ports, macEntries) r <- mkEswitchRegs(
      EswitchRegsCfg { vlan: cfg.vlan });
  // 学习表就是一张 CAM，跟将来的 TLB、cache 标签阵列同一个形状，
  // 所以它住在 hwcore 而不是这里
  Cam#(macEntries, Bit#(48), Bit#(8)) tab <- mkCam;

  Vector#(ports, RmiiTxIfc) txp <- replicateM(mkRmiiTxRaw);
  Vector#(ports, RmiiRxIfc) rxp <- replicateM(mkRmiiRx);
  Vector#(ports, FIFOF#(Cell)) outQ <- replicateM(mkSizedFIFOF(16));
  // 入口缓冲：要装下定向之前的 12 字节，再加上等出口发完上一帧的尾巴、帧间隔
  // 与前导码的那几十个字节
  Vector#(ports, FIFOF#(Cell)) hq <- replicateM(mkSizedFIFOF(64));
  // 每帧一个请求、一个裁决。不带保护：仲裁在一条规则里挑一个口，带保护的话
  // 隐式条件会提到整条规则上，要每个口都有请求才动得了
  Vector#(ports, FIFOF#(Bit#(8))) reqQ <- replicateM(mkUGSizedFIFOF(2));
  Vector#(ports, FIFOF#(Bit#(8))) decQ <- replicateM(mkUGSizedFIFOF(2));

  // 每个入口一份解析状态。收不收在帧头定下，整帧照办：帧中途关口，这一帧照样发完；
  // 帧中途开口，这一帧整个丢掉，不从半截开始当新帧
  Vector#(ports, Reg#(Bit#(4)))  hdr  <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(48))) dst  <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(48))) src  <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bool))     mid  <- replicateM(mkReg(False));
  Vector#(ports, Reg#(Bool))     live <- replicateM(mkReg(False));

  Vector#(ports, RWire#(Staged))                    stage <- replicateM(mkRWire);
  Vector#(ports, RWire#(Tuple2#(Bit#(48), Bit#(8)))) want <- replicateM(mkRWire);
  // 计数器留在本包里，寄存器组那边只是每拍读一眼
  Vector#(ports, Reg#(Bit#(32))) rxn   <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(32))) txn   <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(32))) dropn <- replicateM(mkReg(0));

  // 出口的归属：授出一次翻一下 gnt，帧尾交给发送器时翻一下 rel，两者不等就是占着。
  // 两个寄存器各只有一个写者
  Vector#(ports, Reg#(Bool))    gnt   <- replicateM(mkReg(False));
  Vector#(ports, Reg#(Bool))    rel   <- replicateM(mkReg(False));
  Vector#(ports, Reg#(Bit#(3))) owner <- replicateM(mkReg(0));
  Reg#(Bit#(3)) rr <- mkReg(0);
  // 出口晚一个字节发：帧尾标记是载波掉了之后才到的，最后一个真字节要等它
  Vector#(ports, Reg#(Maybe#(Bit#(8)))) held <- replicateM(mkReg(tagged Invalid));

  for (Integer p = 0; p < valueOf(ports); p = p + 1) begin
    // 关着的口也照收照丢，收发器才不会堵住
    rule ingress;
      let c <- rxp[p].rx.get;
      Bool lv = mid[p] ? live[p] : (r.ctrl_en == 1 && r.porten[p] == 1);
      if (c.last) mid[p] <= False;
      else begin
        mid[p] <= True;
        live[p] <= lv;
      end
      if (lv) begin
        if (c.last) begin
          // 头都没收齐的残帧也要一个裁决，否则它的字节永远排在缓冲里
          if (hdr[p] < 12) reqQ[p].enq(0);
          hdr[p] <= 0;
          rxn[p] <= rxn[p] + 1;
        end else begin
          if (hdr[p] < 6)
            dst[p] <= {dst[p][39:0], c.dat};
          else if (hdr[p] < 12)
            src[p] <= {src[p][39:0], c.dat};
          if (hdr[p] < 12) hdr[p] <= hdr[p] + 1;

          if (hdr[p] == 11) begin
            // 收齐两个地址：学源、查目的，查不到就泛洪给其它开着的口
            Bit#(48) s = {src[p][39:0], c.dat};
            // 只为**单播**源地址建表项（802.1D 7.8）。组地址一旦进表，之后对它
            // 的查表就会命中，本该泛洪的广播只发给一个口——而表还被白占一格。
            // 地址按先到的字节排在高位，所以第一个字节的最低位（组位）是第 40 位。
            if (r.ctrl_learn == 1 && s[40] == 0)
              want[p].wset(tuple2(s, fromInteger(p)));
            let hit = tab.lookup(dst[p]);
            Bit#(8) m = case (hit) matches
                          tagged Valid .q: (8'h1 << q);
                          default: (zeroExtend(r.porten));
                        endcase;
            Bit#(8) iso = cfg.vlan ? zeroExtend(r.isol[p]) : 0;
            // 转发只许走开着的口（802.1D 7.7），从不回送入口，隔开的口也不去
            reqQ[p].enq(m & zeroExtend(r.porten) & ~(8'h1 << p) & ~iso);
          end
        end
        hq[p].enq(Cell { dat: c.dat, last: c.last });
      end
    endrule

    // 裁决到了就从缓冲头上往外放，一拍一字节，比收的快，很快追上。
    // 只在每个目标出口都放得下时才放：暂存线上的字节没人接就没了
    rule forward (decQ[p].notEmpty);
      let g = decQ[p].first;
      Bool room = True;
      for (Integer e = 0; e < valueOf(ports); e = e + 1)
        if (g[e] == 1 && !outQ[e].notFull) room = False;
      if (room) begin
        let c = hq[p].first;
        hq[p].deq;
        stage[p].wset(Staged { body: c, target: g });
        if (c.last) decQ[p].deq;
      end
    endrule
  end

  // 一拍裁一个入口，轮转。出口正被别的帧占着就不给，这一帧在那个出口上丢掉
  rule arbitrate;
    Maybe#(Bit#(3)) sel = tagged Invalid;
    for (Integer i = 0; i < valueOf(ports); i = i + 1) begin
      Bit#(4) w4 = zeroExtend(rr) + fromInteger(i);
      if (w4 >= fromInteger(valueOf(ports))) w4 = w4 - fromInteger(valueOf(ports));
      Bit#(3) w = truncate(w4);
      for (Integer q = 0; q < valueOf(ports); q = q + 1)
        if (!isValid(sel) && w == fromInteger(q) && reqQ[q].notEmpty && decQ[q].notFull)
          sel = tagged Valid w;
    end
    if (sel matches tagged Valid .s) begin
      Bit#(8) ask = 0;
      for (Integer q = 0; q < valueOf(ports); q = q + 1)
        if (s == fromInteger(q)) ask = reqQ[q].first;
      Bit#(8) busy = 0;
      for (Integer e = 0; e < valueOf(ports); e = e + 1)
        if (gnt[e] != rel[e]) busy[e] = 1;
      Bit#(8) g = ask & ~busy;
      for (Integer e = 0; e < valueOf(ports); e = e + 1)
        if (g[e] == 1) begin
          owner[e] <= s;
          gnt[e] <= !gnt[e];
        end
      for (Integer q = 0; q < valueOf(ports); q = q + 1)
        if (s == fromInteger(q)) begin
          reqQ[q].deq;
          decQ[q].enq(g);
          if (g != ask) dropn[q] <= dropn[q] + 1;
        end
      Bit#(4) s4 = zeroExtend(s);
      rr <= (s4 + 1 >= fromInteger(valueOf(ports))) ? 0 : s + 1;
    end
  endrule

  for (Integer e = 0; e < valueOf(ports); e = e + 1) begin
    // 只看归属它的那个入口：别的入口的帧在这个出口上已经被裁掉了
    rule egress_pick;
      Maybe#(Staged) sv = tagged Invalid;
      for (Integer q = 0; q < valueOf(ports); q = q + 1)
        if (owner[e] == fromInteger(q)) sv = stage[q].wget;
      if (sv matches tagged Valid .x &&& x.target[e] == 1) outQ[e].enq(x.body);
    endrule

    rule egress_send;
      let c = outQ[e].first;
      outQ[e].deq;
      if (c.last) begin
        if (held[e] matches tagged Valid .h) txp[e].tx.put(tuple2(h, True));
        held[e] <= tagged Invalid;
        txn[e] <= txn[e] + 1;
        rel[e] <= !rel[e];
      end else begin
        if (held[e] matches tagged Valid .h) txp[e].tx.put(tuple2(h, False));
        held[e] <= tagged Valid c.dat;
      end
    endrule
  end

  // 802.1Q 8.8.3：动态表项从建立或最后一次更新起过了老化时间就删掉；UNH-IOL 按 ±1 秒验。
  // 两位扫描（每半个周期年龄加一）的误差是半个到一个老化周期，达不到，所以每槽记下
  // 最后一次学到它的秒数，与全局秒计数相减。20 位装得下 1000000 秒，差在 20 位上取模也对
  Reg#(Bit#(32)) sub  <- mkReg(0);
  Reg#(Bit#(20)) now  <- mkReg(0);
  Vector#(macEntries, Reg#(Bit#(20))) seen <- replicateM(mkReg(0));

  // 一秒有多少拍取决于装配的时钟，所以做成寄存器
  rule second;
    if (sub >= r.tick) begin
      sub <= 0;
      now <= now + 1;
    end else
      sub <= sub + 1;
  endrule

  // 学习与老化合成一条规则：表的写方法一拍只调一次。各口的请求收拢，一拍学一个；
  // 没有要学的就清一个过期的——老化的粒度是秒，晚一拍不差
  rule table_;
    Bool got = False;
    Bit#(48) m = 0;
    Bit#(8)  q = 0;
    if (r.ctrl_learn == 1)
      for (Integer i = 0; i < valueOf(ports); i = i + 1)
        if (!got &&& want[i].wget matches tagged Valid {.mm, .qq}) begin
          m = mm;
          q = qq;
          got = True;
        end
    let d = tab.dump;
    Maybe#(UInt#(TLog#(macEntries))) stale = tagged Invalid;
    for (Integer i = 0; i < valueOf(macEntries); i = i + 1)
      if (!isValid(stale) && d[i].valid && now - seen[i] >= r.agetime)
        stale = tagged Valid (fromInteger(i));
    if (got) begin
      // 建立与更新都算：重新学到同一个地址时 place 给的是它原来那一槽
      seen[tab.place(m)] <= now;
      tab.learn(m, q);
    end else if (stale matches tagged Valid .i)
      tab.clearAt(i);
  endrule

  rule flush (r.ctrl_flush == 1);
    tab.flush;
  endrule

  // volatile 字段：没有存储，硬件每拍驱动
  rule publish;
    r.linkup_in(r.porten);   // 本版没有 PHY 状态线，链路就等于口开着
    r.rxcnt_in(readVReg(rxn));
    r.txcnt_in(readVReg(txn));
    r.drops_in(readVReg(dropn));
    Vector#(macEntries, Bit#(32)) lo = newVector;
    Vector#(macEntries, Bit#(32)) hi = newVector;
    let d = tab.dump;
    for (Integer i = 0; i < valueOf(macEntries); i = i + 1) begin
      lo[i] = d[i].key[31:0];
      hi[i] = {(d[i].valid ? 16'h8000 : 16'h0000) | zeroExtend(d[i].val),
               d[i].key[47:32]};
    end
    r.maclo_in(lo);
    r.machi_in(hi);
  endrule

  interface regs = r.regs;
  interface EswitchPins pins;
    interface tx = map(getTxPins, txp);
    interface rx = map(getRxPins, rxp);
  endinterface
endmodule

endpackage
