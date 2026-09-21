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
// 直通式转发：读完 12 字节的两个 MAC 地址就决定去哪，不等整帧。代价是坏帧也会
// 被转出去（FCS 要到帧尾才知道），换来的是不必给每个口配一整帧的缓冲——
// 那是 SRAM 宏的量级，第一次流片不划算。
//
// 结构上有一条要守住：**一条规则只调一次某个动作方法**。入口规则若直接调
// `tab.learn` 或往所有出口 `enq`，bsc 会把所有入口规则判成互斥，四个口退化成
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

  Vector#(ports, RmiiTxIfc) txp <- replicateM(mkRmiiTx);
  Vector#(ports, RmiiRxIfc) rxp <- replicateM(mkRmiiRx);
  // 每个口一个浅队列。直通只要装得下头部，不必装下整帧。
  Vector#(ports, FIFOF#(Cell)) outQ <- replicateM(mkSizedFIFOF(16));

  // 每个入口一份解析状态
  Vector#(ports, Reg#(Bit#(4)))  hdr <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(48))) dst <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(48))) src <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(8)))  fan <- replicateM(mkConfigReg(0));

  // 入口与出口之间的暂存：入口只往自己这根线上放，出口各自去取
  Vector#(ports, RWire#(Staged))                    stage <- replicateM(mkRWire);
  Vector#(ports, RWire#(Tuple2#(Bit#(48), Bit#(8)))) want <- replicateM(mkRWire);
  // 计数器留在本包里，寄存器组那边只是每拍读一眼
  Vector#(ports, Reg#(Bit#(32))) rxn <- replicateM(mkReg(0));
  Vector#(ports, Reg#(Bit#(32))) txn <- replicateM(mkReg(0));

  // 802.1Q 8.8.3：动态表项从建立或最后一次更新起过了老化时间就删掉；UNH-IOL 按 ±1 秒验。
  // 两位扫描（每半个周期年龄加一）的误差是半个到一个老化周期，达不到，所以每槽记下
  // 最后一次学到它的秒数，与全局秒计数相减。20 位装得下 1000000 秒，差在 20 位上取模也对
  Reg#(Bit#(32)) sub  <- mkReg(0);
  Reg#(Bit#(20)) now  <- mkReg(0);
  Vector#(macEntries, Reg#(Bit#(20))) seen <- replicateM(mkReg(0));

  for (Integer p = 0; p < valueOf(ports); p = p + 1) begin
    rule ingress (r.ctrl_en == 1 && r.porten[p] == 1);
      let c <- rxp[p].rx.get;
      Bit#(8) target = fan[p];
      if (c.last) begin
        hdr[p] <= 0;
        fan[p] <= 0;
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
          // 命中那一支原来不看 porten：学在后来关掉的口上的地址，帧照样往那个口送，
          // 而泛洪那一支看的正是 porten。转发只许走开着的口（802.1D 7.7）
          target = m & zeroExtend(r.porten) & ~(8'h1 << p);   // 从不回送入口
          fan[p] <= target;
        end
      end
      stage[p].wset(Staged { body: Cell { dat: c.dat, last: c.last },
                             target: target });
    endrule

    // 每个出口一条规则，只调一次 enq。同拍多个入口指向同一出口时，
    // 编号小的先走——简单、可预期，够用。
    rule egress_pick;
      Bool got = False;
      Cell pick = Cell { dat: 0, last: False };
      for (Integer q = 0; q < valueOf(ports); q = q + 1)
        if (!got &&& stage[q].wget matches tagged Valid .s &&& s.target[p] == 1)
          begin
            pick = s.body;
            got = True;
          end
      if (got) outQ[p].enq(pick);
    endrule

    rule egress_send;
      let c = outQ[p].first;
      outQ[p].deq;
      txp[p].tx.put(tuple2(c.dat, c.last));
      if (c.last) txn[p] <= txn[p] + 1;
    endrule
  end

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
