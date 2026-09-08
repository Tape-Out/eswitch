package Eswitch;

import Vector::*;
import FIFOF::*;
import GetPut::*;
import ConfigReg::*;
import RegIf::*;
import RmiiTx::*;
import RmiiRx::*;
import MacTable::*;
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
              Add#(_f, ports, 8), Log#(TAdd#(macEntries, 1), _g));

  EswitchRegsIfc#(aw, dw, ports, macEntries) r <- mkEswitchRegs(
      EswitchRegsCfg { vlan: cfg.vlan });
  MacTableIfc#(macEntries) tab <- mkMacTable;

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
          if (r.ctrl_learn == 1) want[p].wset(tuple2(s, fromInteger(p)));
          let hit = tab.lookup(dst[p]);
          Bit#(8) m = case (hit) matches
                        tagged Valid .q: (8'h1 << q);
                        default: (zeroExtend(r.porten));
                      endcase;
          target = m & ~(8'h1 << p);   // 从不回送入口
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

  // 学习也一样只调一次：把各口的请求收拢，一拍学一个
  rule learner (r.ctrl_learn == 1);
    Bool got = False;
    Bit#(48) m = 0;
    Bit#(8)  q = 0;
    for (Integer i = 0; i < valueOf(ports); i = i + 1)
      if (!got &&& want[i].wget matches tagged Valid {.mm, .qq}) begin
        m = mm;
        q = qq;
        got = True;
      end
    if (got) tab.learn(m, q);
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
      lo[i] = d[i].mac[31:0];
      hi[i] = {(d[i].valid ? 16'h8000 : 16'h0000) | zeroExtend(d[i].port),
               d[i].mac[47:32]};
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
