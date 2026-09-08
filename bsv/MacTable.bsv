package MacTable;

import Vector::*;

// 学习表是**并行比对**，不是按地址读一项，所以它是 CAM 行为：单端口 SRAM 做不了，
// 只能触发器加比较器。D38 的「超过约 900 位就上 SRAM 宏」对它不成立——
// TLB、cache 的标签阵列、这张表，三处都要按这条例外办。
typedef struct {
  Bit#(48) mac;
  Bit#(8)  port;
  Bool     valid;
} MacEntry deriving (Bits, FShow);

interface MacTableIfc#(numeric type entries);
  (* always_ready *) method Maybe#(Bit#(8)) lookup(Bit#(48) mac);
  (* always_ready *) method Action learn(Bit#(48) mac, Bit#(8) port);
  (* always_ready *) method Action flush;
  (* always_ready *) method Vector#(entries, MacEntry) dump;
endinterface

module mkMacTable(MacTableIfc#(entries))
    provisos (Log#(TAdd#(entries, 1), idxw));

  Vector#(entries, Reg#(MacEntry)) tab <- replicateM(
      mkReg(MacEntry { mac: 0, port: 0, valid: False }));
  // 满了就轮换着覆盖。老化计时器要一个全局节拍，等交换机接上系统时钟再说。
  Reg#(Bit#(idxw)) next <- mkReg(0);

  method Maybe#(Bit#(8)) lookup(Bit#(48) mac);
    Maybe#(Bit#(8)) hit = tagged Invalid;
    for (Integer i = 0; i < valueOf(entries); i = i + 1)
      if (tab[i].valid && tab[i].mac == mac) hit = tagged Valid tab[i].port;
    return hit;
  endmethod

  method Action learn(Bit#(48) mac, Bit#(8) port);
    Bit#(idxw) slot = next;
    Bool found = False;
    // 已经在表里就原地更新端口，端设备换口时才认得出来
    for (Integer i = 0; i < valueOf(entries); i = i + 1)
      if (!found && tab[i].valid && tab[i].mac == mac) begin
        slot = fromInteger(i);
        found = True;
      end
    if (!found)
      for (Integer i = 0; i < valueOf(entries); i = i + 1)
        if (!found && !tab[i].valid) begin
          slot = fromInteger(i);
          found = True;
        end
    tab[slot] <= MacEntry { mac: mac, port: port, valid: True };
    if (!found) next <= (next + 1 == fromInteger(valueOf(entries))) ? 0 : next + 1;
  endmethod

  method Action flush;
    for (Integer i = 0; i < valueOf(entries); i = i + 1)
      tab[i] <= MacEntry { mac: 0, port: 0, valid: False };
    next <= 0;
  endmethod

  method Vector#(entries, MacEntry) dump = readVReg(tab);
endmodule

endpackage
