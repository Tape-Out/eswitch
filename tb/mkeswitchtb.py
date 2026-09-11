"""eswitch 的行为测试台：学习表记得对不对，以及帧到底转发到了哪几个口。

激励源直接用 `mkRmiiTx`——它已经被 emac 的环回测过一遍，拿它造前导码、SFD
与 CRC 比测试台自己再写一份可靠。选中的那个口收到它的两根线，其余口接地。

学习表就是 hwcore 的那张 CAM。这一台验的正是它：两个不同的源地址要落进
两个不同的槽，端口号各自记对，互不覆盖。表的转储寄存器 maclo/machi 步长 8、
元素宽 4，顺带把数组译码也验了。

转发这一条是「收尾」的判据：只验学习表是「记住了」，不是「交换」。
数每个口 tx_en 拉高的拍数，两帧之间取一次快照，差值就是这一帧送到了哪些口。
广播该泛洪到除入口外的每个口、且不从入口反射；目的地址已学到的单播只该走那一个口。

认矩阵：`ports`、`macEntries`、`vlan` 从这一点的旋钮来。
"""
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
out.mkdir(parents=True, exist_ok=True)
cfg = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
label = cfg.get("label", "")
k = cfg.get("knobs", {})
ports = int(k.get("ports", 4))
entries = int(k.get("macEntries", 16))
vlan = bool(k.get("vlan", False))

# 第一帧从 0 号口进来，目的是广播、源是 A
A = [0x00, 0x11, 0x22, 0x33, 0x44, 0x55]
# 第二帧从 1 号口进来，目的是 A、源是 B
B = [0x00, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE]
TAIL = [0x08, 0x00, 0xA5, 0x5A, 0x5A, 0xA5]
F0 = [0xFF] * 6 + A + TAIL
F1 = A + B + TAIL
# 第三帧：目的是 B，**源是广播**。桥不该为组地址建表项（802.1D 7.8）。
F2 = B + [0xFF] * 6 + TAIL
NB = len(F0)

second = ports >= 2 and entries >= 2


def word(mac):
    return (mac[2] << 24) | (mac[3] << 16) | (mac[4] << 8) | mac[5]


def hiword(mac, port):
    return ((0x8000 | port) << 16) | (mac[0] << 8) | mac[1]


rows = []
for i in range(NB):
    rows.append(f"      {i}: return (which == 0) ? 8'h{F0[i]:02X} "
                f": ((which == 1) ? 8'h{F1[i]:02X} : 8'h{F2[i]:02X});")

FWD = '    // 第一帧是广播：除入口（0 号）外每个口都该发，入口自己不该发。\n    if (mark[0] != 0) begin\n      $display("FAIL the broadcast came back out of the port it arrived on");\n      wrong = True;\n    end\n    if (mark[1] == 0) begin\n      $display("FAIL the broadcast never reached port 1");\n      wrong = True;\n    end\n    // 第二帧的目的地址已经学在 0 号口上：只该走 0 号。\n    if (txN[0] == mark[0]) begin\n      $display("FAIL the unicast never reached the port its address was learned on");\n      wrong = True;\n    end\n{p2}'
P2 = '    if (txN[2] != mark[2]) begin\n      $display("FAIL the unicast was flooded to port 2 as well");\n      wrong = True;\n    end'

if second:
    entry1 = f'''    if (lo1 != 32'h{word(B):08X} || hi1 != 32'h{hiword(B, 1):08X}) begin
      $display("FAIL entry 1 is %08h %08h, want %08h %08h",
               lo1, hi1, 32'h{word(B):08X}, 32'h{hiword(B, 1):08X});
      wrong = True;
    end'''
    verdict = ("two sources from two ports land in two slots, a broadcast floods every port but the one it came in on, and a unicast to a learned address goes only there")
    fwd = FWD.format(p2=(P2 if ports >= 3 else "    // 只有两个口，没有第三个口可以看有没有被泛洪到"))
else:
    entry1 = "    // 只有一个口或一个槽，第二条学不进来"
    verdict = "a source is learned against the port it came in on"
    fwd = "    // 只有一个口或一个槽，谈不上转发"

txt = f'''package Eswitch{label}Tb;

import Vector::*;
import RegIf::*;
import GetPut::*;
import RmiiTx::*;
import RmiiRx::*;
import Eswitch::*;

// 由 tb/mkeswitchtb.py 生成，勿手改。
// 这一点：ports={ports} macEntries={entries} vlan={vlan}

Integer nb = {NB};

typedef enum {{ Setup, Send0, Gap0, Send1, Gap1, Send2, Gap2, Read, Done }}
  Phase deriving (Bits, Eq);

function Bit#(8) frameByte(Bit#(8) i, Bit#(2) which);
  case (i)
{chr(10).join(rows)}
    default: return 0;
  endcase
endfunction

(* synthesize *)
module mkEswitch{label}Tb(Empty);
  EswitchIfc#(12, 32, {ports}, {entries}) d <- mkEswitch(
      EswitchCfg {{ vlan: {"True" if vlan else "False"} }});
  // 激励源借 emac 的发送器：前导码、SFD、CRC 都是它现成的
  RmiiTxIfc gen <- mkRmiiTx;

  Reg#(Phase)    ph  <- mkReg(Setup);
  Reg#(Bit#(8))  s   <- mkReg(0);
  Reg#(Bit#(8))  fi  <- mkReg(0);
  Reg#(Bit#(4))  srcPort <- mkReg(0);
  Reg#(Bit#(2))  which <- mkReg(0);
  Reg#(Bit#(32)) cyc <- mkReg(0);
  Reg#(Bool)     bad <- mkReg(False);
  Reg#(Bit#(32)) lo0 <- mkReg(0);
  Reg#(Bit#(32)) hi0 <- mkReg(0);
  Reg#(Bit#(32)) lo1 <- mkReg(0);
  Reg#(Bit#(32)) hi1 <- mkReg(0);
  Reg#(Bit#(32)) hi2 <- mkReg(0);   // 第三个槽，组地址不该落进来
  // 每个口发了多少拍，以及第一帧走完时的快照
  Vector#({ports}, Reg#(Bit#(16))) txN <- replicateM(mkReg(0));
  Vector#({ports}, Reg#(Bit#(16))) mark <- replicateM(mkReg(0));

  // 选中的口接激励源的两根线，其余口接地
  rule wirePorts;
    for (Integer p = 0; p < valueOf({ports}); p = p + 1) begin
      Bool sel = (fromInteger(p) == srcPort);
      d.pins.rx[p].wire_in(sel ? gen.pins.txd : 0,
                           sel ? gen.pins.tx_en : False, False);
    end
  endrule

  rule countTx;
    for (Integer p = 0; p < valueOf({ports}); p = p + 1)
      if (d.pins.tx[p].tx_en) txN[p] <= txN[p] + 1;
  endrule

  rule tick_;
    cyc <= cyc + 1;
    if (cyc > 40000) begin
      $display("TIMEOUT in phase %0d", pack(ph));
      $finish(1);
    end
  endrule

  function Action wr(Bit#(12) a, Bit#(32) v) = action
    let _ <- d.regs.access(RegReq {{ addr: a, write: True,
                                     wdata: v, wstrb: 4'hF }});
  endaction;

  rule setup (ph == Setup);
    case (s)
      0: wr(12'h004, 32'hFFFFFFFF);   // porten 全开
      1: wr(12'h000, 32'h00000003);   // en + learn
      default: ph <= Send0;
    endcase
    if (s < 2) s <= s + 1; else s <= 0;
  endrule

  // 一帧一帧灌进去。最后一个字节带 last，发送器自己补 CRC。
  rule feed (ph == Send0 || ph == Send1 || ph == Send2);
    gen.tx.put(tuple2(frameByte(fi, which), fi == fromInteger(nb - 1)));
    if (fi + 1 == fromInteger(nb)) begin
      fi <= 0;
      ph <= (ph == Send0) ? Gap0 : ((ph == Send1) ? Gap1 : Gap2);
    end else fi <= fi + 1;
  endrule

  // 整帧走完要前导码 8 字节加净荷加 FCS，每字节四拍，宽松等一等
  rule gap0 (ph == Gap0);
    if (s > 200) begin
      for (Integer p = 0; p < valueOf({ports}); p = p + 1)
        mark[p] <= txN[p];
      ph <= {"Send1" if second else "Read"};
      srcPort <= 1;
      which <= 1;
      s <= 0;
    end else s <= s + 1;
  endrule

  rule gap1 (ph == Gap1);
    if (s > 200) begin
      ph <= Send2;
      which <= 2;
      srcPort <= 0;
      s <= 0;
    end else s <= s + 1;
  endrule

  rule gap2 (ph == Gap2);
    if (s > 200) begin ph <= Read; s <= 0; end
    else s <= s + 1;
  endrule

  rule read_ (ph == Read);
    Bit#(12) a = (s == 0) ? 12'h100 : ((s == 1) ? 12'h104
               : ((s == 2) ? 12'h108 : ((s == 3) ? 12'h10C : 12'h114)));
    let x <- d.regs.access(RegReq {{ addr: a, write: False,
                                     wdata: 0, wstrb: 4'hF }});
    if (s == 0) lo0 <= x.rdata;
    if (s == 1) hi0 <= x.rdata;
    if (s == 2) lo1 <= x.rdata;
    if (s == 3) hi1 <= x.rdata;
    if (s == 4) hi2 <= x.rdata;
    if (s == 4) ph <= Done;
    if (s < 4) s <= s + 1; else s <= 0;
  endrule

  rule fin (ph == Done);
    Bool wrong = bad;
    if (lo0 != 32'h{word(A):08X} || hi0 != 32'h{hiword(A, 0):08X}) begin
      $display("FAIL entry 0 is %08h %08h, want %08h %08h",
               lo0, hi0, 32'h{word(A):08X}, 32'h{hiword(A, 0):08X});
      wrong = True;
    end
{entry1}
    // 802.1D 7.8：只为**单播**源地址建表项。源地址是组地址的帧不该进表——
    // 进了表之后，对那个组地址的查表会命中，本该泛洪的广播就只发给一个口。
    if (hi2[31] == 1) begin
      $display("FAIL a frame with a group source address was learned: %08h", hi2);
      wrong = True;
    end
{fwd}
    if (wrong) $display("FAILED");
    else $display("PASS eswitch: {verdict}");
    $finish(wrong ? 1 : 0);
  endrule
endmodule

endpackage
'''

(out / f"Eswitch{label}Tb.bsv").write_text(txt, encoding="utf-8")
print(f"  eswitch 行为测试台就位：ports={ports} macEntries={entries} vlan={vlan}")
