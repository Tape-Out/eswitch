"""eswitch 的行为测试台：学习表记得对不对，以及帧到底转发到了哪几个口。

激励源直接用 `mkRmiiTx`——它已经被 emac 的环回测过一遍，拿它造前导码、SFD
与 CRC 比测试台自己再写一份可靠。选中的那个口收到它的两根线，其余口接地。

学习表就是 hwcore 的那张 CAM。这一台验的正是它：两个不同的源地址要落进
两个不同的槽，端口号各自记对，互不覆盖。表的转储寄存器 maclo/machi 步长 8、
元素宽 4，顺带把数组译码也验了。

转发这一条是「收尾」的判据：只验学习表是「记住了」，不是「交换」。
数每个口 tx_en 拉高的拍数，两帧之间取一次快照，差值就是这一帧送到了哪些口。
广播该泛洪到除入口外的每个口、且不从入口反射；目的地址已学到的单播只该走那一个口。
最后关掉 1 号口再发一帧给学在它上面的地址：转发只许走开着的口（802.1D 7.7），
这一帧哪儿都不该去，既不从关掉的口出去，也不改成泛洪。

老化（802.1Q 8.8.3，只在三个口以上的点上跑）：把「一秒」调成 500 拍、老化时间写 5
（范围外，按下限算成 10 秒）。2 号口学到 C 之后，每秒从 0 号口给 C 发一帧，第一次泛洪到
1 号口的那一帧离 C 被学到要在 8 到 12 秒之间——UNH-IOL 的验收是 ±1 秒，每秒探一次再加上
学习落在帧头里的那几十拍，放宽到 ±2 秒。再验刷新：E 每秒、D 每三秒各发一帧互相往来，
十五秒里 1 号口一帧都不许收到——刷新不算数的话，两个地址十秒就过期，帧会泛洪出去。

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
C = [0x02, 0x00, 0x00, 0x00, 0x00, 0x0C]
D = [0x02, 0x00, 0x00, 0x00, 0x00, 0x0D]
E = [0x02, 0x00, 0x00, 0x00, 0x00, 0x0E]
TAIL = [0x08, 0x00, 0xA5, 0x5A, 0x5A, 0xA5]
FRAMES = [
    [0xFF] * 6 + A + TAIL,      # 0：广播，源 A
    A + B + TAIL,               # 1：给 A，源 B
    B + [0xFF] * 6 + TAIL,      # 2：给 B，**源是广播**（802.1D 7.8：不许学）
    B + A + TAIL,               # 3：1 号口关掉之后，从 0 号口发往 B
    [0xFF] * 6 + C + TAIL,      # 4：2 号口学到 C
    C + A + TAIL,               # 5：从 0 号口探 C
    E + D + TAIL,               # 6：2 号口，D 发给 E
    D + E + TAIL,               # 7：0 号口，E 发给 D
]
NB = len(FRAMES[0])

second = ports >= 2 and entries >= 2
ageing = ports >= 3
SEC = 500               # 测试台里的「一秒」
LO, HI = 8 * SEC, 12 * SEC


def word(mac):
    return (mac[2] << 24) | (mac[3] << 16) | (mac[4] << 8) | mac[5]


def hiword(mac, port):
    return ((0x8000 | port) << 16) | (mac[0] << 8) | mac[1]


def pick(i):
    expr = f"8'h{FRAMES[-1][i]:02X}"
    for w in range(len(FRAMES) - 2, -1, -1):
        expr = f"((which == {w}) ? 8'h{FRAMES[w][i]:02X} : {expr})"
    return expr


rows = [f"      {i}: return {pick(i)};" for i in range(NB)]

# 转发的检查用关口之前的快照 mark2 与第一帧后的快照 mark 相减：
# 老化那一段之后还要往各口发几十帧，拿收尾时的 txN 比会误报
FWD = '    // 第一帧是广播：除入口（0 号）外每个口都该发，入口自己不该发。\n    if (mark[0] != 0) begin\n      $display("FAIL the broadcast came back out of the port it arrived on");\n      wrong = True;\n    end\n    if (mark[1] == 0) begin\n      $display("FAIL the broadcast never reached port 1");\n      wrong = True;\n    end\n    // 第二帧的目的地址已经学在 0 号口上：只该走 0 号。\n    if (mark2[0] == mark[0]) begin\n      $display("FAIL the unicast never reached the port its address was learned on");\n      wrong = True;\n    end\n{p2}'
P2 = '    if (mark2[2] != mark[2]) begin\n      $display("FAIL the unicast was flooded to port 2 as well");\n      wrong = True;\n    end'
OFF = """    // 目的地址学在 1 号口上，而 1 号口已经关掉：这一帧哪儿都不该去。
    if (mark3[1] != mark2[1]) begin
      $display("FAIL a unicast went out of port 1 after the port was disabled");
      wrong = True;
    end
{p2}"""
OFF2 = """    if (mark3[2] != mark2[2]) begin
      $display("FAIL a unicast to a disabled port was flooded to port 2 instead");
      wrong = True;
    end"""

if second:
    entry1 = f'''    if (lo1 != 32'h{word(B):08X} || hi1 != 32'h{hiword(B, 1):08X}) begin
      $display("FAIL entry 1 is %08h %08h, want %08h %08h",
               lo1, hi1, 32'h{word(B):08X}, 32'h{hiword(B, 1):08X});
      wrong = True;
    end'''
    verdict = ("two sources from two ports land in two slots, a broadcast floods every port but the one it came in on, and a unicast to a learned address goes only there")
    fwd = FWD.format(p2=(P2 if ports >= 3 else "    // 只有两个口，没有第三个口可以看有没有被泛洪到"))
    fwd += chr(10) + OFF.format(p2=(OFF2 if ports >= 3 else "    // 只有两个口，没有第三个口可以看有没有被泛洪到"))
else:
    entry1 = "    // 只有一个口或一个槽，第二条学不进来"
    verdict = "a source is learned against the port it came in on"
    fwd = "    // 只有一个口或一个槽，谈不上转发"
if ageing:
    verdict += ", an address ages out about ten seconds after it was learned, and addresses that keep sending do not"

AGE = f'''
  // ---- 老化（802.1Q 8.8.3）----
  rule ageCfg (ph == AgeCfg);
    case (s)
      0: wr(12'h004, 32'hFFFFFFFF);          // 1 号口开回来
      1: wr(12'h014, {SEC - 1});             // 一秒 {SEC} 拍
      2: wr(12'h010, 10);                    // 下限
      3: wr(12'h010, 5);                     // 范围外：agetime 是 WARL，这一笔不算数，仍按 10 秒老化
      default: begin ph <= AgeSendC; which <= 4; srcPort <= 2; end
    endcase
    if (s < 4) s <= s + 1; else s <= 0;
  endrule

  rule ageGapC (ph == AgeGapC);
    if (s > 300) begin ph <= AgeProbe; which <= 5; srcPort <= 0; s <= 0; end
    else s <= s + 1;
  endrule

  rule ageWait (ph == AgeWait);
    if (cyc - pStart >= {SEC}) ph <= AgeChk;
  endrule

  rule ageChk (ph == AgeChk);
    if (txN[1] != markP) begin
      Bit#(32) el = pStart - tStart;
      if (el <= {LO} || el > {HI}) begin
        $display("FAIL an address aged out %0d cycles after it was learned, want about 10 seconds ({10 * SEC} cycles)", el);
        bad <= True;
      end
      ph <= RefSendD;
      which <= 6;
      srcPort <= 2;
    end else if (cyc - tStart > {16 * SEC}) begin
      $display("FAIL a learned address never aged out: 16 seconds and a unicast to it still goes only to its port");
      bad <= True;
      ph <= RefSendD;
      which <= 6;
      srcPort <= 2;
    end else
      ph <= AgeProbe;
  endrule

  // 刷新：先让 D、E 各学一次，再 E 每秒、D 每三秒发一帧，十五秒里 1 号口不许收到任何帧
  rule refGapD (ph == RefGapD);
    if (s > 300) begin ph <= RefSendE; which <= 7; srcPort <= 0; s <= 0; end
    else s <= s + 1;
  endrule

  rule refGapE (ph == RefGapE);
    if (s > 300) begin
      markR <= txN[1];
      k15 <= 0;
      ph <= RefLoopE;
      which <= 7;
      srcPort <= 0;
      s <= 0;
    end else s <= s + 1;
  endrule

  rule refWaitE (ph == RefWaitE);
    if (cyc - iStart >= {SEC // 2}) begin
      if (k15 % 3 == 0) begin ph <= RefLoopD; which <= 6; srcPort <= 2; end
      else ph <= RefWaitD;
    end
  endrule

  rule refWaitD (ph == RefWaitD);
    if (cyc - iStart >= {SEC}) begin
      if (k15 + 1 == 15) ph <= RefChk;
      else begin ph <= RefLoopE; which <= 7; srcPort <= 0; end
      k15 <= k15 + 1;
    end
  endrule

  rule refChk (ph == RefChk);
    if (txN[1] != markR) begin
      $display("FAIL addresses refreshed every one and every three seconds aged out: port 1 saw flooded frames");
      bad <= True;
    end
    ph <= Done;
  endrule
''' if ageing else ""

after_read = "AgeCfg" if ageing else "Done"
feed_phases = "ph == Send0 || ph == Send1 || ph == Send2 || ph == Send3" + (
    " || ph == AgeSendC || ph == AgeProbe || ph == RefSendD || ph == RefSendE || ph == RefLoopE || ph == RefLoopD"
    if ageing else "")

txt = f'''package Eswitch{label}Tb;

import Vector::*;
import ConfigReg::*;
import RegIf::*;
import GetPut::*;
import RmiiTx::*;
import RmiiRx::*;
import Eswitch::*;

// 由 htest/mkeswitchtb.py 生成，勿手改。
// 这一点：ports={ports} macEntries={entries} vlan={vlan}

Integer nb = {NB};

typedef enum {{ Setup, Send0, Gap0, Send1, Gap1, Send2, Gap2, Off, Send3, Gap3, Read,
               AgeCfg, AgeSendC, AgeGapC, AgeProbe, AgeWait, AgeChk,
               RefSendD, RefGapD, RefSendE, RefGapE, RefLoopE, RefWaitE, RefLoopD, RefWaitD, RefChk,
               Done }}
  Phase deriving (Bits, Eq);

function Bit#(8) frameByte(Bit#(8) i, Bit#(3) which);
  case (i)
{chr(10).join(rows)}
    default: return 0;
  endcase
endfunction

// 一帧发完之后去哪一相
function Phase afterFrame(Phase p);
  case (p)
    Send0: return Gap0;
    Send1: return Gap1;
    Send2: return Gap2;
    Send3: return Gap3;
    AgeSendC: return AgeGapC;
    AgeProbe: return AgeWait;
    RefSendD: return RefGapD;
    RefSendE: return RefGapE;
    RefLoopE: return RefWaitE;
    default: return RefWaitD;
  endcase
endfunction

(* synthesize *)
module mkEswitch{label}Tb(Empty);
  EswitchIfc#(12, 32, {ports}, {entries}) d <- mkEswitch(
      EswitchCfg {{ vlan: {"True" if vlan else "False"} }});
  // 激励源借 emac 的发送器：前导码、SFD、CRC 都是它现成的
  RmiiTxIfc gen <- mkRmiiTx;

  Reg#(Phase)    ph  <- mkReg(Setup);
  Reg#(Bit#(16)) s   <- mkReg(0);
  Reg#(Bit#(8))  fi  <- mkReg(0);
  Reg#(Bit#(4))  srcPort <- mkReg(0);
  Reg#(Bit#(3))  which <- mkReg(0);
  // 各阶段规则与计拍规则都读它：普通寄存器会绕成环，把计拍规则整条挡掉
  Reg#(Bit#(32)) cyc <- mkConfigReg(0);
  Reg#(Bool)     bad <- mkReg(False);
  Reg#(Bit#(32)) lo0 <- mkReg(0);
  Reg#(Bit#(32)) hi0 <- mkReg(0);
  Reg#(Bit#(32)) lo1 <- mkReg(0);
  Reg#(Bit#(32)) hi1 <- mkReg(0);
  Reg#(Bit#(32)) hi2 <- mkReg(0);   // 第三个槽，组地址不该落进来
  // 每个口发了多少拍，以及第一帧走完时、关口之前、关口那一帧之后的快照
  Vector#({ports}, Reg#(Bit#(16))) txN <- replicateM(mkReg(0));
  Vector#({ports}, Reg#(Bit#(16))) mark <- replicateM(mkReg(0));
  Vector#({ports}, Reg#(Bit#(16))) mark2 <- replicateM(mkReg(0));
  Vector#({ports}, Reg#(Bit#(16))) mark3 <- replicateM(mkReg(0));
  // 老化：C 那一帧开头的拍、每次探测开头的拍与当时 1 号口的计数、刷新循环
  Reg#(Bit#(32)) tStart <- mkReg(0);
  Reg#(Bit#(32)) pStart <- mkReg(0);
  Reg#(Bit#(16)) markP  <- mkReg(0);
  Reg#(Bit#(16)) markR  <- mkReg(0);
  Reg#(Bit#(32)) iStart <- mkReg(0);
  Reg#(Bit#(8))  k15    <- mkReg(0);

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
    if (cyc > 150000) begin
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
  // 帧开头那一拍记下来：老化量的是从 C 被学到、以及从每次探测开始算起的拍数
  rule feed ({feed_phases});
    gen.tx.put(tuple2(frameByte(fi, which), fi == fromInteger(nb - 1)));
    if (fi == 0) begin
      if (ph == AgeSendC) tStart <= cyc;
      if (ph == AgeProbe) begin pStart <= cyc; markP <= txN[1]; end
      if (ph == RefLoopE) iStart <= cyc;
    end
    if (fi + 1 == fromInteger(nb)) begin
      fi <= 0;
      ph <= afterFrame(ph);
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
    if (s > 200) begin ph <= {"Off" if second else "Read"}; s <= 0; end
    else s <= s + 1;
  endrule

  rule portOff (ph == Off);
    wr(12'h004, 32'hFFFFFFFD);   // 关掉 1 号口
    for (Integer p = 0; p < valueOf({ports}); p = p + 1)
      mark2[p] <= txN[p];
    which <= 3;
    srcPort <= 0;
    ph <= Send3;
  endrule

  // 关口那一帧的结果当场记下：后面的老化段还要往 1 号口发东西
  rule gap3 (ph == Gap3);
    if (s > 200) begin
      for (Integer p = 0; p < valueOf({ports}); p = p + 1)
        mark3[p] <= txN[p];
      ph <= Read;
      s <= 0;
    end else s <= s + 1;
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
    if (s == 4) ph <= {after_read};
    if (s < 4) s <= s + 1; else s <= 0;
  endrule
{AGE}
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
