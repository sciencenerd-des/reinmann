/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile003Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2501/160)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 16 ((15/16), (2501/160))
  have he : value ((15/16), (2501/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-24308947/8388608), (-50663897/1048576)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-366446865021221/18014398509481984), (461639382088083/9007199254740992)), (176576863/18014398509481984), by norm_num⟩
  | 1 => ⟨((67514349/1073741824), (-340210659/2147483648)), (131/4294967296), by norm_num⟩
  | 2 => ⟨((-208689719/2147483648), (525802795/2147483648)), (51/1073741824), by norm_num⟩
  | 3 => ⟨((215022927/2147483648), (-541759587/2147483648)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((-166161249/2147483648), (837300941/4294967296)), (83/2147483648), by norm_num⟩
  | 5 => ⟨((102722295/2147483648), (-517626551/4294967296)), (207/8589934592), by norm_num⟩
  | 6 => ⟨((-423358633/17179869184), (1066670429/17179869184)), (215/17179869184), by norm_num⟩
  | 7 => ⟨((46736411/4294967296), (-942035309/34359738368)), (3/536870912), by norm_num⟩
  | 8 => ⟨((-288928461/68719476736), (727967783/68719476736)), (299/137438953472), by norm_num⟩
  | 9 => ⟨((396928951/274877906944), (-1000079699/274877906944)), (207/274877906944), by norm_num⟩
  | 10 => ⟨((-490769695/1099511627776), (1236515523/1099511627776)), (129/549755813888), by norm_num⟩
  | 11 => ⟨((551632713/4398046511104), (-1389862537/4398046511104)), (73/1099511627776), by norm_num⟩
  | 12 => ⟨((-284186689/8796093022208), (1432041369/17592186044416)), (303/17592186044416), by norm_num⟩
  | 13 => ⟨((135143557/17592186044416), (-1362000205/70368744177664)), (145/35184372088832), by norm_num⟩
  | 14 => ⟨((-477410825/281474976710656), (1202857273/281474976710656)), (129/140737488355328), by norm_num⟩
  | 15 => ⟨((196759617/562949953421312), (-247872193/281474976710656)), (107/562949953421312), by norm_num⟩
  | 16 => ⟨((-608192329/9007199254740992), (1532366943/9007199254740992)), (333/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (1269150891627/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111093502711683/39614081257132168796771975168), (374983364393/79228162514264337593543950336)), (5781/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888310129219289/39614081257132168796771975168), (3374004168637/39614081257132168796771975168)), (104077/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887995820716429/2475880078570760549798248448), (3583819517021/2475880078570760549798248448)), (27651/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((884831091893663/77371252455336267181195264), (3582627638765/154742504910672534362390528)), (110629/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548120574051463/9671406556917033397649408), (1678723759073/4835703278458516698824704)), (103741/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257535059678127/604462909807314587353088), (2936501222237/604462909807314587353088)), (5675/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885755133217101/75557863725914323419136), (4769443084173/75557863725914323419136)), (147599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324002992055645/1180591620717411303424), (893752119181/1180591620717411303424)), (110743/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619348145731731/590295810358705651712), (4912268808377/590295810358705651712)), (152341/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820850142262227/73786976294838206464), (6135287977523/73786976294838206464)), (47633/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909852506453089/4611686018427387904), (861907999913/1152921504606846976)), (107247/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590954335000695/1152921504606846976), (3443302189015/576460752303423488)), (53669/288230376151711744), by norm_num⟩
  | 5 => ⟨((595964549835893/72057594037927936), (6016049255447/144115188075855872)), (94023/72057594037927936), by norm_num⟩
  | 4 => ⟨((743830880259293/18014398509481984), (9004645945641/36028797018963968)), (282479/36028797018963968), by norm_num⟩
  | 3 => ⟨((371072849088167/2251799813685248), (11221878679161/9007199254740992)), (176909/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218025403733341/4503599627370496), (22342251192263/4503599627370496)), (88725/562949953421312), by norm_num⟩
  | 1 => ⟨((2201244761395329/2251799813685248), (33260589635393/2251799813685248)), (1070129/2251799813685248), by norm_num⟩
  | 0 => ⟨((1075558542634487/1125899906842624), (16378970937353/562949953421312)), (2162083/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1075558542634487/1125899906842624), (16378970937353/562949953421312)), (8247692116744231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1026514958260587/1125899906842624), (62586530131739/1125899906842624)), (4256635/2251799813685248), by norm_num⟩
  | 2 => ⟨((932423814407105/1125899906842624), (228247676282425/2251799813685248)), (8235027/2251799813685248), by norm_num⟩
  | 3 => ⟨((1521254090237913/2251799813685248), (189025301143901/1125899906842624)), (15309263/2251799813685248), by norm_num⟩
  | 4 => ⟨((241061809311317/562949953421312), (127700300344641/562949953421312)), (25825525/2251799813685248), by norm_num⟩
  | 5 => ⟨((594062458963183/4503599627370496), (437462197320965/2251799813685248)), (33834181/2251799813685248), by norm_num⟩
  | 6 => ⟨((-366446865021221/18014398509481984), (461639382088083/9007199254740992)), (176576863/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-50663897/1048576)), (1/16777216), by norm_num⟩, -8, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-98634119/33554432), (-25696243/524288)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((297010216445217/18014398509481984), (452660234553515/9007199254740992)), (138890807/18014398509481984), by norm_num⟩
  | 1 => ⟨((-55508245/1073741824), (-1353562877/8589934592)), (105/4294967296), by norm_num⟩
  | 2 => ⟨((174045781/2147483648), (1061022143/4294967296)), (83/2147483648), by norm_num⟩
  | 3 => ⟨((-181906513/2147483648), (-1108942931/4294967296)), (11/268435456), by norm_num⟩
  | 4 => ⟨((142591705/2147483648), (217317759/1073741824)), (35/1073741824), by norm_num⟩
  | 5 => ⟨((-357676373/8589934592), (-545118861/4294967296)), (177/8589934592), by norm_num⟩
  | 6 => ⟨((373830733/17179869184), (142434753/2147483648)), (187/17179869184), by norm_num⟩
  | 7 => ⟨((-334898315/34359738368), (-255201911/8589934592)), (85/17179869184), by norm_num⟩
  | 8 => ⟨((525035865/137438953472), (1600368231/137438953472)), (269/137438953472), by norm_num⟩
  | 9 => ⟨((-45729081/34359738368), (-557549481/137438953472)), (95/137438953472), by norm_num⟩
  | 10 => ⟨((458826461/1099511627776), (699277269/549755813888)), (15/68719476736), by norm_num⟩
  | 11 => ⟨((-523144623/4398046511104), (-797301757/2199023255552)), (69/1099511627776), by norm_num⟩
  | 12 => ⟨((273386157/8796093022208), (416655841/4398046511104)), (73/4398046511104), by norm_num⟩
  | 13 => ⟨((-131877033/17592186044416), (-803951987/35184372088832)), (71/17592186044416), by norm_num⟩
  | 14 => ⟨((29535691/17592186044416), (1440449603/281474976710656)), (257/281474976710656), by norm_num⟩
  | 15 => ⟨((-395131683/1125899906842624), (-602202853/562949953421312)), (217/1125899906842624), by norm_num⟩
  | 16 => ⟨((309733277/4503599627370496), (944101781/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (1633199511331/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777434720690097/633825300114114700748351602688), (1930047794469/633825300114114700748351602688)), (92391/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888241312327249/39614081257132168796771975168), (2170755656511/39614081257132168796771975168)), (6497/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((943961466401367/1237940039285380274899124224), (2305736578067/2475880078570760549798248448)), (110463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769589554349357/154742504910672534362390528), (2304959272901/154742504910672534362390528)), (110479/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548052758354127/9671406556917033397649408), (540018445053/2417851639229258349412352)), (103591/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314368998771267/151115727451828646838272), (944619705947/302231454903657293676544)), (90659/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885659666720635/75557863725914323419136), (383558466157/9444732965739290427392)), (147353/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295940817085353/4722366482869645213696), (2299998604053/4722366482869645213696)), (110543/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809625520542387/295147905179352825856), (3160302327585/590295810358705651712)), (76021/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820729851906933/73786976294838206464), (3947087008719/73786976294838206464)), (23765/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1819571182714073/9223372036854775808), (2217976163267/4611686018427387904)), (106989/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198852796376687/144115188075855872), (4430308267289/1152921504606846976)), (13381/72057594037927936), by norm_num⟩
  | 5 => ⟨((595907862334771/72057594037927936), (1935089642121/72057594037927936)), (93733/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487495870035733/36028797018963968), (5792610786491/36028797018963968)), (35183/4503599627370496), by norm_num⟩
  | 3 => ⟨((1484091300730379/9007199254740992), (7218662855991/9007199254740992)), (352295/9007199254740992), by norm_num⟩
  | 2 => ⟨((2217646881156811/4503599627370496), (3592806961743/1125899906842624)), (176497/1125899906842624), by norm_num⟩
  | 1 => ⟨((2200730682972541/2251799813685248), (21392309125161/2251799813685248)), (531247/1125899906842624), by norm_num⟩
  | 0 => ⟨((2150300968669727/2251799813685248), (10532685873327/562949953421312)), (2139129/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2150300968669727/2251799813685248), (10532685873327/562949953421312)), (8160129555709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2052588879448555/2251799813685248), (20115859765565/562949953421312)), (520683/281474976710656), by norm_num⟩
  | 2 => ⟨((467031607055429/562949953421312), (146690091381691/2251799813685248)), (3945801/1125899906842624), by norm_num⟩
  | 3 => ⟨((96266838081917/140737488355328), (121696269270009/1125899906842624)), (7061077/1125899906842624), by norm_num⟩
  | 4 => ⟨((1027262686222349/2251799813685248), (166484640104007/1125899906842624)), (22372459/2251799813685248), by norm_num⟩
  | 5 => ⟨((419397887504453/2251799813685248), (75949672599053/562949953421312)), (13514405/1125899906842624), by norm_num⟩
  | 6 => ⟨((297010216445217/18014398509481984), (452660234553515/9007199254740992)), (138890807/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-25696243/524288)), (1/16777216), by norm_num⟩, -8, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-99972929/33554432), (-1666881973/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((380749163799721/9007199254740992), (508244227723117/18014398509481984)), (93196735/18014398509481984), by norm_num⟩
  | 1 => ⟨((-576992673/4294967296), (-385100249/4294967296)), (143/8589934592), by norm_num⟩
  | 2 => ⟨((916856887/4294967296), (611934661/4294967296)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((-485636757/2147483648), (-162063441/1073741824)), (125/4294967296), by norm_num⟩
  | 4 => ⟨((385844939/2147483648), (515046339/4294967296)), (101/4294967296), by norm_num⟩
  | 5 => ⟨((-980988789/8589934592), (-163684499/2147483648)), (65/4294967296), by norm_num⟩
  | 6 => ⟨((519605863/8589934592), (173399383/4294967296)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((-471810115/17179869184), (-629797227/34359738368)), (1/268435456), by norm_num⟩
  | 8 => ⟨((749718971/68719476736), (125095593/17179869184)), (13/8589934592), by norm_num⟩
  | 9 => ⟨((-264738583/68719476736), (-706774273/274877906944)), (149/274877906944), by norm_num⟩
  | 10 => ⟨((336541387/274877906944), (449233337/549755813888)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((-777852105/2199023255552), (-259579587/1099511627776)), (113/2199023255552), by norm_num⟩
  | 12 => ⟨((206004655/2199023255552), (274985967/4398046511104)), (61/4398046511104), by norm_num⟩
  | 13 => ⟨((-805777087/35184372088832), (-268898525/17592186044416)), (61/17592186044416), by norm_num⟩
  | 14 => ⟨((182914497/35184372088832), (488327993/140737488355328)), (7/8796093022208), by norm_num⟩
  | 15 => ⟨((-620066259/562949953421312), (-206924353/281474976710656)), (3/17592186044416), by norm_num⟩
  | 16 => ⟨((985301975/4503599627370496), (657616733/4503599627370496)), (155/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (766624101449/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888687430687995/316912650057057350374175801344), (28309530903/19807040628566084398385987584)), (46145/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888174072140569/39614081257132168796771975168), (1018883508683/39614081257132168796771975168)), (103833/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((943925813179371/1237940039285380274899124224), (1082234957893/2475880078570760549798248448)), (13791/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769518401002761/154742504910672534362390528), (1081865309985/154742504910672534362390528)), (431/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((96749138413977/604462909807314587353088), (506928076791/4835703278458516698824704)), (12931/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314354482925451/151115727451828646838272), (886731758415/604462909807314587353088)), (90525/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885565617866415/75557863725914323419136), (180025478021/9444732965739290427392)), (73559/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1295870546249985/4722366482869645213696), (1079509916685/4722366482869645213696)), (6897/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619154850019761/590295810358705651712), (1483282128891/590295810358705651712)), (151755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455152564756849/18446744073709551616), (1852538031795/73786976294838206464)), (189725/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56857422725203/288230376151711744), (130122260097/576460752303423488)), (106743/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590689821059919/1152921504606846976), (2079273114023/1152921504606846976)), (213541/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595850491855609/72057594037927936), (454087539217/36028797018963968)), (5841/4503599627370496), by norm_num⟩
  | 4 => ⟨((1487326230377831/36028797018963968), (1359254553481/18014398509481984)), (140247/18014398509481984), by norm_num⟩
  | 3 => ⟨((741941778601347/4503599627370496), (3387633998855/9007199254740992)), (350839/9007199254740992), by norm_num⟩
  | 2 => ⟨((2217244234237097/4503599627370496), (3371931971225/2251799813685248)), (702345/4503599627370496), by norm_num⟩
  | 1 => ⟨((1100079270596595/1125899906842624), (10037645457263/2251799813685248)), (263801/562949953421312), by norm_num⟩
  | 0 => ⟨((2149282379084131/2251799813685248), (9882418941055/1125899906842624)), (2117233/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2149282379084131/2251799813685248), (9882418941055/1125899906842624)), (8076602944380950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64101836286593/70368744177664), (37730012701219/2251799813685248)), (1019713/562949953421312), by norm_num⟩
  | 2 => ⟨((29186645818401/35184372088832), (68739697589553/2251799813685248)), (3783941/1125899906842624), by norm_num⟩
  | 3 => ⟨((1547426461957179/2251799813685248), (114043883014021/2251799813685248)), (813605/140737488355328), by norm_num⟩
  | 4 => ⟨((1057608510951445/2251799813685248), (612268993839/8796093022208)), (9604979/1125899906842624), by norm_num⟩
  | 5 => ⟨((485819413357855/2251799813685248), (73616877088603/1125899906842624)), (647471/70368744177664), by norm_num⟩
  | 6 => ⟨((380749163799721/9007199254740992), (508244227723117/18014398509481984)), (93196735/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-1666881973/33554432)), (1/16777216), by norm_num⟩, -8, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-50628539/16777216), (-211036627/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1760139985259473/36028797018963968), (-10915273103521/4503599627370496)), (57829217/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1350801479/8589934592), (8376815/1073741824)), (91/8589934592), by norm_num⟩
  | 2 => ⟨((271753889/1073741824), (-53927855/4294967296)), (75/4294967296), by norm_num⟩
  | 3 => ⟨((-583161349/2147483648), (14465589/1073741824)), (41/2147483648), by norm_num⟩
  | 4 => ⟨((1877123969/8589934592), (-93125869/8589934592)), (67/4294967296), by norm_num⟩
  | 5 => ⟨((-1208445793/8589934592), (29976061/4294967296)), (11/1073741824), by norm_num⟩
  | 6 => ⟨((324153079/4294967296), (-64326145/17179869184)), (97/17179869184), by norm_num⟩
  | 7 => ⟨((-298116717/8589934592), (1848731/1073741824)), (91/34359738368), by norm_num⟩
  | 8 => ⟨((1919201387/137438953472), (-11901671/17179869184)), (149/137438953472), by norm_num⟩
  | 9 => ⟨((-686407883/137438953472), (68106669/274877906944)), (109/274877906944), by norm_num⟩
  | 10 => ⟨((1767569393/1099511627776), (-21922691/274877906944)), (71/549755813888), by norm_num⟩
  | 11 => ⟨((-1034470253/2199023255552), (51321033/2199023255552)), (85/2199023255552), by norm_num⟩
  | 12 => ⟨((1109943763/8796093022208), (-215099/34359738368)), (93/8796093022208), by norm_num⟩
  | 13 => ⟨((-1099314199/35184372088832), (54538001/35184372088832)), (47/17592186044416), by norm_num⟩
  | 14 => ⟨((2022031943/281474976710656), (-100314887/281474976710656)), (175/281474976710656), by norm_num⟩
  | 15 => ⟨((-108477829/70368744177664), (86106977/1125899906842624)), (19/140737488355328), by norm_num⟩
  | 16 => ⟨((1396706645/4503599627370496), (-69291917/4503599627370496)), (31/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (-32285418827/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222164548981543/79228162514264337593543950336), (-38148646611/316912650057057350374175801344)), (5763/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((59003385450491/1237940039285380274899124224), (-42906175507/19807040628566084398385987584)), (103735/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((117986364597105/154742504910672534362390528), (-91147580703/2475880078570760549798248448)), (110219/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769448668350889/154742504910672534362390528), (-91116052535/154742504910672534362390528)), (110219/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193490113016085/1208925819614629174706176), (-21346954001/2417851639229258349412352)), (25833/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257360848832411/604462909807314587353088), (-37340436565/302231454903657293676544)), (90417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235684122217859/9444732965739290427392), (-121293707221/75557863725914323419136)), (9183/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1295801170642805/4722366482869645213696), (-5682215289/295147905179352825856)), (110197/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809529814070123/295147905179352825856), (-31229924319/147573952589676412928)), (151523/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820491485684029/73786976294838206464), (-78008091877/36893488147419103232)), (189407/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454826063965499/2305843009213693952), (-175334925759/9223372036854775808)), (213087/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795278492331551/576460752303423488), (-43776529575/288230376151711744)), (213093/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595792619982259/72057594037927936), (-152960848447/144115188075855872)), (186463/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487153587926771/36028797018963968), (-28616033641/4503599627370496)), (279709/36028797018963968), by norm_num⟩
  | 3 => ⟨((741834725190903/4503599627370496), (-285264840305/9007199254740992)), (87415/2251799813685248), by norm_num⟩
  | 2 => ⟨((1108410541104579/2251799813685248), (-283926104525/2251799813685248)), (87425/562949953421312), by norm_num⟩
  | 1 => ⟨((2199536372715023/2251799813685248), (-422558043667/1125899906842624)), (1049313/2251799813685248), by norm_num⟩
  | 0 => ⟨((2148087716996021/2251799813685248), (-207971392563/281474976710656)), (2099555/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2148087716996021/2251799813685248), (-207971392563/281474976710656)), (8009166726119231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((128071943932683/140737488355328), (-1587142129193/1125899906842624)), (4008813/2251799813685248), by norm_num⟩
  | 2 => ⟨((932367553503277/1125899906842624), (-361077173109/140737488355328)), (3653695/1125899906842624), by norm_num⟩
  | 3 => ⟨((386047154561493/562949953421312), (-9568357214605/2251799813685248)), (3035031/562949953421312), by norm_num⟩
  | 4 => ⟨((529449136812547/1125899906842624), (-13123145509035/2251799813685248)), (33507069/4503599627370496), by norm_num⟩
  | 5 => ⟨((995730908338069/4503599627370496), (-49368779727559/9007199254740992)), (1993977/281474976710656), by norm_num⟩
  | 6 => ⟨((1760139985259473/36028797018963968), (-10915273103521/4503599627370496)), (57829217/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-211036627/4194304)), (1/16777216), by norm_num⟩, -8, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-102490855/33554432), (-854432095/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((334798218401899/9007199254740992), (-65314299044527/2251799813685248)), (90922379/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1040272633/8589934592), (811768691/8589934592)), (143/8589934592), by norm_num⟩
  | 2 => ⟨((423663583/2147483648), (-661205191/4294967296)), (59/2147483648), by norm_num⟩
  | 3 => ⟨((-920224569/4294967296), (718090115/4294967296)), (65/2147483648), by norm_num⟩
  | 4 => ⟨((749545121/4294967296), (-292450865/2147483648)), (27/1073741824), by norm_num⟩
  | 5 => ⟨((-488418073/4294967296), (762266521/8589934592)), (143/8589934592), by norm_num⟩
  | 6 => ⟨((1060875489/17179869184), (-827845971/17179869184)), (157/17179869184), by norm_num⟩
  | 7 => ⟨((-246888197/8589934592), (770629169/34359738368)), (37/8589934592), by norm_num⟩
  | 8 => ⟨((201096395/17179869184), (-627696057/68719476736)), (61/34359738368), by norm_num⟩
  | 9 => ⟨((-1164784833/274877906944), (454465411/137438953472)), (179/274877906944), by norm_num⟩
  | 10 => ⟨((379498143/274877906944), (-592276873/549755813888)), (59/274877906944), by norm_num⟩
  | 11 => ⟨((-224807561/549755813888), (175426839/549755813888)), (71/1099511627776), by norm_num⟩
  | 12 => ⟨((488296491/4398046511104), (-762076769/8796093022208)), (39/2199023255552), by norm_num⟩
  | 13 => ⟨((-122378239/4398046511104), (763975287/35184372088832)), (79/17592186044416), by norm_num⟩
  | 14 => ⟨((911360267/140737488355328), (-711172925/140737488355328)), (149/140737488355328), by norm_num⟩
  | 15 => ⟨((-395906631/281474976710656), (617885345/562949953421312)), (131/562949953421312), by norm_num⟩
  | 16 => ⟨((161237753/562949953421312), (-251641263/1125899906842624)), (27/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (-863161346309/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777259243610347/633825300114114700748351602688), (-1019854691407/633825300114114700748351602688)), (92301/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888044029387535/39614081257132168796771975168), (-1147037368495/39614081257132168796771975168)), (103845/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((943856744878061/1237940039285380274899124224), (-1218347768957/2475880078570760549798248448)), (110343/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769380302437063/154742504910672534362390528), (-608960581927/77371252455336267181195264)), (6897/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1547856787619655/9671406556917033397649408), (-1141348031289/9671406556917033397649408)), (12933/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257304723460223/604462909807314587353088), (-249556675459/151115727451828646838272)), (22635/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942690865084273/37778931862957161709568), (-405317460035/18889465931478580854784)), (18393/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1295732696678725/4722366482869645213696), (-303802598941/1180591620717411303424)), (110373/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809482707190087/295147905179352825856), (-1669709501173/590295810358705651712)), (151787/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910186812829265/36893488147419103232), (-1042665657873/36893488147419103232)), (189769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819171536126275/9223372036854775808), (-1171758864157/4611686018427387904)), (213541/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397606026639785/288230376151711744), (-2340421687385/1152921504606846976)), (53401/288230376151711744), by norm_num⟩
  | 5 => ⟨((1191468794337927/144115188075855872), (-1022195684897/72057594037927936)), (93487/72057594037927936), by norm_num⟩
  | 4 => ⟨((371744641776481/9007199254740992), (-3059645416999/36028797018963968)), (140301/18014398509481984), by norm_num⟩
  | 3 => ⟨((1483450062599875/9007199254740992), (-3812439387897/9007199254740992)), (175501/4503599627370496), by norm_num⟩
  | 2 => ⟨((1108190245467207/2251799813685248), (-1897162060965/1125899906842624)), (702755/4503599627370496), by norm_num⟩
  | 1 => ⟨((1099435507293267/1125899906842624), (-5646410148765/1125899906842624)), (1056025/2251799813685248), by norm_num⟩
  | 0 => ⟨((536684880287665/562949953421312), (-22227566711909/2251799813685248)), (1059855/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((536684880287665/562949953421312), (-22227566711909/2251799813685248)), (4043025974753951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2046361527762489/2251799813685248), (-21190514196453/1125899906842624)), (4083473/2251799813685248), by norm_num⟩
  | 2 => ⟨((1858868326260493/2251799813685248), (-77028966325667/2251799813685248)), (7575563/2251799813685248), by norm_num⟩
  | 3 => ⟨((1531867074398579/2251799813685248), (-127175341997237/2251799813685248)), (1628199/281474976710656), by norm_num⟩
  | 4 => ⟨((517462332097895/1125899906842624), (-86515558753029/1125899906842624)), (19193545/2251799813685248), by norm_num⟩
  | 5 => ⟨((924708570102849/4503599627370496), (-159049814368099/2251799813685248)), (2574047/281474976710656), by norm_num⟩
  | 6 => ⟨((334798218401899/9007199254740992), (-65314299044527/2251799813685248)), (90922379/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-854432095/16777216)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-103678063/33554432), (-864329453/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((513015674672153/36028797018963968), (-389326833995347/9007199254740992)), (239462663/36028797018963968), by norm_num⟩
  | 1 => ⟨((-201560971/4294967296), (1223714573/8589934592)), (95/4294967296), by norm_num⟩
  | 2 => ⟨((332156039/4294967296), (-1008290901/4294967296)), (159/4294967296), by norm_num⟩
  | 3 => ⟨((-182455353/2147483648), (553860387/2147483648)), (177/4294967296), by norm_num⟩
  | 4 => ⟨((300671539/4294967296), (-912716741/4294967296)), (147/4294967296), by norm_num⟩
  | 5 => ⟨((-396385737/8589934592), (1203266193/8589934592)), (49/2147483648), by norm_num⟩
  | 6 => ⟨((217737121/8589934592), (-660961513/8589934592)), (217/17179869184), by norm_num⟩
  | 7 => ⟨((-410072017/34359738368), (155601523/4294967296)), (103/17179869184), by norm_num⟩
  | 8 => ⟨((168941309/34359738368), (-128209309/8589934592)), (171/68719476736), by norm_num⟩
  | 9 => ⟨((-494935995/274877906944), (375606193/68719476736)), (63/68719476736), by norm_num⟩
  | 10 => ⟨((81561415/137438953472), (-495174695/274877906944)), (21/68719476736), by norm_num⟩
  | 11 => ⟨((-391000899/2199023255552), (1186920011/2199023255552)), (203/2199023255552), by norm_num⟩
  | 12 => ⟨((429558393/8796093022208), (-651982455/4398046511104)), (225/8796093022208), by norm_num⟩
  | 13 => ⟨((-435616735/35184372088832), (165294447/4398046511104)), (115/17592186044416), by norm_num⟩
  | 14 => ⟨((205103099/70368744177664), (-622609751/70368744177664)), (219/140737488355328), by norm_num⟩
  | 15 => ⟨((-45065757/70368744177664), (547205379/281474976710656)), (97/281474976710656), by norm_num⟩
  | 16 => ⟨((297058767/2251799813685248), (-901749831/2251799813685248)), (81/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (-1631609093585/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777203352906137/633825300114114700748351602688), (-1927689270199/633825300114114700748351602688)), (92391/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((943990545812695/19807040628566084398385987584), (-2168077146459/39614081257132168796771975168)), (6497/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1887646533644789/2475880078570760549798248448), (-575714071733/618970019642690137449562112)), (110463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769313251154019/154742504910672534362390528), (-287755045705/19342813113834066795298816)), (110479/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((773896913014799/4835703278458516698824704), (-2157296313343/9671406556917033397649408)), (103591/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257249531178151/604462909807314587353088), (-943384090123/302231454903657293676544)), (90659/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942645926898889/37778931862957161709568), (-3064375291739/75557863725914323419136)), (147353/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295665124359817/4722366482869645213696), (-1148431133581/2361183241434822606848)), (110543/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1618872234732591/590295810358705651712), (-1577940573325/295147905179352825856)), (152041/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113766046898639/4611686018427387904), (-3941397755753/73786976294838206464)), (23765/9223372036854775808), by norm_num⟩
  | 7 => ⟨((454759875453039/2305843009213693952), (-4429328585253/9223372036854775808)), (106989/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397572846815633/288230376151711744), (-2211703044871/576460752303423488)), (13381/72057594037927936), by norm_num⟩
  | 5 => ⟨((148918987144605/18014398509481984), (-3863827637541/144115188075855872)), (93733/72057594037927936), by norm_num⟩
  | 4 => ⟨((371700423186127/9007199254740992), (-5782461326285/36028797018963968)), (35183/4503599627370496), by norm_num⟩
  | 3 => ⟨((370806577580645/2251799813685248), (-7204893139469/9007199254740992)), (352295/9007199254740992), by norm_num⟩
  | 2 => ⟨((2215925070975981/4503599627370496), (-7170231011419/2251799813685248)), (705989/4503599627370496), by norm_num⟩
  | 1 => ⟨((1099084157003087/1125899906842624), (-1333635751681/140737488355328)), (265625/562949953421312), by norm_num⟩
  | 0 => ⟨((2145257135557657/2251799813685248), (-41990978563533/2251799813685248)), (66849/70368744177664), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2145257135557657/2251799813685248), (-41990978563533/2251799813685248)), (255008697778201081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2042972429174981/2251799813685248), (-20002099175291/562949953421312)), (4155691/2251799813685248), by norm_num⟩
  | 2 => ⟨((1850668508585699/2251799813685248), (-72588578953413/1125899906842624)), (7835913/2251799813685248), by norm_num⟩
  | 3 => ⟨((755817080365187/1125899906842624), (-3728611784661/35184372088832)), (6945233/1125899906842624), by norm_num⟩
  | 4 => ⟨((989472063449997/2251799813685248), (-160193194056871/1125899906842624)), (5398349/562949953421312), by norm_num⟩
  | 5 => ⟨((12162597688151/70368744177664), (-281564443359091/2251799813685248)), (50242997/4503599627370496), by norm_num⟩
  | 6 => ⟨((513015674672153/36028797018963968), (-389326833995347/9007199254740992)), (239462663/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-864329453/16777216)), (1/16777216), by norm_num⟩, -8, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile003Terms3
