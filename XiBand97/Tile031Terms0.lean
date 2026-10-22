/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile031Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63483/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63483/2560))
  have he : value ((69/80), (63483/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-1153513881/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-111391499863671/2251799813685248), (616733666624021/1125899906842624)), (49906109/1125899906842624), by norm_num⟩
  | 1 => ⟨((147267731/4294967296), (-1630734261/4294967296)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((-102078213/8589934592), (1130338855/8589934592)), (95/8589934592), by norm_num⟩
  | 3 => ⟨((94340301/34359738368), (-1044654921/34359738368)), (45/17179869184), by norm_num⟩
  | 4 => ⟨((-130783427/274877906944), (724099613/137438953472)), (127/274877906944), by norm_num⟩
  | 5 => ⟨((72521731/1099511627776), (-1606104337/2199023255552)), (143/2199023255552), by norm_num⟩
  | 6 => ⟨((-67024311/8796093022208), (1484355591/17592186044416)), (67/8796093022208), by norm_num⟩
  | 7 => ⟨((414801/549755813888), (-587929653/70368744177664)), (27/35184372088832), by norm_num⟩
  | 8 => ⟨((-73604645/1125899906842624), (1630087125/2251799813685248)), (19/281474976710656), by norm_num⟩
  | 9 => ⟨((45350091/9007199254740992), (-1004346929/18014398509481984)), (3/562949953421312), by norm_num⟩
  | 10 => ⟨((-100589721/288230376151711744), (1113856387/288230376151711744)), (109/288230376151711744), by norm_num⟩
  | 11 => ⟨((101415973/4611686018427387904), (-1123005693/4611686018427387904)), (7/288230376151711744), by norm_num⟩
  | 12 => ⟨((-93728261/73786976294838206464), (129734705/9223372036854775808)), (105/73786976294838206464), by norm_num⟩
  | 13 => ⟨((79959975/1180591620717411303424), (-885417797/1180591620717411303424)), (91/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-31670875/9444732965739290427392), (175349957/4722366482869645213696)), (73/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((23416083/151115727451828646838272), (-1037169735/604462909807314587353088)), (55/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-129846335/19342813113834066795298816), (1437822555/19342813113834066795298816)), (155/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (270431889861/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445261228731895/158456325028528675187087900672), (1283288392067/316912650057057350374175801344)), (23113/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892302048154249/39614081257132168796771975168), (1443618758747/19807040628566084398385987584)), (52013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892236573080775/2475880078570760549798248448), (1533750974939/1237940039285380274899124224)), (55273/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773902191797669/154742504910672534362390528), (766822627583/38685626227668133590597632)), (55283/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776047395321593/4835703278458516698824704), (718840041729/2417851639229258349412352)), (51839/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315252927057605/151115727451828646838272), (1257857711771/302231454903657293676544)), (45371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118212700247117/4722366482869645213696), (4087616132113/75557863725914323419136)), (18437/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300246723409583/4722366482869645213696), (766335817611/1180591620717411303424)), (27665/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812584412447977/295147905179352825856), (4214247507181/590295810358705651712)), (19027/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1828122827066683/73786976294838206464), (5266909899157/73786976294838206464)), (95179/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913941216040689/4611686018427387904), (2962018219275/4611686018427387904)), (53569/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599126314361993/1152921504606846976), (1480622333029/288230376151711744)), (107215/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199073460765779/144115188075855872), (1295109208651/36028797018963968)), (23475/36028797018963968), by norm_num⟩
  | 4 => ⟨((374591514464521/9007199254740992), (3883585251169/18014398509481984)), (141023/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497650334726627/9007199254740992), (4851430063797/4503599627370496)), (88291/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122339478977299/2251799813685248), (9693696271053/2251799813685248)), (88519/1125899906842624), by norm_num⟩
  | 1 => ⟨((280133026163807/281474976710656), (3629400528525/281474976710656)), (266697/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115056000735531/1125899906842624), (28943239911641/1125899906842624)), (268981/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115056000735531/1125899906842624), (28943239911641/1125899906842624)), (1026081087352561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((551786249420753/562949953421312), (14332239104055/281474976710656)), (1093221/1125899906842624), by norm_num⟩
  | 2 => ⟨((1078768764056115/1125899906842624), (7024010227699/70368744177664)), (1127207/562949953421312), by norm_num⟩
  | 3 => ⟨((1022392700336443/1125899906842624), (215359330924581/1125899906842624)), (149067/35184372088832), by norm_num⟩
  | 4 => ⟨((887207811470745/1125899906842624), (391121460350931/1125899906842624)), (5244033/562949953421312), by norm_num⟩
  | 5 => ⟨((281624370041051/562949953421312), (616406507804597/1125899906842624)), (2976997/140737488355328), by norm_num⟩
  | 6 => ⟨((-111391499863671/2251799813685248), (616733666624021/1125899906842624)), (49906109/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1153513881/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-1828276245/67108864)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-224382674553751/1125899906842624), (-748821228964515/2251799813685248)), (57668047/1125899906842624), by norm_num⟩
  | 1 => ⟨((470179679/2147483648), (784553723/2147483648)), (123/2147483648), by norm_num⟩
  | 2 => ⟨((-516545173/4294967296), (-861920361/4294967296)), (69/2147483648), by norm_num⟩
  | 3 => ⟨((756643833/17179869184), (315638767/4294967296)), (205/17179869184), by norm_num⟩
  | 4 => ⟨((-415629107/34359738368), (-693529257/34359738368)), (115/34359738368), by norm_num⟩
  | 5 => ⟨((730584391/274877906944), (1219071623/274877906944)), (205/274877906944), by norm_num⟩
  | 6 => ⟨((-535085993/1099511627776), (-223214511/274877906944)), (19/137438953472), by norm_num⟩
  | 7 => ⟨((671830911/8796093022208), (1121034079/8796093022208)), (97/4398046511104), by norm_num⟩
  | 8 => ⟨((-738081695/70368744177664), (-153947727/8796093022208)), (27/8796093022208), by norm_num⟩
  | 9 => ⟨((22524045/17592186044416), (1202694149/562949953421312)), (107/281474976710656), by norm_num⟩
  | 10 => ⟨((-633476931/4503599627370496), (-528517829/2251799813685248)), (191/4503599627370496), by norm_num⟩
  | 11 => ⟨((126535553/9007199254740992), (844561719/36028797018963968)), (155/36028797018963968), by norm_num⟩
  | 12 => ⟨((-741405405/576460752303423488), (-309281961/144115188075855872)), (115/288230376151711744), by norm_num⟩
  | 13 => ⟨((250620643/2305843009213693952), (836383909/4611686018427387904)), (79/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-157334239/18446744073709551616), (-1050127589/73786976294838206464)), (201/73786976294838206464), by norm_num⟩
  | 15 => ⟨((184372617/295147905179352825856), (1230595279/1180591620717411303424)), (119/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-202554023/4722366482869645213696), (-168993387/2361183241434822606848)), (133/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-343677443941/1267650600228229401496703205376)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((890251244592195/316912650057057350374175801344), (-3259847395147/633825300114114700748351602688)), (69391/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891691736068617/39614081257132168796771975168), (-3667005680721/39614081257132168796771975168)), (305/154742504910672534362390528), by norm_num⟩
  | 15 => ⟨((472897002107127/618970019642690137449562112), (-1947907672017/1237940039285380274899124224)), (82977/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773253505650999/154742504910672534362390528), (-3895389809847/154742504910672534362390528)), (82997/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551486518374365/9671406556917033397649408), (-1825737887325/4835703278458516698824704)), (9729/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315119835270125/151115727451828646838272), (-798647270873/151115727451828646838272)), (17031/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890537865814849/75557863725914323419136), (-5190359249157/75557863725914323419136)), (110741/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40612422145925/147573952589676412928), (-1946013663323/2361183241434822606848)), (83091/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406068952974457/147573952589676412928), (-668791432193/73786976294838206464)), (114307/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827006047361503/73786976294838206464), (-6686104819513/73786976294838206464)), (142969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826625349946237/9223372036854775808), (-7519379324971/9223372036854775808)), (160957/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798934176286951/576460752303423488), (-7516267783881/1152921504606846976)), (10069/72057594037927936), by norm_num⟩
  | 5 => ⟨((1197971756729959/144115188075855872), (-6573232737277/144115188075855872)), (35283/36028797018963968), by norm_num⟩
  | 4 => ⟨((1496711532205957/36028797018963968), (-9852843243077/36028797018963968)), (53007/9007199254740992), by norm_num⟩
  | 3 => ⟨((373894685720919/2251799813685248), (-3075946927215/2251799813685248)), (265615/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120262758994447/2251799813685248), (-1535672010503/281474976710656)), (266485/2251799813685248), by norm_num⟩
  | 1 => ⟨((558702144185303/562949953421312), (-18381992970001/1125899906842624)), (200953/562949953421312), by norm_num⟩
  | 0 => ⟨((69296870420241/70368744177664), (-9144862751055/281474976710656)), (1587/2199023255552), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((69296870420241/70368744177664), (-9144862751055/281474976710656)), (6053924568935483/8388608000000000000000000), by norm_num⟩
  | 1 => ⟨((272668186645927/281474976710656), (-72044527891051/1125899906842624)), (1653133/1125899906842624), by norm_num⟩
  | 2 => ⟨((1051937760136039/1125899906842624), (-34895199224065/281474976710656)), (3414383/1125899906842624), by norm_num⟩
  | 3 => ⟨((482765051196413/562949953421312), (-130411513450439/562949953421312)), (7226755/1125899906842624), by norm_num⟩
  | 4 => ⟨((383790655817935/562949953421312), (-27959022194103/70368744177664)), (15743059/1125899906842624), by norm_num⟩
  | 5 => ⟨((691116671319055/2251799813685248), (-304976636695727/562949953421312)), (16987875/562949953421312), by norm_num⟩
  | 6 => ⟨((-224382674553751/1125899906842624), (-748821228964515/2251799813685248)), (57668047/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1828276245/67108864)), (3/67108864), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-1153513881/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1340291074523621/4503599627370496), (-61016869904837/1125899906842624)), (114079967/2251799813685248), by norm_num⟩
  | 1 => ⟨((221495385/536870912), (322675105/4294967296)), (19/268435456), by norm_num⟩
  | 2 => ⟨((-1228231213/4294967296), (-223661339/4294967296)), (213/4294967296), by norm_num⟩
  | 3 => ⟨((567563335/4294967296), (206706969/8589934592)), (199/8589934592), by norm_num⟩
  | 4 => ⟨((-786809851/17179869184), (-143278353/17179869184)), (139/17179869184), by norm_num⟩
  | 5 => ⟨((54537503/4294967296), (317801557/137438953472)), (311/137438953472), by norm_num⟩
  | 6 => ⟨((-201613421/68719476736), (-73427751/137438953472)), (145/274877906944), by norm_num⟩
  | 7 => ⟨((1277693937/2199023255552), (232668519/2199023255552)), (29/274877906944), by norm_num⟩
  | 8 => ⟨((-442814975/4398046511104), (-20159191/1099511627776)), (81/4398046511104), by norm_num⟩
  | 9 => ⟨((1091327827/70368744177664), (12420699/4398046511104)), (101/35184372088832), by norm_num⟩
  | 10 => ⟨((-605160645/281474976710656), (-3443749/8796093022208)), (113/281474976710656), by norm_num⟩
  | 11 => ⟨((1220262967/4503599627370496), (222210319/4503599627370496)), (229/4503599627370496), by norm_num⟩
  | 12 => ⟨((-1127762447/36028797018963968), (-205365941/36028797018963968)), (107/18014398509481984), by norm_num⟩
  | 13 => ⟨((962098905/288230376151711744), (175198551/288230376151711744)), (23/36028797018963968), by norm_num⟩
  | 14 => ⟨((-190536041/576460752303423488), (-69393361/1152921504606846976)), (293/4611686018427387904), by norm_num⟩
  | 15 => ⟨((563496617/18446744073709551616), (205225867/36893488147419103232)), (109/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-1562344365/590295810358705651712), (-142251731/295147905179352825856)), (305/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-1928820073055/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780113862621795/633825300114114700748351602688), (-4571938886617/633825300114114700748351602688)), (92649/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891254252664471/39614081257132168796771975168), (-321428231983/2475880078570760549798248448)), (104259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891122827901671/2475880078570760549798248448), (-5463609388125/2475880078570760549798248448)), (110809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886393963289357/77371252455336267181195264), (-2731427382953/77371252455336267181195264)), (110847/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551049614746725/9671406556917033397649408), (-5120624407043/9671406556917033397649408)), (103959/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260096627391723/604462909807314587353088), (-4479744251603/604462909807314587353088)), (22751/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((118119697713307/4722366482869645213696), (-7278080105039/75557863725914323419136)), (36989/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162391223598425/590295810358705651712), (-1364310863917/1180591620717411303424)), (111033/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405907892932811/147573952589676412928), (-7501569570143/590295810358705651712)), (152777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826199060783957/73786976294838206464), (-9373750522191/73786976294838206464)), (95565/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912857586963569/4611686018427387904), (-10541051712083/9223372036854775808)), (215241/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798477642681835/576460752303423488), (-658470427821/72057594037927936)), (215517/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197169575773955/144115188075855872), (-143943228545/2251799813685248)), (188887/144115188075855872), by norm_num⟩
  | 4 => ⟨((747750890043569/18014398509481984), (-13806101530213/36028797018963968)), (283951/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494055242162641/9007199254740992), (-17235820495809/9007199254740992)), (356025/9007199254740992), by norm_num⟩
  | 2 => ⟨((559361176839327/1125899906842624), (-537595865655/70368744177664)), (357657/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115051633387175/1125899906842624), (-6430642375403/281474976710656)), (540573/1125899906842624), by norm_num⟩
  | 0 => ⟨((1103877715988533/1125899906842624), (-51116118661313/1125899906842624)), (1097543/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1103877715988533/1125899906842624), (-51116118661313/1125899906842624)), (4186794285300826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1079965587419685/1125899906842624), (-12529076513623/140737488355328)), (2251809/1125899906842624), by norm_num⟩
  | 2 => ⟨((1026982137979853/1125899906842624), (-192286669813215/1125899906842624)), (4720813/1125899906842624), by norm_num⟩
  | 3 => ⟨((451957648347185/562949953421312), (-350786022930907/1125899906842624)), (10224605/1125899906842624), by norm_num⟩
  | 4 => ⟨((308203253902301/562949953421312), (-35203046255131/70368744177664)), (22788573/1125899906842624), by norm_num⟩
  | 5 => ⟨((111391499863693/2251799813685248), (-1233467333248039/2251799813685248)), (95506395/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1340291074523621/4503599627370496), (-61016869904837/1125899906842624)), (114079967/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1153513881/33554432)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-83699259/2097152)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-672051182764041/4503599627370496), (-900736739531311/4503599627370496)), (100540789/4503599627370496), by norm_num⟩
  | 1 => ⟨((257879413/1073741824), (86407653/268435456)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-51880113/268435456), (-1112542021/4294967296)), (65/2147483648), by norm_num⟩
  | 3 => ⟨((445321711/4294967296), (1193711539/8589934592)), (71/4294967296), by norm_num⟩
  | 4 => ⟨((-716717645/17179869184), (-15009411/268435456)), (29/4294967296), by norm_num⟩
  | 5 => ⟨((115351255/8589934592), (618411907/34359738368)), (19/8589934592), by norm_num⟩
  | 6 => ⟨((-61883561/17179869184), (-663530379/137438953472)), (83/137438953472), by norm_num⟩
  | 7 => ⟨((910607993/1099511627776), (1220469655/1099511627776)), (155/1099511627776), by norm_num⟩
  | 8 => ⟨((-366391757/2199023255552), (-982135067/4398046511104)), (63/2199023255552), by norm_num⟩
  | 9 => ⟨((524164253/17592186044416), (351263425/8796093022208)), (91/17592186044416), by norm_num⟩
  | 10 => ⟨((-674887857/140737488355328), (-452269339/70368744177664)), (119/140737488355328), by norm_num⟩
  | 11 => ⟨((789956439/1125899906842624), (529381397/562949953421312)), (141/1125899906842624), by norm_num⟩
  | 12 => ⟨((-423795281/4503599627370496), (-568004327/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 13 => ⟨((209868367/18014398509481984), (1125129475/72057594037927936)), (155/72057594037927936), by norm_num⟩
  | 14 => ⟨((-386022979/288230376151711744), (-517378867/288230376151711744)), (145/576460752303423488), by norm_num⟩
  | 15 => ⟨((662698685/4611686018427387904), (888201775/4611686018427387904)), (127/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-266643097/18446744073709551616), (-714752805/36893488147419103232)), (13/4611686018427387904), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-2881122912559/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444955429889765/158456325028528675187087900672), (-3413522125577/633825300114114700748351602688)), (11567/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945462962310189/19807040628566084398385987584), (-1919863312423/19807040628566084398385987584)), (52063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945387195271695/1237940039285380274899124224), (-4079130140935/2475880078570760549798248448)), (55329/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221554993966007/19342813113834066795298816), (-4078478295751/154742504910672534362390528)), (55343/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550723879598491/9671406556917033397649408), (-3822880840559/9671406556917033397649408)), (51899/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157476512531741/75557863725914323419136), (-1672164100245/302231454903657293676544)), (45427/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889453727323701/75557863725914323419136), (-2716617439791/37778931862957161709568)), (36923/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162348064603979/590295810358705651712), (-2036895038165/2361183241434822606848)), (55409/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623158130470475/590295810358705651712), (-5599615326887/590295810358705651712)), (76227/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825609219625927/73786976294838206464), (-3498375152583/36893488147419103232)), (5959/4611686018427387904), by norm_num⟩
  | 7 => ⟨((912527148205751/4611686018427387904), (-983442153469/1152921504606846976)), (107343/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596297772398621/1152921504606846976), (-3931389555035/576460752303423488)), (53723/576460752303423488), by norm_num⟩
  | 5 => ⟨((598299016677987/72057594037927936), (-6874579481143/144115188075855872)), (94131/144115188075855872), by norm_num⟩
  | 4 => ⟨((747326010035261/18014398509481984), (-10301166358503/36028797018963968)), (141427/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493006240136713/9007199254740992), (-3214432901947/2251799813685248)), (177189/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117693106929737/2251799813685248), (-6414824758533/1125899906842624)), (177799/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113557005145669/1125899906842624), (-4793573843449/281474976710656)), (134111/562949953421312), by norm_num⟩
  | 0 => ⟨((1101084546729573/1125899906842624), (-38068035928395/1125899906842624)), (271279/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101084546729573/1125899906842624), (-38068035928395/1125899906842624)), (1034847261668968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1075529002469743/1125899906842624), (-37228998626217/562949953421312)), (1097889/1125899906842624), by norm_num⟩
  | 2 => ⟨((1022487554002109/1125899906842624), (-142253738585661/1125899906842624)), (1121377/562949953421312), by norm_num⟩
  | 3 => ⟨((910600192536409/1125899906842624), (-129187928989179/562949953421312)), (2320125/562949953421312), by norm_num⟩
  | 4 => ⟨((338588990916341/562949953421312), (-52242012054527/140737488355328)), (4817783/562949953421312), by norm_num⟩
  | 5 => ⟨((252153354529343/1125899906842624), (-502739400899987/1125899906842624)), (4686049/281474976710656), by norm_num⟩
  | 6 => ⟨((-672051182764041/4503599627370496), (-900736739531311/4503599627370496)), (100540789/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-83699259/2097152)), (1/33554432), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-1490895063/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((108095218297949/562949953421312), (-417554949366711/4503599627370496)), (10821985/1125899906842624), by norm_num⟩
  | 1 => ⟨((-738832973/2147483648), (356749551/2147483648)), (39/2147483648), by norm_num⟩
  | 2 => ⟨((41369093/134217728), (-319604693/2147483648)), (9/536870912), by norm_num⟩
  | 3 => ⟨((-197662571/1073741824), (381769823/4294967296)), (45/4294967296), by norm_num⟩
  | 4 => ⟨((1416655133/17179869184), (-42752481/1073741824)), (83/17179869184), by norm_num⟩
  | 5 => ⟨((-253830525/8589934592), (490253841/34359738368)), (61/34359738368), by norm_num⟩
  | 6 => ⟨((606404329/68719476736), (-146402827/34359738368)), (75/137438953472), by norm_num⟩
  | 7 => ⟨((-620874685/274877906944), (599585489/549755813888)), (79/549755813888), by norm_num⟩
  | 8 => ⟨((69528631/137438953472), (-537156489/2199023255552)), (73/2199023255552), by norm_num⟩
  | 9 => ⟨((-442946073/4398046511104), (213878939/4398046511104)), (15/2199023255552), by norm_num⟩
  | 10 => ⟨((1269844513/70368744177664), (-613151383/70368744177664)), (11/8796093022208), by norm_num⟩
  | 11 => ⟨((-827365793/281474976710656), (99874527/70368744177664)), (59/281474976710656), by norm_num⟩
  | 12 => ⟨((988293663/2251799813685248), (-119300753/562949953421312)), (9/281474976710656), by norm_num⟩
  | 13 => ⟨((-1089713557/18014398509481984), (526174163/18014398509481984)), (41/9007199254740992), by norm_num⟩
  | 14 => ⟨((557858453/72057594037927936), (-269365011/72057594037927936)), (43/72057594037927936), by norm_num⟩
  | 15 => ⟨((-533092355/576460752303423488), (257406565/576460752303423488)), (21/288230376151711744), by norm_num⟩
  | 16 => ⟨((955173275/9223372036854775808), (-230605325/4611686018427387904)), (77/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-2288923565/39614081257132168796771975168)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889792513048889/316912650057057350374175801344), (-21689503783/19807040628566084398385987584)), (46135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945330014302419/19807040628566084398385987584), (-1524834935/77371252455336267181195264)), (811/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1890492359210611/2475880078570760549798248448), (-829379417153/2475880078570760549798248448)), (55151/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772158463742425/154742504910672534362390528), (-829232318551/154742504910672534362390528)), (55153/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550460561683481/9671406556917033397649408), (-777249042291/9671406556917033397649408)), (25855/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629791136942869/302231454903657293676544), (-679936696055/604462909807314587353088)), (45249/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944540670214159/37778931862957161709568), (-69037769501/4722366482869645213696)), (36767/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324626542983307/1180591620717411303424), (-207049275781/1180591620717411303424)), (13789/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622776941252087/590295810358705651712), (-1138354964919/590295810358705651712)), (75847/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825135033789559/73786976294838206464), (-1422319909641/73786976294838206464)), (94821/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824523997802239/9223372036854775808), (-1599252635045/9223372036854775808)), (53345/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398942854970279/288230376151711744), (-24971589701/18014398509481984)), (13339/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196141908101117/144115188075855872), (-1397205208453/144115188075855872)), (23349/36028797018963968), by norm_num⟩
  | 4 => ⟨((746988341603155/18014398509481984), (-261675316751/4503599627370496)), (140141/36028797018963968), by norm_num⟩
  | 3 => ⟨((746088761883149/4503599627370496), (-1306274607047/4503599627370496)), (175259/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116887503551543/2251799813685248), (-5212507678293/4503599627370496)), (350765/4503599627370496), by norm_num⟩
  | 1 => ⟨((34762691910149/35184372088832), (-3893679204505/1125899906842624)), (526773/2251799813685248), by norm_num⟩
  | 0 => ⟨((2198023073658049/2251799813685248), (-3862386506041/562949953421312)), (1056059/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2198023073658049/2251799813685248), (-3862386506041/562949953421312)), (4028545388228606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((536356153253517/562949953421312), (-7540292532283/562949953421312)), (2076169/2251799813685248), by norm_num⟩
  | 2 => ⟨((1021835299473529/1125899906842624), (-14368177037559/562949953421312)), (501475/281474976710656), by norm_num⟩
  | 3 => ⟨((926655730996929/1125899906842624), (-6520078026845/140737488355328)), (7486783/2251799813685248), by norm_num⟩
  | 4 => ⟨((5939485799515/8796093022208), (-85860103668595/1125899906842624)), (13017473/2251799813685248), by norm_num⟩
  | 5 => ⟨((126701863303395/281474976710656), (-115952586039499/1125899906842624)), (19565275/2251799813685248), by norm_num⟩
  | 6 => ⟨((108095218297949/562949953421312), (-417554949366711/4503599627370496)), (10821985/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1490895063/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-1619161435/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-716081108661013/9007199254740992), (760693096354819/4503599627370496)), (147985659/4503599627370496), by norm_num⟩
  | 1 => ⟨((332219481/2147483648), (-1411667267/4294967296)), (277/4294967296), by norm_num⟩
  | 2 => ⟨((-161617315/1073741824), (1373488831/4294967296)), (271/4294967296), by norm_num⟩
  | 3 => ⟨((209661849/2147483648), (-890895285/4294967296)), (177/4294967296), by norm_num⟩
  | 4 => ⟨((-25498945/536870912), (866801089/8589934592)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((635118795/34359738368), (-1349373629/34359738368)), (273/34359738368), by norm_num⟩
  | 6 => ⟨((-205980685/34359738368), (27351665/2147483648)), (179/68719476736), by norm_num⟩
  | 7 => ⟨((114519973/68719476736), (-973236709/274877906944)), (25/34359738368), by norm_num⟩
  | 8 => ⟨((-111422789/274877906944), (946915595/1099511627776)), (49/274877906944), by norm_num⟩
  | 9 => ⟨((385455531/4398046511104), (-818938963/4398046511104)), (171/4398046511104), by norm_num⟩
  | 10 => ⟨((-75006183/4398046511104), (39839541/1099511627776)), (67/8796093022208), by norm_num⟩
  | 11 => ⟨((424597215/140737488355328), (-112762425/17592186044416)), (191/140737488355328), by norm_num⟩
  | 12 => ⟨((-550818687/1125899906842624), (1170269585/1125899906842624)), (125/562949953421312), by norm_num⟩
  | 13 => ⟨((659596107/9007199254740992), (-1401378131/9007199254740992)), (301/9007199254740992), by norm_num⟩
  | 14 => ⟨((-366718503/36028797018963968), (779130265/36028797018963968)), (169/36028797018963968), by norm_num⟩
  | 15 => ⟨((380587337/288230376151711744), (-808595995/288230376151711744)), (177/288230376151711744), by norm_num⟩
  | 16 => ⟨((-370294381/2305843009213693952), (786727577/2305843009213693952)), (87/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (1309588030761/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779375024213337/633825300114114700748351602688), (775421463777/158456325028528675187087900672)), (92505/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890423528048585/39614081257132168796771975168), (3488870989085/39614081257132168796771975168)), (13011/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945120379016411/1237940039285380274899124224), (1853144800455/1237940039285380274899124224)), (13827/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885953251771275/77371252455336267181195264), (3705574364843/154742504910672534362390528)), (55321/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387555991936401/2417851639229258349412352), (3473216131441/9671406556917033397649408)), (51877/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259374873176345/604462909807314587353088), (3038304394869/604462909807314587353088)), (22703/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888743600377657/75557863725914323419136), (4935820411813/75557863725914323419136)), (36905/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298252242737235/4722366482869645213696), (925154838309/1180591620717411303424)), (13845/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811213387646437/295147905179352825856), (2543163696637/295147905179352825856)), (76183/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824695808016053/73786976294838206464), (3177436860795/36893488147419103232)), (190567/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912013891893221/4611686018427387904), (1786265101841/2305843009213693952)), (26817/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797636301799917/576460752303423488), (7139846712513/1152921504606846976)), (214723/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298925630453855/36028797018963968), (6241503172991/144115188075855872)), (188093/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493311773456281/36028797018963968), (146102127021/562949953421312)), (282561/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491336214429511/9007199254740992), (11667677807279/9007199254740992)), (353939/9007199254740992), by norm_num⟩
  | 2 => ⟨((279007749428523/562949953421312), (5818484903751/1125899906842624)), (355047/2251799813685248), by norm_num⟩
  | 1 => ⟨((555541803341421/562949953421312), (17378791730489/1125899906842624)), (535345/1125899906842624), by norm_num⟩
  | 0 => ⟨((548108327438973/562949953421312), (34451574900403/1125899906842624)), (540911/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548108327438973/562949953421312), (34451574900403/1125899906842624)), (2063411714793968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((533130892063605/562949953421312), (33543292759039/562949953421312)), (271601/140737488355328), by norm_num⟩
  | 2 => ⟨((502892653002037/562949953421312), (15883264118501/140737488355328)), (2187183/562949953421312), by norm_num⟩
  | 3 => ⟨((1768289132389343/2251799813685248), (454041175480883/2251799813685248)), (17605497/2251799813685248), by norm_num⟩
  | 4 => ⟨((1297048276202781/2251799813685248), (356548602313879/1125899906842624)), (17375093/1125899906842624), by norm_num⟩
  | 5 => ⟨((521283730649051/2251799813685248), (821495316241055/2251799813685248)), (31020933/1125899906842624), by norm_num⟩
  | 6 => ⟨((-716081108661013/9007199254740992), (760693096354819/4503599627370496)), (147985659/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1619161435/33554432)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-1730270821/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((399987883253543/9007199254740992), (-361048570626329/2251799813685248)), (3415707/140737488355328), by norm_num⟩
  | 1 => ⟨((-6197031/67108864), (1431998055/4294967296)), (219/4294967296), by norm_num⟩
  | 2 => ⟨((206181819/2147483648), (-744439061/2147483648)), (231/4294967296), by norm_num⟩
  | 3 => ⟨((-285828693/4294967296), (1032011673/4294967296)), (81/2147483648), by norm_num⟩
  | 4 => ⟨((297182029/8589934592), (-268250993/2147483648)), (85/4294967296), by norm_num⟩
  | 5 => ⟨((-247189063/17179869184), (446249807/8589934592)), (9/1073741824), by norm_num⟩
  | 6 => ⟨((85669201/17179869184), (-618633591/34359738368)), (101/34359738368), by norm_num⟩
  | 7 => ⟨((-50898313/34359738368), (1470185587/274877906944)), (243/274877906944), by norm_num⟩
  | 8 => ⟨((211680133/549755813888), (-382145623/274877906944)), (255/1099511627776), by norm_num⟩
  | 9 => ⟨((-195633983/2199023255552), (1412710193/4398046511104)), (119/2199023255552), by norm_num⟩
  | 10 => ⟨((325447545/17592186044416), (-1175059305/17592186044416)), (25/2199023255552), by norm_num⟩
  | 11 => ⟨((-123045299/35184372088832), (888533503/70368744177664)), (153/70368744177664), by norm_num⟩
  | 12 => ⟨((42644251/70368744177664), (-1231768985/562949953421312)), (107/281474976710656), by norm_num⟩
  | 13 => ⟨((-436559887/4503599627370496), (1576240983/4503599627370496)), (69/1125899906842624), by norm_num⟩
  | 14 => ⟨((259371647/18014398509481984), (-468242997/9007199254740992)), (83/9007199254740992), by norm_num⟩
  | 15 => ⟨((-287652361/144115188075855872), (519298101/72057594037927936)), (93/72057594037927936), by norm_num⟩
  | 16 => ⟨((299078135/1152921504606846976), (-269962511/288230376151711744)), (49/288230376151711744), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-1694185007811/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111200023240907/39614081257132168796771975168), (-501477506287/158456325028528675187087900672)), (46199/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890227247607167/39614081257132168796771975168), (-2256290719945/39614081257132168796771975168)), (12995/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890032467935267/2475880078570760549798248448), (-74902188003/77371252455336267181195264)), (13809/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771698503403063/154742504910672534362390528), (-149773524979/9671406556917033397649408)), (110489/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550029275554255/9671406556917033397649408), (-2246078526115/9671406556917033397649408)), (103601/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259204825289735/604462909807314587353088), (-1964794495505/604462909807314587353088)), (90669/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888467849314039/75557863725914323419136), (-797952109117/18889465931478580854784)), (147369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324511483440207/1180591620717411303424), (-1196498410001/2361183241434822606848)), (110555/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622143919341185/590295810358705651712), (-3288974460489/590295810358705651712)), (38015/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824343465308555/73786976294838206464), (-4109124756553/73786976294838206464)), (190145/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823633083891283/9223372036854775808), (-4619888550507/9223372036854775808)), (107005/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594880008079705/1152921504606846976), (-4616294818429/1152921504606846976)), (214131/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195361364463267/144115188075855872), (-126100566733/4503599627370496)), (187501/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492804755657067/36028797018963968), (-3022377666025/18014398509481984)), (281523/36028797018963968), by norm_num⟩
  | 3 => ⟨((372677669585659/2251799813685248), (-3770917952955/4503599627370496)), (176191/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115417774447945/2251799813685248), (-3760354258135/1125899906842624)), (706197/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110194409103329/1125899906842624), (-22456733310075/2251799813685248)), (531445/1125899906842624), by norm_num⟩
  | 0 => ⟨((2189119885157077/2251799813685248), (-44493363648895/2251799813685248)), (267525/281474976710656), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189119885157077/2251799813685248), (-44493363648895/2251799813685248)), (1020526887060069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((265913192142383/281474976710656), (-43254869517871/1125899906842624)), (4245831/2251799813685248), by norm_num⟩
  | 2 => ⟨((501592646683867/562949953421312), (-163453825467731/2251799813685248)), (4174211/1125899906842624), by norm_num⟩
  | 3 => ⟨((443956624602525/562949953421312), (-72819294529369/562949953421312)), (16089007/2251799813685248), by norm_num⟩
  | 4 => ⟨((1362784266751137/2251799813685248), (-459417154348725/2251799813685248)), (7384681/562949953421312), by norm_num⟩
  | 5 => ⟨((731022725017707/2251799813685248), (-556076491362153/2251799813685248)), (47806653/2251799813685248), by norm_num⟩
  | 6 => ⟨((399987883253543/9007199254740992), (-361048570626329/2251799813685248)), (3415707/140737488355328), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1730270821/33554432)), (1/16777216), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile031Terms0
