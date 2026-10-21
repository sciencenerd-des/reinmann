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
namespace Reinmann.XiBand58.Tile002Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2403/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2403/160))
  have he : value ((15/16), (2403/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-698616979/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-162402473606005/562949953421312), (489997388257379/1125899906842624)), (51762921/2251799813685248), by norm_num⟩
  | 1 => ⟨((429415957/2147483648), (-647812477/2147483648)), (9/536870912), by norm_num⟩
  | 2 => ⟨((-74412115/1073741824), (28064337/268435456)), (13/2147483648), by norm_num⟩
  | 3 => ⟨((68771397/4294967296), (-103747819/4294967296)), (25/17179869184), by norm_num⟩
  | 4 => ⟨((-762699199/274877906944), (287650033/68719476736)), (71/274877906944), by norm_num⟩
  | 5 => ⟨((845860479/2199023255552), (-319014095/549755813888)), (81/2199023255552), by norm_num⟩
  | 6 => ⟨((-781741075/17592186044416), (1179326509/17592186044416)), (77/17592186044416), by norm_num⟩
  | 7 => ⟨((619270425/140737488355328), (-934224965/140737488355328)), (63/140737488355328), by norm_num⟩
  | 8 => ⟨((-429245549/1125899906842624), (647555401/1125899906842624)), (45/1125899906842624), by norm_num⟩
  | 9 => ⟨((264471415/9007199254740992), (-398978845/9007199254740992)), (57/18014398509481984), by norm_num⟩
  | 10 => ⟨((-293308185/144115188075855872), (884963397/288230376151711744)), (65/288230376151711744), by norm_num⟩
  | 11 => ⟨((147858721/1152921504606846976), (-446116279/2305843009213693952)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-68325237/9223372036854775808), (103074747/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 13 => ⟨((466308385/1180591620717411303424), (-703468015/1180591620717411303424)), (7/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-369394677/18889465931478580854784), (1114529991/37778931862957161709568)), (91/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((546229075/604462909807314587353088), (-412017771/302231454903657293676544)), (69/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-757234287/19342813113834066795298816), (1142355825/19342813113834066795298816)), (49/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (2808647470001/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445240544441707/158456325028528675187087900672), (3331704162227/633825300114114700748351602688)), (23133/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892208828730523/39614081257132168796771975168), (1873967664399/19807040628566084398385987584)), (26029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946068677855295/1237940039285380274899124224), (995478903739/618970019642690137449562112)), (13831/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773802781258439/154742504910672534362390528), (3981616636365/154742504910672534362390528)), (27669/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552001388067555/9671406556917033397649408), (933111962115/2417851639229258349412352)), (25947/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315232443958623/151115727451828646838272), (3265574025517/604462909807314587353088)), (22711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891269679281111/75557863725914323419136), (5305961638805/75557863725914323419136)), (18459/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650073121777095/2361183241434822606848), (3978949396513/4722366482869645213696)), (27701/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812515059367749/295147905179352825856), (5470207069335/590295810358705651712)), (9527/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1827948625196235/73786976294838206464), (6836485658249/73786976294838206464)), (2979/4611686018427387904), by norm_num⟩
  | 7 => ⟨((456921332304641/2305843009213693952), (7689294686415/9223372036854775808)), (53661/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799463902600771/576460752303423488), (3843551750455/576460752303423488)), (53711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599449092202339/72057594037927936), (6723748300563/144115188075855872)), (23527/72057594037927936), by norm_num⟩
  | 4 => ⟨((187262498090679/4503599627370496), (10080682485437/36028797018963968)), (70693/36028797018963968), by norm_num⟩
  | 3 => ⟨((748656111379779/4503599627370496), (12592195948521/9007199254740992)), (88563/9007199254740992), by norm_num⟩
  | 2 => ⟨((280498275041739/562949953421312), (1572398228267/281474976710656)), (22215/562949953421312), by norm_num⟩
  | 1 => ⟨((1119991918353139/1125899906842624), (1177260520175/70368744177664)), (134031/1125899906842624), by norm_num⟩
  | 0 => ⟨((278473362635955/281474976710656), (4692673276679/140737488355328)), (33879/140737488355328), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278473362635955/281474976710656), (4692673276679/140737488355328)), (129238129198980287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1100763270299147/1125899906842624), (37141049549197/562949953421312)), (554359/1125899906842624), by norm_num⟩
  | 2 => ⟨((1071287011982855/1125899906842624), (145247380928441/1125899906842624)), (578557/562949953421312), by norm_num⟩
  | 3 => ⟨((1000585445944131/1125899906842624), (276404024491877/1125899906842624)), (625131/281474976710656), by norm_num⟩
  | 4 => ⟨((821362577845183/1125899906842624), (491279628723897/1125899906842624)), (2836081/562949953421312), by norm_num⟩
  | 5 => ⟨((769661331441885/2251799813685248), (44799575415087/70368744177664)), (26451799/2251799813685248), by norm_num⟩
  | 6 => ⟨((-162402473606005/562949953421312), (489997388257379/1125899906842624)), (51762921/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-698616979/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-553640857/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-282407765454287/1125899906842624), (4469663047985/17592186044416)), (35964101/1125899906842624), by norm_num⟩
  | 1 => ⟨((591767581/2147483648), (-37463583/134217728)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-650123137/4294967296), (658527243/4294967296)), (87/4294967296), by norm_num⟩
  | 3 => ⟨((59519439/1073741824), (-120577687/2147483648)), (65/8589934592), by norm_num⟩
  | 4 => ⟨((-523110297/34359738368), (529872515/34359738368)), (73/34359738368), by norm_num⟩
  | 5 => ⟨((919512641/274877906944), (-465699565/137438953472)), (131/274877906944), by norm_num⟩
  | 6 => ⟨((-673458591/1099511627776), (682164353/1099511627776)), (99/1099511627776), by norm_num⟩
  | 7 => ⟨((422782791/4398046511104), (-856496161/8796093022208)), (127/8796093022208), by norm_num⟩
  | 8 => ⟨((-928948739/70368744177664), (117619651/8796093022208)), (71/35184372088832), by norm_num⟩
  | 9 => ⟨((226789889/140737488355328), (-918886357/562949953421312)), (141/562949953421312), by norm_num⟩
  | 10 => ⟨((-797293309/4503599627370496), (807599875/4503599627370496)), (63/2251799813685248), by norm_num⟩
  | 11 => ⟨((637029983/36028797018963968), (-322632417/18014398509481984)), (103/36028797018963968), by norm_num⟩
  | 12 => ⟨((-933131957/576460752303423488), (472597251/288230376151711744)), (153/576460752303423488), by norm_num⟩
  | 13 => ⟨((630861683/4611686018427387904), (-639016797/4611686018427387904)), (105/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-198020685/18446744073709551616), (401160975/36893488147419103232)), (67/36893488147419103232), by norm_num⟩
  | 15 => ⟨((928204621/1180591620717411303424), (-940203471/1180591620717411303424)), (159/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-1019737003/18889465931478580854784), (1032919087/18889465931478580854784)), (89/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (3060841183503/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780373885676417/633825300114114700748351602688), (1814295829277/316912650057057350374175801344)), (46279/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472886747613575/9903520314283042199192993792), (4081773960161/39614081257132168796771975168)), (52075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59107316611299/77371252455336267181195264), (4336427048419/2475880078570760549798248448)), (55343/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773099533591345/154742504910672534362390528), (4335911938619/154742504910672534362390528)), (27679/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775671034237047/4835703278458516698824704), (1016092519057/2417851639229258349412352)), (25957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630176423188637/302231454903657293676544), (3555776380665/604462909807314587353088)), (355/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((945166061292815/37778931862957161709568), (5777110027859/75557863725914323419136)), (36935/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649721517846355/2361183241434822606848), (4331934106059/4722366482869645213696)), (55429/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406015785685585/147573952589676412928), (2977474597373/295147905179352825856)), (76257/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826739808074243/73786976294838206464), (7441495707959/73786976294838206464)), (11923/9223372036854775808), by norm_num⟩
  | 7 => ⟨((57072664920289/288230376151711744), (8368669556803/9223372036854775808)), (53697/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597567589368609/1152921504606846976), (4182450994699/576460752303423488)), (107503/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598853906568439/72057594037927936), (7315049117635/144115188075855872)), (23547/36028797018963968), by norm_num⟩
  | 4 => ⟨((187039258548161/4503599627370496), (10964089419729/36028797018963968)), (141527/36028797018963968), by norm_num⟩
  | 3 => ⟨((373769802607827/2251799813685248), (13690255339729/9007199254740992)), (44335/2251799813685248), by norm_num⟩
  | 2 => ⟨((279939796670477/562949953421312), (854247050693/140737488355328)), (88993/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116638879787905/1125899906842624), (5111527688925/281474976710656)), (268597/1125899906842624), by norm_num⟩
  | 0 => ⟨((276794801570515/281474976710656), (40668578248131/1125899906842624)), (271841/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((276794801570515/281474976710656), (40668578248131/1125899906842624)), (1036991121532249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((271825198254005/281474976710656), (79984737385149/1125899906842624)), (1108561/1125899906842624), by norm_num⟩
  | 2 => ⟨((522171397800395/562949953421312), (154485257276439/1125899906842624)), (574655/281474976710656), by norm_num⟩
  | 3 => ⟨((118437057939625/140737488355328), (286589535149033/1125899906842624)), (4895019/1125899906842624), by norm_num⟩
  | 4 => ⟨((724412518167379/1125899906842624), (482356503245799/1125899906842624)), (5365375/562949953421312), by norm_num⟩
  | 5 => ⟨((259441979237075/1125899906842624), (1241407294012833/2251799813685248)), (46005997/2251799813685248), by norm_num⟩
  | 6 => ⟨((-282407765454287/1125899906842624), (4469663047985/17592186044416)), (35964101/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-553640857/33554432)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-698616979/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-478192371977761/4503599627370496), (-1130854171740899/4503599627370496)), (106783771/4503599627370496), by norm_num⟩
  | 1 => ⟨((158051345/1073741824), (1495072137/4294967296)), (9/268435456), by norm_num⟩
  | 2 => ⟨((-438211377/4294967296), (-1036305037/4294967296)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((404993307/8589934592), (239437305/2147483648)), (3/268435456), by norm_num⟩
  | 4 => ⟨((-280719969/17179869184), (-1327722343/34359738368)), (135/34359738368), by norm_num⟩
  | 5 => ⟨((38916051/8589934592), (736245599/68719476736)), (19/17179869184), by norm_num⟩
  | 6 => ⟨((-575457089/549755813888), (-680435415/274877906944)), (143/549755813888), by norm_num⟩
  | 7 => ⟨((227929405/1099511627776), (1078038605/2199023255552)), (115/2199023255552), by norm_num⟩
  | 8 => ⟨((-315977249/8796093022208), (-1494478839/17592186044416)), (81/8796093022208), by norm_num⟩
  | 9 => ⟨((48670831/8796093022208), (920794483/70368744177664)), (51/35184372088832), by norm_num⟩
  | 10 => ⟨((-431821431/562949953421312), (-31912305/17592186044416)), (115/562949953421312), by norm_num⟩
  | 11 => ⟨((435368447/4503599627370496), (128697741/562949953421312)), (59/2251799813685248), by norm_num⟩
  | 12 => ⟨((-201182941/18014398509481984), (-951535747/36028797018963968)), (111/36028797018963968), by norm_num⟩
  | 13 => ⟨((343260033/288230376151711744), (811759163/288230376151711744)), (97/288230376151711744), by norm_num⟩
  | 14 => ⟨((-543839369/4611686018427387904), (-80381225/288230376151711744)), (39/1152921504606846976), by norm_num⟩
  | 15 => ⟨((25130715/2305843009213693952), (237721683/9223372036854775808)), (59/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-69677137/73786976294838206464), (-1318208915/590295810358705651712)), (83/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (-2567255443885/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889979789364107/316912650057057350374175801344), (-1521049583849/316912650057057350374175801344)), (23125/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945540535752085/19807040628566084398385987584), (-213872323005/2475880078570760549798248448)), (52041/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945469653037413/1237940039285380274899124224), (-1817673110589/1237940039285380274899124224)), (55305/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221575618521031/19342813113834066795298816), (-454350317437/19342813113834066795298816)), (55317/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387719662418047/2417851639229258349412352), (-1703524873285/4835703278458516698824704)), (51873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629973804959059/302231454903657293676544), (-2980590925027/604462909807314587353088)), (22701/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889674091365947/75557863725914323419136), (-2421188656533/37778931862957161709568)), (73803/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298949930466489/4722366482869645213696), (-3630835478253/4722366482869645213696)), (55375/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623385802453871/590295810358705651712), (-2495429604257/295147905179352825856)), (76175/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456473537882945/18446744073709551616), (-779533108383/9223372036854775808)), (11909/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825375314261077/9223372036854775808), (-7012623257377/9223372036854775808)), (107253/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798309688013835/576460752303423488), (-7008655392785/1152921504606846976)), (107345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299220023526067/36028797018963968), (-383006897267/9007199254740992)), (47015/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495076422768599/36028797018963968), (-286976286089/1125899906842624)), (141251/36028797018963968), by norm_num⟩
  | 3 => ⟨((746769515370335/4503599627370496), (-11463437950789/9007199254740992)), (44231/2251799813685248), by norm_num⟩
  | 2 => ⟨((559114656172839/1125899906842624), (-11440026103479/2251799813685248)), (177467/2251799813685248), by norm_num⟩
  | 1 => ⟨((1114369794253263/1125899906842624), (-8550769564033/562949953421312)), (267557/1125899906842624), by norm_num⟩
  | 0 => ⟨((34460741037961/35184372088832), (-33969257446665/1125899906842624)), (135139/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((34460741037961/35184372088832), (-33969257446665/1125899906842624)), (515514374853038699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((134879861344659/140737488355328), (-66541234907695/1125899906842624)), (136437/140737488355328), by norm_num⟩
  | 2 => ⟨((128774456856067/140737488355328), (-31885862974165/281474976710656)), (2221151/1125899906842624), by norm_num⟩
  | 3 => ⟨((232044551384167/281474976710656), (-233403891677715/1125899906842624)), (2283963/562949953421312), by norm_num⟩
  | 4 => ⟨((358396603320695/562949953421312), (-384830665720941/1125899906842624)), (18850775/2251799813685248), by norm_num⟩
  | 5 => ⟨((649609894424017/2251799813685248), (-979994776514751/2251799813685248)), (36888651/2251799813685248), by norm_num⟩
  | 6 => ⟨((-478192371977761/4503599627370496), (-1130854171740899/4503599627370496)), (106783771/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-698616979/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-202767299/8388608)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((71304301656437/562949953421312), (816513282868733/4503599627370496)), (15479563/1125899906842624), by norm_num⟩
  | 1 => ⟨((-875548145/4294967296), (-626624791/2147483648)), (97/4294967296), by norm_num⟩
  | 2 => ⟨((704570189/4294967296), (31516053/134217728)), (5/268435456), by norm_num⟩
  | 3 => ⟨((-377987325/4294967296), (-270523363/2147483648)), (11/1073741824), by norm_num⟩
  | 4 => ⟨((608347131/17179869184), (870781113/17179869184)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((-783277549/68719476736), (-560587255/34359738368)), (3/2147483648), by norm_num⟩
  | 6 => ⟨((840424389/274877906944), (601486921/137438953472)), (105/274877906944), by norm_num⟩
  | 7 => ⟨((-193230125/274877906944), (-276587387/274877906944)), (99/1099511627776), by norm_num⟩
  | 8 => ⟨((310991889/2199023255552), (445150227/2199023255552)), (41/2199023255552), by norm_num⟩
  | 9 => ⟨((-222454283/8796093022208), (-19901157/549755813888)), (15/4398046511104), by norm_num⟩
  | 10 => ⟨((572842171/140737488355328), (819959721/140737488355328)), (79/140737488355328), by norm_num⟩
  | 11 => ⟨((-670511933/1125899906842624), (-239940775/281474976710656)), (47/562949953421312), by norm_num⟩
  | 12 => ⟨((719431551/9007199254740992), (32180815/281474976710656)), (103/9007199254740992), by norm_num⟩
  | 13 => ⟨((-712541793/72057594037927936), (-1019924159/72057594037927936)), (13/9007199254740992), by norm_num⟩
  | 14 => ⟨((327654793/288230376151711744), (469001317/288230376151711744)), (97/576460752303423488), by norm_num⟩
  | 15 => ⟨((-562496049/4611686018427387904), (-805150401/4611686018427387904)), (85/4611686018427387904), by norm_num⟩
  | 16 => ⟨((226325617/18446744073709551616), (323959895/18446744073709551616)), (35/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (1251804026677/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779640495652827/633825300114114700748351602688), (741414127115/316912650057057350374175801344)), (46173/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472680592497443/9903520314283042199192993792), (833979136439/19807040628566084398385987584)), (25975/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118159907427483/154742504910672534362390528), (55372898181/77371252455336267181195264)), (27601/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772224535562307/154742504910672534362390528), (1771625767277/154742504910672534362390528)), (6901/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193815301344667/1208925819614629174706176), (1660573061587/9671406556917033397649408)), (12941/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629818149306555/302231454903657293676544), (1452675406981/604462909807314587353088)), (11325/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889168955932987/75557863725914323419136), (73749575033/2361183241434822606848)), (73625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298571730814697/4722366482869645213696), (1769455213165/4722366482869645213696)), (55229/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811433418339681/295147905179352825856), (2432132505163/590295810358705651712)), (75957/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825247031334917/73786976294838206464), (1519431761403/36893488147419103232)), (94973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912324742204447/4611686018427387904), (3416931893457/9223372036854775808)), (106879/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595896268960647/1152921504606846976), (426837021919/144115188075855872)), (26731/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196250434875427/144115188075855872), (2985345680249/144115188075855872)), (93609/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494138043643535/36028797018963968), (2236497922847/18014398509481984)), (140513/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492376728173863/9007199254740992), (5582464730785/9007199254740992)), (87909/4503599627370496), by norm_num⟩
  | 2 => ⟨((279270743871729/562949953421312), (5569313807663/2251799813685248)), (88041/1125899906842624), by norm_num⟩
  | 1 => ⟨((2225380117662903/2251799813685248), (8321160495517/1125899906842624)), (132393/562949953421312), by norm_num⟩
  | 0 => ⟨((274885614155119/281474976710656), (8255741027285/562949953421312)), (1064461/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((274885614155119/281474976710656), (8255741027285/562949953421312)), (4060596474654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1073559894201417/1125899906842624), (64499785213197/2251799813685248)), (1055153/1125899906842624), by norm_num⟩
  | 2 => ⟨((511364635464693/562949953421312), (123002732602895/2251799813685248)), (2072651/1125899906842624), by norm_num⟩
  | 3 => ⟨((1851306207994001/2251799813685248), (223463017045733/2251799813685248)), (1995943/562949953421312), by norm_num⟩
  | 4 => ⟨((749933216808151/1125899906842624), (91859513487743/562949953421312)), (14712219/2251799813685248), by norm_num⟩
  | 5 => ⟨((939065978399259/2251799813685248), (489482235681001/2251799813685248)), (12200105/1125899906842624), by norm_num⟩
  | 6 => ⟨((71304301656437/562949953421312), (816513282868733/4503599627370496)), (15479563/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-202767299/8388608)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-112727759/67108864), (-902949347/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-86047524962551/2251799813685248), (-205428795465305/1125899906842624)), (70807613/4503599627370496), by norm_num⟩
  | 1 => ⟨((294068275/4294967296), (1404109915/4294967296)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((-16465613/268435456), (-628956809/2147483648)), (7/268435456), by norm_num⟩
  | 3 => ⟨((314692459/8589934592), (751292879/4294967296)), (135/8589934592), by norm_num⟩
  | 4 => ⟨((-281926597/17179869184), (-673068065/8589934592)), (123/17179869184), by norm_num⟩
  | 5 => ⟨((50514465/8589934592), (964780863/34359738368)), (45/17179869184), by norm_num⟩
  | 6 => ⟨((-241359389/137438953472), (-36013651/4294967296)), (55/68719476736), by norm_num⟩
  | 7 => ⟨((30889855/68719476736), (589968459/274877906944)), (57/274877906944), by norm_num⟩
  | 8 => ⟨((-221388761/2199023255552), (-1057081573/2199023255552)), (13/274877906944), by norm_num⟩
  | 9 => ⟨((88150091/4398046511104), (1683587483/17592186044416)), (21/2199023255552), by norm_num⟩
  | 10 => ⟨((-1974297/549755813888), (-603316763/35184372088832)), (61/35184372088832), by norm_num⟩
  | 11 => ⟨((329305865/562949953421312), (98272593/35184372088832)), (161/562949953421312), by norm_num⟩
  | 12 => ⟨((-196678967/2251799813685248), (-469548931/1125899906842624)), (49/1125899906842624), by norm_num⟩
  | 13 => ⟨((216862401/18014398509481984), (1035469223/18014398509481984)), (109/18014398509481984), by norm_num⟩
  | 14 => ⟨((-55509323/36028797018963968), (-1060178163/144115188075855872)), (113/144115188075855872), by norm_num⟩
  | 15 => ⟨((106089979/576460752303423488), (1013111607/1152921504606846976)), (55/576460752303423488), by norm_num⟩
  | 16 => ⟨((-47521931/2305843009213693952), (-453813079/4611686018427387904)), (25/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790893836630535/5070602400912917605986812821504), (-72345679681/316912650057057350374175801344)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779373947910179/633825300114114700748351602688), (-1370770275549/316912650057057350374175801344)), (11559/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945211191184801/19807040628566084398385987584), (-3083770130565/39614081257132168796771975168)), (52023/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945119812007261/1237940039285380274899124224), (-3275943521081/2475880078570760549798248448)), (55285/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771905463145201/154742504910672534362390528), (-3275311084973/154742504910672534362390528)), (27/75557863725914323419136), by norm_num⟩
  | 13 => ⟨((1550223091794279/9671406556917033397649408), (-3069932287667/9671406556917033397649408)), (12963/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259374206082699/604462909807314587353088), (-1342759509809/302231454903657293676544)), (45383/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472185675633887/18889465931478580854784), (-4362709169339/75557863725914323419136)), (73769/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298251732145631/4722366482869645213696), (-1635465152151/2361183241434822606848)), (55347/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811213168767279/295147905179352825856), (-561967450073/73786976294838206464)), (76133/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824695656876033/73786976294838206464), (-2808495501365/36893488147419103232)), (47607/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456007039421023/2305843009213693952), (-6315426455799/9223372036854775808)), (53591/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797636828218329/576460752303423488), (-6310818009421/1152921504606846976)), (107265/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37365756422391/4503599627370496), (-1379196029619/36028797018963968)), (46975/72057594037927936), by norm_num⟩
  | 4 => ⟨((186664477575523/4503599627370496), (-8264820055383/36028797018963968)), (70555/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491343928647141/9007199254740992), (-5156458981039/4503599627370496)), (88357/4503599627370496), by norm_num⟩
  | 2 => ⟨((558021339926741/1125899906842624), (-5142894761589/1125899906842624)), (177203/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111110997273849/1125899906842624), (-15360975999305/1125899906842624)), (267031/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096310591740063/1125899906842624), (-3806474500737/140737488355328)), (134745/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1096310591740063/1125899906842624), (-3806474500737/140737488355328)), (514011384130382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((533337641464665/562949953421312), (-14825752402979/281474976710656)), (1078787/1125899906842624), by norm_num⟩
  | 2 => ⟨((503721203532297/562949953421312), (-224734203002979/2251799813685248)), (4315449/2251799813685248), by norm_num⟩
  | 3 => ⟨((890233520724821/1125899906842624), (-402179208022105/2251799813685248)), (8584211/2251799813685248), by norm_num⟩
  | 4 => ⟨((667980064666541/1125899906842624), (-635995100708155/2251799813685248)), (16641175/2251799813685248), by norm_num⟩
  | 5 => ⟨((153244050676059/562949953421312), (-188663328736743/562949953421312)), (29146155/2251799813685248), by norm_num⟩
  | 6 => ⟨((-86047524962551/2251799813685248), (-205428795465305/1125899906842624)), (70807613/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-112727759/67108864), (-902949347/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-122426081/67108864), (-1961265815/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-105540223991453/1125899906842624), (1182693858144421/9007199254740992)), (65352207/4503599627370496), by norm_num⟩
  | 1 => ⟨((783431217/4294967296), (-1097400657/4294967296)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((-381121689/2147483648), (533860769/2147483648)), (121/4294967296), by norm_num⟩
  | 3 => ⟨((247209521/2147483648), (-10821303/67108864)), (5/268435456), by norm_num⟩
  | 4 => ⟨((-120261879/2147483648), (673833067/8589934592)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((748860195/34359738368), (-1048974883/34359738368)), (125/34359738368), by norm_num⟩
  | 6 => ⟨((-242869109/34359738368), (85050453/8589934592)), (41/34359738368), by norm_num⟩
  | 7 => ⟨((540115959/274877906944), (-94571737/34359738368)), (93/274877906944), by norm_num⟩
  | 8 => ⟨((-525508563/1099511627776), (736112411/1099511627776)), (23/274877906944), by norm_num⟩
  | 9 => ⟨((113621383/1099511627776), (-318313025/2199023255552)), (81/4398046511104), by norm_num⟩
  | 10 => ⟨((-88438801/4398046511104), (495526837/17592186044416)), (1/274877906944), by norm_num⟩
  | 11 => ⟨((31289811/8796093022208), (-701273237/140737488355328)), (23/35184372088832), by norm_num⟩
  | 12 => ⟨((-81182881/140737488355328), (227435785/281474976710656)), (61/562949953421312), by norm_num⟩
  | 13 => ⟨((777721069/9007199254740992), (-544701049/4503599627370496)), (37/2251799813685248), by norm_num⟩
  | 14 => ⟨((-432392949/36028797018963968), (1211359199/72057594037927936)), (167/72057594037927936), by norm_num⟩
  | 15 => ⟨((112186377/72057594037927936), (-628585643/288230376151711744)), (11/36028797018963968), by norm_num⟩
  | 16 => ⟨((-436609219/2305843009213693952), (611585591/2305843009213693952)), (87/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395399856174459/2535301200456458802993406410752), (2853746601391/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111196809968393/39614081257132168796771975168), (844663999057/158456325028528675187087900672)), (46267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890169191402213/39614081257132168796771975168), (3800366599951/39614081257132168796771975168)), (52061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944985251432167/1237940039285380274899124224), (2018568320795/1237940039285380274899124224)), (55327/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771636223146583/154742504910672534362390528), (504536218143/19342813113834066795298816)), (55341/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((3027286236567/18889465931478580854784), (1891560970171/4835703278458516698824704)), (51897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259153108687497/604462909807314587353088), (3309332150119/604462909807314587353088)), (2839/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((59011974473673/2361183241434822606848), (1343994601687/18889465931478580854784)), (36921/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648990943130765/2361183241434822606848), (1007627143707/1180591620717411303424)), (27703/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622054964585875/590295810358705651712), (5539552631767/590295810358705651712)), (76223/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912115469605253/36893488147419103232), (1730211708905/18446744073709551616)), (95337/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28492260345107/144115188075855872), (243156646377/288230376151711744)), (13417/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594749302524809/1152921504606846976), (3887420099675/576460752303423488)), (107437/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195244432938507/144115188075855872), (6796044600415/144115188075855872)), (94123/144115188075855872), by norm_num⟩
  | 4 => ⟨((373156060666361/9007199254740992), (1272524304763/4503599627370496)), (141413/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490476112986703/9007199254740992), (12700985800617/9007199254740992)), (11073/562949953421312), by norm_num⟩
  | 2 => ⟨((139396234944571/281474976710656), (1583079888081/281474976710656)), (177773/2251799813685248), by norm_num⟩
  | 1 => ⟨((277447360185761/281474976710656), (2363278656333/140737488355328)), (67043/281474976710656), by norm_num⟩
  | 0 => ⟨((68351167830301/70368744177664), (37450366647253/1125899906842624)), (542415/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((68351167830301/70368744177664), (37450366647253/1125899906842624)), (2069149021628951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66313582338777/70368744177664), (72753218092109/1125899906842624)), (272453/281474976710656), by norm_num⟩
  | 2 => ⟨((995172581784313/1125899906842624), (137121290844165/1125899906842624)), (1097431/562949953421312), by norm_num⟩
  | 3 => ⟨((215731037285779/281474976710656), (484800995888383/2251799813685248)), (8829307/2251799813685248), by norm_num⟩
  | 4 => ⟨((1218367781367353/2251799813685248), (743132643209631/2251799813685248)), (2166989/281474976710656), by norm_num⟩
  | 5 => ⟨((413968381916107/2251799813685248), (804164619133885/2251799813685248)), (15100987/1125899906842624), by norm_num⟩
  | 6 => ⟨((-105540223991453/1125899906842624), (1182693858144421/9007199254740992)), (65352207/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-122426081/67108864), (-1961265815/67108864)), (1/33554432), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-1047925469/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((315052357878647/2251799813685248), (59061202875755/2251799813685248)), (93814781/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1249566957/4294967296), (-234249723/4294967296)), (95/4294967296), by norm_num⟩
  | 2 => ⟨((81200045/268435456), (243554303/4294967296)), (101/4294967296), by norm_num⟩
  | 3 => ⟨((-225134329/1073741824), (-337637957/8589934592)), (143/8589934592), by norm_num⟩
  | 4 => ⟨((117038419/1073741824), (87762299/4294967296)), (77/8589934592), by norm_num⟩
  | 5 => ⟨((-1557597123/34359738368), (-291994513/34359738368)), (131/34359738368), by norm_num⟩
  | 6 => ⟨((539822027/34359738368), (202395173/68719476736)), (93/68719476736), by norm_num⟩
  | 7 => ⟨((-1282889541/274877906944), (-60124133/68719476736)), (113/274877906944), by norm_num⟩
  | 8 => ⟨((1333846903/1099511627776), (31256155/137438953472)), (15/137438953472), by norm_num⟩
  | 9 => ⟨((-616368147/2199023255552), (-28886821/549755813888)), (57/2199023255552), by norm_num⟩
  | 10 => ⟨((128170153/2199023255552), (96109529/8796093022208)), (97/17592186044416), by norm_num⟩
  | 11 => ⟨((-387668859/35184372088832), (-290696941/140737488355328)), (149/140737488355328), by norm_num⟩
  | 12 => ⟨((537423153/281474976710656), (201495765/562949953421312)), (105/562949953421312), by norm_num⟩
  | 13 => ⟨((-1375433883/4503599627370496), (-64461333/1125899906842624)), (137/4503599627370496), by norm_num⟩
  | 14 => ⟨((204295311/4503599627370496), (306385311/36028797018963968)), (165/36028797018963968), by norm_num⟩
  | 15 => ⟨((-906283001/144115188075855872), (-42474023/36028797018963968)), (47/72057594037927936), by norm_num⟩
  | 16 => ⟨((235570315/288230376151711744), (11040281/72057594037927936)), (25/288230376151711744), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (241392006705/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444740494637969/158456325028528675187087900672), (35716736339/79228162514264337593543950336)), (92229/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944979610108735/19807040628566084398385987584), (80348949755/9903520314283042199192993792)), (103759/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944873949406897/1237940039285380274899124224), (341415141223/2475880078570760549798248448)), (55123/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885707085184571/77371252455336267181195264), (341338785731/154742504910672534362390528)), (110249/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549762964057517/9671406556917033397649408), (319924008023/9671406556917033397649408)), (1615/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1258972053317103/604462909807314587353088), (69963107637/151115727451828646838272)), (90443/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888090064421257/75557863725914323419136), (454608238881/75557863725914323419136)), (146975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81110187854431/295147905179352825856), (42602908887/590295810358705651712)), (110235/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405438889967567/147573952589676412928), (468416130097/590295810358705651712)), (37895/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455964753751521/18446744073709551616), (292598274963/36893488147419103232)), (189485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455772362361179/2305843009213693952), (657901457799/9223372036854775808)), (3331/144115188075855872), by norm_num⟩
  | 6 => ⟨((199292260814801/144115188075855872), (82168261405/144115188075855872)), (106601/576460752303423488), by norm_num⟩
  | 5 => ⟨((597444553470909/72057594037927936), (143638418431/36028797018963968)), (46643/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492100209196711/36028797018963968), (860583774801/36028797018963968)), (139949/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489836697282367/9007199254740992), (536775736547/4503599627370496)), (174971/4503599627370496), by norm_num⟩
  | 2 => ⟨((278638452784199/562949953421312), (2140582355045/4503599627370496)), (700097/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217846770753539/2251799813685248), (1597310727793/1125899906842624)), (1050683/2251799813685248), by norm_num⟩
  | 0 => ⟨((2184233687771637/2251799813685248), (6324530155161/2251799813685248)), (1051777/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2184233687771637/2251799813685248), (6324530155161/2251799813685248)), (4012210850242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2118677146218851/2251799813685248), (1533690044323/281474976710656)), (4092689/2251799813685248), by norm_num⟩
  | 2 => ⟨((996678808102907/1125899906842624), (11544166676069/1125899906842624)), (3873037/1125899906842624), by norm_num⟩
  | 3 => ⟨((1764340458154099/2251799813685248), (40876906422389/2251799813685248)), (13872939/2251799813685248), by norm_num⟩
  | 4 => ⟨((1381662042910015/2251799813685248), (64056120234923/2251799813685248)), (22243249/2251799813685248), by norm_num⟩
  | 5 => ⟨((422969840103421/1125899906842624), (39303631435971/1125899906842624)), (57123141/4503599627370496), by norm_num⟩
  | 6 => ⟨((315052357878647/2251799813685248), (59061202875755/2251799813685248)), (93814781/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-1047925469/33554432)), (1/16777216), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile002Terms0
