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
namespace Reinmann.XiBand97.Tile035Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6581/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6581/256))
  have he : value ((69/80), (6581/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1195796489/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((318373554590815/1125899906842624), (1062263078234771/2251799813685248)), (78640159/2251799813685248), by norm_num⟩
  | 1 => ⟨((-420913185/2147483648), (-702194841/2147483648)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((583509575/8589934592), (973448749/8589934592)), (77/8589934592), by norm_num⟩
  | 3 => ⟨((-134819339/8589934592), (-449828837/17179869184)), (73/34359738368), by norm_num⟩
  | 4 => ⟨((373798579/137438953472), (155898795/34359738368)), (13/34359738368), by norm_num⟩
  | 5 => ⟨((-207277945/549755813888), (-691589185/1099511627776)), (59/1099511627776), by norm_num⟩
  | 6 => ⟨((383130995/8796093022208), (639164125/8796093022208)), (111/17592186044416), by norm_num⟩
  | 7 => ⟨((-303504193/70368744177664), (-1012650997/140737488355328)), (45/70368744177664), by norm_num⟩
  | 8 => ⟨((420746151/1125899906842624), (87739523/140737488355328)), (1/17592186044416), by norm_num⟩
  | 9 => ⟨((-129617337/4503599627370496), (-432472199/9007199254740992)), (81/18014398509481984), by norm_num⟩
  | 10 => ⟨((575000907/288230376151711744), (959254033/288230376151711744)), (23/72057594037927936), by norm_num⟩
  | 11 => ⟨((-579724011/4611686018427387904), (-967133423/4611686018427387904)), (95/4611686018427387904), by norm_num⟩
  | 12 => ⟨((8371543/1152921504606846976), (446910537/36893488147419103232)), (45/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-114268779/295147905179352825856), (-190630633/295147905179352825856)), (79/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((362080375/18889465931478580854784), (1208092213/37778931862957161709568)), (127/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-267706657/302231454903657293676544), (-893211425/604462909807314587353088)), (3/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((371120229/9671406556917033397649408), (619126981/9671406556917033397649408)), (135/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (1342731677679/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781047072259517/633825300114114700748351602688), (99557876229/39614081257132168796771975168)), (46179/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892304606207395/39614081257132168796771975168), (895971897027/19807040628566084398385987584)), (12989/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892239450650957/2475880078570760549798248448), (951911960577/1237940039285380274899124224)), (55209/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773905248935137/154742504910672534362390528), (59490406695/4835703278458516698824704)), (55215/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552097847464653/9671406556917033397649408), (446143278105/2417851639229258349412352)), (12943/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261014573664763/604462909807314587353088), (780681192563/302231454903657293676544)), (45307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118213013612021/4722366482869645213696), (317119135723/9444732965739290427392)), (18409/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300250796523601/4722366482869645213696), (1902486623463/4722366482869645213696)), (55239/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625174933464795/590295810358705651712), (2615548297885/590295810358705651712)), (18993/147573952589676412928), by norm_num⟩
  | 8 => ⟨((914065612278753/36893488147419103232), (3268879159719/73786976294838206464)), (94993/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827892926257415/9223372036854775808), (3676724264693/9223372036854775808)), (106905/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399784529153483/288230376151711744), (3675768280897/1152921504606846976)), (106953/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599542629198197/72057594037927936), (3215221769277/144115188075855872)), (93637/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498386693310393/36028797018963968), (602585214327/4503599627370496)), (140563/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497681267094363/9007199254740992), (6022088031887/9007199254740992)), (43973/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122378107999811/2251799813685248), (6016441933425/2251799813685248)), (88087/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120609253315511/1125899906842624), (9010547911337/1125899906842624)), (33121/140737488355328), by norm_num⟩
  | 0 => ⟨((1115286899282255/1125899906842624), (17964637549155/1125899906842624)), (133191/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115286899282255/1125899906842624), (17964637549155/1125899906842624)), (508083344579601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1104487292299043/1125899906842624), (17795298487157/562949953421312)), (536243/562949953421312), by norm_num⟩
  | 2 => ⟨((541178430183235/562949953421312), (69827454189427/1125899906842624)), (135749/70368744177664), by norm_num⟩
  | 3 => ⟨((259041787980815/281474976710656), (134253895261075/1125899906842624)), (1111345/281474976710656), by norm_num⟩
  | 4 => ⟨((7324823097593/8796093022208), (123554034814141/562949953421312)), (4621163/562949953421312), by norm_num⟩
  | 5 => ⟨((181630022429087/281474976710656), (205775779251651/562949953421312)), (9724887/562949953421312), by norm_num⟩
  | 6 => ⟨((318373554590815/1125899906842624), (1062263078234771/2251799813685248)), (78640159/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1195796489/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1895292593/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-1745084568777313/4503599627370496), (-880303936653/70368744177664)), (209227307/4503599627370496), by norm_num⟩
  | 1 => ⟨((1828357079/4294967296), (14756969/1073741824)), (221/4294967296), by norm_num⟩
  | 2 => ⟨((-502163889/2147483648), (-32424375/4294967296)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((1471155785/17179869184), (11873939/4294967296)), (183/17179869184), by norm_num⟩
  | 4 => ⟨((-25253591/1073741824), (-52179421/68719476736)), (51/17179869184), by norm_num⟩
  | 5 => ⟨((1420487957/274877906944), (45859963/274877906944)), (91/137438953472), by norm_num⟩
  | 6 => ⟨((-1040377017/1099511627776), (-33588213/1099511627776)), (135/1099511627776), by norm_num⟩
  | 7 => ⟨((5102549/34359738368), (42171913/8796093022208)), (43/2199023255552), by norm_num⟩
  | 8 => ⟨((-1435065097/70368744177664), (-23165291/35184372088832)), (191/70368744177664), by norm_num⟩
  | 9 => ⟨((1401404579/562949953421312), (5655483/70368744177664)), (189/562949953421312), by norm_num⟩
  | 10 => ⟨((-615840117/2251799813685248), (-9941093/1125899906842624)), (21/562949953421312), by norm_num⟩
  | 11 => ⟨((984101121/36028797018963968), (63542731/72057594037927936)), (271/72057594037927936), by norm_num⟩
  | 12 => ⟨((-1441527447/576460752303423488), (-46539217/576460752303423488)), (201/576460752303423488), by norm_num⟩
  | 13 => ⟨((974572165/4611686018427387904), (62927453/9223372036854775808)), (137/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-152953851/9223372036854775808), (-39504499/73786976294838206464)), (87/36893488147419103232), by norm_num⟩
  | 15 => ⟨((716957783/590295810358705651712), (23146735/590295810358705651712)), (103/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-787658631/9444732965739290427392), (-50858575/18889465931478580854784)), (57/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-253139714195/633825300114114700748351602688)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((890247929025299/316912650057057350374175801344), (-4802158840941/633825300114114700748351602688)), (543/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((1891683880005495/39614081257132168796771975168), (-5401933274059/39614081257132168796771975168)), (78215/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891579171563257/2475880078570760549798248448), (-1434748634521/618970019642690137449562112)), (41565/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443311029463613/38685626227668133590597632), (-5738364698811/154742504910672534362390528)), (83159/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551477132122969/9671406556917033397649408), (-5379047453891/9671406556917033397649408)), (77993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630235271556021/302231454903657293676544), (-588249599155/75557863725914323419136)), (17069/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890522472655633/75557863725914323419136), (-955748557211/9444732965739290427392)), (55503/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162448125601147/590295810358705651712), (-716673933029/590295810358705651712)), (83307/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624257061502113/590295810358705651712), (-7881624856329/590295810358705651712)), (114631/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826980274338639/73786976294838206464), (-9849346530783/73786976294838206464)), (71707/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826593146832387/9223372036854775808), (-11076820474201/9223372036854775808)), (80757/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798916071092537/576460752303423488), (-692012363655/72057594037927936)), (80865/576460752303423488), by norm_num⟩
  | 5 => ⟨((299483892250759/36028797018963968), (-4841483083237/72057594037927936)), (141759/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496648254725489/36028797018963968), (-7257009670607/18014398509481984)), (106563/18014398509481984), by norm_num⟩
  | 3 => ⟨((747741964438399/4503599627370496), (-18124235795547/9007199254740992)), (133631/4503599627370496), by norm_num⟩
  | 2 => ⟨((560072210326337/1125899906842624), (-18096731371667/2251799813685248)), (268547/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117168150352793/1125899906842624), (-6769021387111/281474976710656)), (406039/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108044214108537/1125899906842624), (-53874630639311/1125899906842624)), (824985/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108044214108537/1125899906842624), (-53874630639311/1125899906842624)), (3147068027976607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1087893779143985/1125899906842624), (-53020230665555/562949953421312)), (425689/281474976710656), by norm_num⟩
  | 2 => ⟨((1041183401949357/1125899906842624), (-204921871861915/1125899906842624)), (3611297/1125899906842624), by norm_num⟩
  | 3 => ⟨((925543999599161/1125899906842624), (-379005718683023/1125899906842624)), (7993707/1125899906842624), by norm_num⟩
  | 4 => ⟨((39578693677965/70368744177664), (-623121942916853/1125899906842624)), (18524185/1125899906842624), by norm_num⟩
  | 5 => ⟨((22623912571969/2251799813685248), (-1401892433405267/2251799813685248)), (20670963/562949953421312), by norm_num⟩
  | 6 => ⟨((-1745084568777313/4503599627370496), (-880303936653/70368744177664)), (209227307/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1895292593/67108864)), (3/67108864), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1195796489/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-160528471921861/1125899906842624), (1201515232651875/4503599627370496)), (239578333/4503599627370496), by norm_num⟩
  | 1 => ⟨((212230411/1073741824), (-794245621/2147483648)), (5/67108864), by norm_num⟩
  | 2 => ⟨((-147106911/1073741824), (550529113/2147483648)), (7/134217728), by norm_num⟩
  | 3 => ⟨((543822617/8589934592), (-1017593873/8589934592)), (209/8589934592), by norm_num⟩
  | 4 => ⟨((-188474557/8589934592), (176335581/4294967296)), (73/8589934592), by norm_num⟩
  | 5 => ⟨((418049945/68719476736), (-782249669/68719476736)), (163/68719476736), by norm_num⟩
  | 6 => ⟨((-96590047/68719476736), (722952203/274877906944)), (153/274877906944), by norm_num⟩
  | 7 => ⟨((306062257/1099511627776), (-286349875/549755813888)), (61/549755813888), by norm_num⟩
  | 8 => ⟨((-424292381/8796093022208), (396965217/4398046511104)), (171/8796093022208), by norm_num⟩
  | 9 => ⟨((522839231/70368744177664), (-489165015/35184372088832)), (213/70368744177664), by norm_num⟩
  | 10 => ⟨((-289923631/281474976710656), (1085002723/562949953421312)), (119/281474976710656), by norm_num⟩
  | 11 => ⟨((292305087/2251799813685248), (-1093915023/4503599627370496)), (121/2251799813685248), by norm_num⟩
  | 12 => ⟨((-540294525/36028797018963968), (126374019/4503599627370496)), (225/36028797018963968), by norm_num⟩
  | 13 => ⟨((460927541/288230376151711744), (-431240837/144115188075855872)), (97/144115188075855872), by norm_num⟩
  | 14 => ⟨((-730264287/4611686018427387904), (1366461121/4611686018427387904)), (155/2305843009213693952), by norm_num⟩
  | 15 => ⟨((539926007/36893488147419103232), (-1010302585/36893488147419103232)), (231/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-374248189/295147905179352825856), (175072097/73786976294838206464)), (81/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (1342731677679/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780119612544325/633825300114114700748351602688), (3182716344169/633825300114114700748351602688)), (92513/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118203816284731/2475880078570760549798248448), (3580164024541/39614081257132168796771975168)), (104097/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891130485496077/2475880078570760549798248448), (3803458867469/2475880078570760549798248448)), (55313/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110799753829697/9671406556917033397649408), (1901467625927/77371252455336267181195264)), (110653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551057747757847/9671406556917033397649408), (3564695458797/9671406556917033397649408)), (103765/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39378257821837/18889465931478580854784), (3118552188603/604462909807314587353088)), (45411/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889928499918047/75557863725914323419136), (5066604177327/75557863725914323419136)), (147637/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299140621338969/4722366482869645213696), (1899520199711/2361183241434822606848)), (55387/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101477988417473/36893488147419103232), (2611098682873/295147905179352825856)), (38097/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826221385282537/73786976294838206464), (3262760973795/36893488147419103232)), (190595/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456435766303483/2305843009213693952), (7338153172989/9223372036854775808)), (214573/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798493321671621/576460752303423488), (916791180229/144115188075855872)), (214765/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197200909097755/144115188075855872), (6413236623941/144115188075855872)), (188135/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495556557905911/36028797018963968), (4805625909589/18014398509481984)), (282633/36028797018963968), by norm_num⟩
  | 3 => ⟨((186767162229927/1125899906842624), (5999504850433/4503599627370496)), (177023/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118824728810473/2251799813685248), (11976427914347/2251799813685248)), (88795/562949953421312), by norm_num⟩
  | 1 => ⟨((1115255799766159/1125899906842624), (17908190559307/1125899906842624)), (267805/562949953421312), by norm_num⟩
  | 0 => ⟨((1104487292299043/1125899906842624), (17795298487157/562949953421312)), (541301/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104487292299043/1125899906842624), (17795298487157/562949953421312)), (2064899446727561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((541178430183235/562949953421312), (69827454189427/1125899906842624)), (1096235/562949953421312), by norm_num⟩
  | 2 => ⟨((259041787980815/281474976710656), (134253895261075/1125899906842624)), (1121827/281474976710656), by norm_num⟩
  | 3 => ⟨((7324823097593/8796093022208), (123554034814141/562949953421312)), (9329497/1125899906842624), by norm_num⟩
  | 4 => ⟨((181630022429087/281474976710656), (205775779251651/562949953421312)), (19633219/1125899906842624), by norm_num⟩
  | 5 => ⟨((318373554590815/1125899906842624), (1062263078234771/2251799813685248)), (79381871/2251799813685248), by norm_num⟩
  | 6 => ⟨((-160528471921861/1125899906842624), (1201515232651875/4503599627370496)), (239578333/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1195796489/33554432)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-347069183/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-241959812659907/1125899906842624), (571197558745947/4503599627370496)), (100170307/2251799813685248), by norm_num⟩
  | 1 => ⟨((371379181/1073741824), (-438359741/2147483648)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-298855867/1073741824), (705512787/4294967296)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((1282639901/8589934592), (-378493009/4294967296)), (137/4294967296), by norm_num⟩
  | 4 => ⟨((-1032164643/17179869184), (304580499/8589934592)), (223/17179869184), by norm_num⟩
  | 5 => ⟨((1328963927/68719476736), (-196081361/17179869184)), (289/68719476736), by norm_num⟩
  | 6 => ⟨((-712961643/137438953472), (13149199/4294967296)), (157/137438953472), by norm_num⟩
  | 7 => ⟨((1311391427/1099511627776), (-386977269/549755813888)), (291/1099511627776), by norm_num⟩
  | 8 => ⟨((-1055301541/4398046511104), (38925993/274877906944)), (59/1099511627776), by norm_num⟩
  | 9 => ⟨((754863249/17592186044416), (-445503779/17592186044416)), (85/8796093022208), by norm_num⟩
  | 10 => ⟨((-971924425/140737488355328), (286804269/70368744177664)), (221/140737488355328), by norm_num⟩
  | 11 => ⟨((1137637831/1125899906842624), (-335704483/562949953421312)), (261/1125899906842624), by norm_num⟩
  | 12 => ⟨((-38144947/281474976710656), (360197015/4503599627370496)), (141/4503599627370496), by norm_num⟩
  | 13 => ⟨((1208948655/72057594037927936), (-713495055/72057594037927936)), (281/72057594037927936), by norm_num⟩
  | 14 => ⟨((-1111844457/576460752303423488), (656186281/576460752303423488)), (65/144115188075855872), by norm_num⟩
  | 15 => ⟨((954370465/4611686018427387904), (-563248575/4611686018427387904)), (225/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-768000005/36893488147419103232), (453256805/36893488147419103232)), (183/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (3397766644187/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779819287584129/633825300114114700748351602688), (4025635826545/633825300114114700748351602688)), (23149/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890923046540545/39614081257132168796771975168), (4528261235721/39614081257132168796771975168)), (26049/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236346394165255/309485009821345068724781056), (2405296763207/1237940039285380274899124224)), (55369/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772436512914339/154742504910672534362390528), (1202455969717/38685626227668133590597632)), (110771/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96920027600663/604462909807314587353088), (1127098026835/2417851639229258349412352)), (51941/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259808878017735/604462909807314587353088), (1972012641299/302231454903657293676544)), (90933/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889448090165257/75557863725914323419136), (6407507619807/75557863725914323419136)), (147831/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298779938285809/4722366482869645213696), (4804288865641/4722366482869645213696)), (110931/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25361738523915/9223372036854775808), (6603716558771/590295810358705651712)), (9539/36893488147419103232), by norm_num⟩
  | 8 => ⟨((456399946253027/18446744073709551616), (8251374531249/73786976294838206464)), (190921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228130313770257/1152921504606846976), (4639149068951/4611686018427387904)), (53745/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596284522517475/1152921504606846976), (9272674848089/1152921504606846976)), (107611/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196584795536615/144115188075855872), (2026815893267/36028797018963968)), (11787/9007199254740992), by norm_num⟩
  | 4 => ⟨((1494628881025451/36028797018963968), (6074119874583/18014398509481984)), (141717/18014398509481984), by norm_num⟩
  | 3 => ⟨((746485792923025/4503599627370496), (7581574221043/4503599627370496)), (177625/4503599627370496), by norm_num⟩
  | 2 => ⟨((558824942024599/1125899906842624), (472809808677/70368744177664)), (356687/2251799813685248), by norm_num⟩
  | 1 => ⟨((556735422161875/562949953421312), (22611758156283/1125899906842624)), (538629/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100827488879271/1125899906842624), (22445456855857/562949953421312)), (68231/70368744177664), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100827488879271/1125899906842624), (22445456855857/562949953421312)), (260280609399294831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((67157721946785/70368744177664), (87782495609833/1125899906842624)), (1110913/562949953421312), by norm_num⟩
  | 2 => ⟨((509323736713717/562949953421312), (167553720074239/1125899906842624)), (1146835/281474976710656), by norm_num⟩
  | 3 => ⟨((896676889192153/1125899906842624), (151592670520443/562949953421312)), (4833031/562949953421312), by norm_num⟩
  | 4 => ⟨((158119760082895/281474976710656), (241459553199167/562949953421312)), (41204171/2251799813685248), by norm_num⟩
  | 5 => ⟨((296329846232963/2251799813685248), (271281852957197/562949953421312)), (81639685/2251799813685248), by norm_num⟩
  | 6 => ⟨((-241959812659907/1125899906842624), (571197558745947/4503599627370496)), (100170307/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-347069183/8388608)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1545544541/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-466884413262221/4503599627370496), (-839156694784615/4503599627370496)), (85076005/4503599627370496), by norm_num⟩
  | 1 => ⟨((398895535/2147483648), (358478297/1073741824)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((-178681213/1073741824), (-1284613767/4294967296)), (135/4294967296), by norm_num⟩
  | 3 => ⟨((213435837/2147483648), (767239627/4294967296)), (41/2147483648), by norm_num⟩
  | 4 => ⟨((-191212841/4294967296), (-1374708867/17179869184)), (149/17179869184), by norm_num⟩
  | 5 => ⟨((274085935/17179869184), (246314763/8589934592)), (109/34359738368), by norm_num⟩
  | 6 => ⟨((-654794759/137438953472), (-588449079/68719476736)), (33/34359738368), by norm_num⟩
  | 7 => ⟨((335209917/274877906944), (602490977/274877906944)), (137/549755813888), by norm_num⟩
  | 8 => ⟨((-600615543/2199023255552), (-1079518913/2199023255552)), (125/2199023255552), by norm_num⟩
  | 9 => ⟨((478292705/8796093022208), (429830719/4398046511104)), (101/8796093022208), by norm_num⟩
  | 10 => ⟨((-685588387/70368744177664), (-616122609/35184372088832)), (147/70368744177664), by norm_num⟩
  | 11 => ⟨((223347179/140737488355328), (401434007/140737488355328)), (97/281474976710656), by norm_num⟩
  | 12 => ⟨((-533579231/2251799813685248), (-959030911/2251799813685248)), (59/1125899906842624), by norm_num⟩
  | 13 => ⟨((294167889/9007199254740992), (1057447825/18014398509481984)), (33/4503599627370496), by norm_num⟩
  | 14 => ⟨((-150593743/36028797018963968), (-1082681231/144115188075855872)), (137/144115188075855872), by norm_num⟩
  | 15 => ⟨((575632565/1152921504606846976), (258653913/288230376151711744)), (133/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-257848775/4611686018427387904), (-231722799/2305843009213693952)), (121/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-2707503749441/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779579787806525/633825300114114700748351602688), (-1603494261285/316912650057057350374175801344)), (23129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472663457962607/9903520314283042199192993792), (-1803679335645/19807040628566084398385987584)), (52051/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472621347323797/618970019642690137449562112), (-479026625933/309485009821345068724781056)), (55315/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886075529980689/77371252455336267181195264), (-1915765879047/77371252455336267181195264)), (55329/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387613289968849/2417851639229258349412352), (-3591337264715/9671406556917033397649408)), (51885/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259575336786475/604462909807314587353088), (-3141696425615/604462909807314587353088)), (45413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889069204695219/75557863725914323419136), (-5103899954495/75557863725914323419136)), (36911/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298496315577697/4722366482869645213696), (-3826737985763/4722366482869645213696)), (27695/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622762163589941/590295810358705651712), (-2629918098573/295147905179352825856)), (38099/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825114725665655/73786976294838206464), (-6571902988453/73786976294838206464)), (11913/9223372036854775808), by norm_num⟩
  | 7 => ⟨((228062328672819/1152921504606846976), (-7389414888857/9223372036854775808)), (53647/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595742903408281/1152921504606846976), (-7384446246379/1152921504606846976)), (53695/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196113420360059/144115188075855872), (-6455802565855/144115188075855872)), (94075/144115188075855872), by norm_num⟩
  | 4 => ⟨((186740861782275/4503599627370496), (-4836266307399/18014398509481984)), (70665/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492102969422247/9007199254740992), (-12071126402785/9007199254740992)), (44261/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116794536239625/2251799813685248), (-12041837995215/2251799813685248)), (11101/140737488355328), by norm_num⟩
  | 1 => ⟨((1112220882281325/1125899906842624), (-17989608457279/1125899906842624)), (133929/562949953421312), by norm_num⟩
  | 0 => ⟨((68653695730241/70368744177664), (-17843529791859/562949953421312)), (541463/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((68653695730241/70368744177664), (-17843529791859/562949953421312)), (2065517429832076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1070555997413719/1125899906842624), (-69634567414811/1125899906842624)), (1090859/1125899906842624), by norm_num⟩
  | 2 => ⟨((1013625779417491/1125899906842624), (-132423323459171/1125899906842624)), (2209411/1125899906842624), by norm_num⟩
  | 3 => ⟨((448486263284195/562949953421312), (-59609070770231/281474976710656)), (4497903/1125899906842624), by norm_num⟩
  | 4 => ⟨((1328195957357953/2251799813685248), (-189955424954633/562949953421312)), (18143563/2251799813685248), by norm_num⟩
  | 5 => ⟨((131758546920367/562949953421312), (-896342653444135/2251799813685248)), (33647823/2251799813685248), by norm_num⟩
  | 6 => ⟨((-466884413262221/4503599627370496), (-839156694784615/4503599627370496)), (85076005/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1545544541/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1678512579/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((408130748828223/2251799813685248), (100702771598875/2251799813685248)), (2010697/140737488355328), by norm_num⟩
  | 1 => ⟨((-94674321/268435456), (-373761263/4294967296)), (61/2147483648), by norm_num⟩
  | 2 => ⟨((1473821777/4294967296), (181826459/2147483648)), (121/4294967296), by norm_num⟩
  | 3 => ⟨((-477987459/2147483648), (-235878635/4294967296)), (5/268435456), by norm_num⟩
  | 4 => ⟨((116265081/1073741824), (229499315/8589934592)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((-1447944967/34359738368), (-357268037/34359738368)), (125/34359738368), by norm_num⟩
  | 6 => ⟨((939190269/68719476736), (115868583/34359738368)), (83/68719476736), by norm_num⟩
  | 7 => ⟨((-522165679/137438953472), (-128839915/137438953472)), (47/137438953472), by norm_num⟩
  | 8 => ⟨((508043747/549755813888), (125355449/549755813888)), (93/1099511627776), by norm_num⟩
  | 9 => ⟨((-27461319/137438953472), (-108413529/2199023255552)), (41/2199023255552), by norm_num⟩
  | 10 => ⟨((1367993839/35184372088832), (168770389/17592186044416)), (65/17592186044416), by norm_num⟩
  | 11 => ⟨((-967997489/140737488355328), (-59711275/35184372088832)), (47/70368744177664), by norm_num⟩
  | 12 => ⟨((627878713/562949953421312), (309847403/1125899906842624)), (31/281474976710656), by norm_num⟩
  | 13 => ⟨((-751874191/4503599627370496), (-185518525/4503599627370496)), (75/4503599627370496), by norm_num⟩
  | 14 => ⟨((1672090993/72057594037927936), (412574149/72057594037927936)), (169/72057594037927936), by norm_num⟩
  | 15 => ⟨((-867663689/288230376151711744), (-214088593/288230376151711744)), (89/288230376151711744), by norm_num⟩
  | 16 => ⟨((1688395579/4611686018427387904), (208298583/2305843009213693952)), (175/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (157557031553/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222422511593321/79228162514264337593543950336), (186582499481/316912650057057350374175801344)), (92237/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118151845125603/2475880078570760549798248448), (209874293169/19807040628566084398385987584)), (103769/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945123749871627/1237940039285380274899124224), (222953259231/1237940039285380274899124224)), (55129/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885956832383933/77371252455336267181195264), (445820644433/154742504910672534362390528)), (27565/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775115563449595/4835703278458516698824704), (417865636261/9671406556917033397649408)), (103373/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78711348917637/37778931862957161709568), (91385310001/151115727451828646838272)), (45227/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888755337612897/75557863725914323419136), (296916793059/37778931862957161709568)), (73497/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298261775117243/4722366482869645213696), (445225682383/4722366482869645213696)), (110251/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622441066649279/590295810358705651712), (4780800533/4611686018427387904)), (37901/147573952589676412928), by norm_num⟩
  | 8 => ⟨((114044715432133/4611686018427387904), (764563999881/73786976294838206464)), (94759/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456013078710635/2305843009213693952), (859634178319/9223372036854775808)), (213225/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797650088449295/576460752303423488), (13422019061/18014398509481984)), (833/4503599627370496), by norm_num⟩
  | 5 => ⟨((1195730064961847/144115188075855872), (375465299281/72057594037927936)), (93309/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493359906179889/36028797018963968), (562496241055/18014398509481984)), (139989/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491408278099831/9007199254740992), (701894022809/4503599627370496)), (350063/9007199254740992), by norm_num⟩
  | 2 => ⟨((558060420331663/1125899906842624), (2800232082605/4503599627370496)), (700397/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222525168030741/2251799813685248), (2091017916311/1125899906842624)), (1051281/2251799813685248), by norm_num⟩
  | 0 => ⟨((2193500106976253/2251799813685248), (4145554088731/1125899906842624)), (1052663/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193500106976253/2251799813685248), (4145554088731/1125899906842624)), (4015590672019576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1068339633831799/1125899906842624), (8076449142453/1125899906842624)), (2058571/1125899906842624), by norm_num⟩
  | 2 => ⟨((2027328250493653/2251799813685248), (7663550433809/562949953421312)), (61503/17592186044416), by norm_num⟩
  | 3 => ⟨((228101990360809/281474976710656), (55196850800399/2251799813685248)), (7194791/1125899906842624), by norm_num⟩
  | 4 => ⟨((738721630551381/1125899906842624), (22365241266477/562949953421312)), (24027535/2251799813685248), by norm_num⟩
  | 5 => ⟨((965820901258603/2251799813685248), (58696825164073/1125899906842624)), (66877787/4503599627370496), by norm_num⟩
  | 6 => ⟨((408130748828223/2251799813685248), (100702771598875/2251799813685248)), (2010697/140737488355328), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1678512579/33554432)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1793694733/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1496748887114821/9007199254740992), (18422474880137/2251799813685248)), (243995663/9007199254740992), by norm_num⟩
  | 1 => ⟨((371027209/1073741824), (-18266897/1073741824)), (61/1073741824), by norm_num⟩
  | 2 => ⟨((-1543058783/4294967296), (75969889/4294967296)), (1/16777216), by norm_num⟩
  | 3 => ⟨((1069566845/4294967296), (-26329157/2147483648)), (179/4294967296), by norm_num⟩
  | 4 => ⟨((-1112050865/8589934592), (54749943/8589934592)), (47/2147483648), by norm_num⟩
  | 5 => ⟨((462488953/8589934592), (-91079445/34359738368)), (79/8589934592), by norm_num⟩
  | 6 => ⟨((-1282291655/68719476736), (63131461/68719476736)), (111/34359738368), by norm_num⟩
  | 7 => ⟨((1523686021/274877906944), (-9377013/34359738368)), (133/137438953472), by norm_num⟩
  | 8 => ⟨((-396052001/274877906944), (77995801/1099511627776)), (279/1099511627776), by norm_num⟩
  | 9 => ⟨((732059541/2199023255552), (-36041713/2199023255552)), (65/1099511627776), by norm_num⟩
  | 10 => ⟨((-1217820017/17592186044416), (14989327/4398046511104)), (219/17592186044416), by norm_num⟩
  | 11 => ⟨((920867467/70368744177664), (-90674703/140737488355328)), (167/70368744177664), by norm_num⟩
  | 12 => ⟨((-1276593377/562949953421312), (62850915/562949953421312)), (117/281474976710656), by norm_num⟩
  | 13 => ⟨((51050025/140737488355328), (-80427571/4503599627370496)), (151/2251799813685248), by norm_num⟩
  | 14 => ⟨((-485282481/9007199254740992), (95568247/36028797018963968)), (181/18014398509481984), by norm_num⟩
  | 15 => ⟨((1076390987/144115188075855872), (-52994289/144115188075855872)), (203/144115188075855872), by norm_num⟩
  | 16 => ⟨((-1119146067/1152921504606846976), (55099263/1152921504606846976)), (213/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (4028195052447/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779190358847861/633825300114114700748351602688), (298085687281/39614081257132168796771975168)), (92669/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945107704887297/19807040628566084398385987584), (2682330395873/19807040628566084398385987584)), (104283/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945009576792547/1237940039285380274899124224), (1424726257677/618970019642690137449562112)), (27709/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221460545100107/19342813113834066795298816), (5697726929509/154742504910672534362390528)), (110875/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550015137333535/9671406556917033397649408), (2670183635745/4835703278458516698824704)), (103987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259191575362417/604462909807314587353088), (4671569645851/604462909807314587353088)), (91031/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472111167812205/18889465931478580854784), (7588953723749/75557863725914323419136)), (74001/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324506777576743/1180591620717411303424), (5689661729615/4722366482869645213696)), (111071/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811057849712087/295147905179352825856), (7819947874523/590295810358705651712)), (152833/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824304687719801/73786976294838206464), (1221241175535/9223372036854775808)), (191209/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823584649089663/9223372036854775808), (1373036026869/1152921504606846976)), (53835/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594825570037809/1152921504606846976), (5487842719215/576460752303423488)), (53907/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195306990280959/144115188075855872), (9594046896813/144115188075855872)), (188999/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492709744445455/36028797018963968), (14371715320623/36028797018963968)), (142073/18014398509481984), by norm_num⟩
  | 3 => ⟨((372642112137011/2251799813685248), (4482693638241/2251799813685248)), (356319/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115240489061455/2251799813685248), (8939986926049/1125899906842624)), (358027/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109841342162139/1125899906842624), (26692973332231/1125899906842624)), (270659/562949953421312), by norm_num⟩
  | 0 => ⟨((1093508248693977/1125899906842624), (52878093649105/1125899906842624)), (1099807/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093508248693977/1125899906842624), (52878093649105/1125899906842624)), (4195430759910201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1059565055404659/1125899906842624), (51356813540079/562949953421312)), (1119819/562949953421312), by norm_num⟩
  | 2 => ⟨((493884052520029/562949953421312), (96662029463347/562949953421312)), (2312003/562949953421312), by norm_num⟩
  | 3 => ⟨((833388147447187/1125899906842624), (339211928492263/1125899906842624)), (2425339/281474976710656), by norm_num⟩
  | 4 => ⟨((1029347401757999/2251799813685248), (1004335106380533/2251799813685248)), (40414999/2251799813685248), by norm_num⟩
  | 5 => ⟨((45179031713569/4503599627370496), (918207494257879/2251799813685248)), (146001039/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1496748887114821/9007199254740992), (18422474880137/2251799813685248)), (243995663/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1793694733/33554432)), (1/16777216), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile035Terms0
