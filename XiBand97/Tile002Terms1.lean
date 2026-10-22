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
namespace Reinmann.XiBand97.Tile002Terms1
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
  | 0 => ⟨((69/80), (9561/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9561/640))
  have he : value ((69/80), (9561/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/8388608), (-34418957/1048576)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((218688894757991/9007199254740992), (-668011763338689/4503599627370496)), (51490571/2251799813685248), by norm_num⟩
  | 1 => ⟨((-114562181/2147483648), (699888165/2147483648)), (109/2147483648), by norm_num⟩
  | 2 => ⟨((31464855/536870912), (-768905739/2147483648)), (121/2147483648), by norm_num⟩
  | 3 => ⟨((-184360941/4294967296), (1126305725/4294967296)), (179/4294967296), by norm_num⟩
  | 4 => ⟨((202541195/8589934592), (-1237373311/8589934592)), (199/8589934592), by norm_num⟩
  | 5 => ⟨((-178011397/17179869184), (271878705/4294967296)), (177/17179869184), by norm_num⟩
  | 6 => ⟨((260754011/68719476736), (-199126191/8589934592)), (131/34359738368), by norm_num⟩
  | 7 => ⟨((-163695749/137438953472), (500028527/68719476736)), (83/68719476736), by norm_num⟩
  | 8 => ⟨((179838161/549755813888), (-1098674969/549755813888)), (185/549755813888), by norm_num⟩
  | 9 => ⟨((-175619923/2199023255552), (1072904731/2199023255552)), (183/2199023255552), by norm_num⟩
  | 10 => ⟨((38587641/2199023255552), (-471482529/4398046511104)), (163/8796093022208), by norm_num⟩
  | 11 => ⟨((-61662337/17592186044416), (188355091/8796093022208)), (263/70368744177664), by norm_num⟩
  | 12 => ⟨((180648003/281474976710656), (-551811247/140737488355328)), (195/281474976710656), by norm_num⟩
  | 13 => ⟨((-122130533/1125899906842624), (746125067/1125899906842624)), (133/1125899906842624), by norm_num⟩
  | 14 => ⟨((76670917/4503599627370496), (-936802477/9007199254740992)), (169/9007199254740992), by norm_num⟩
  | 15 => ⟨((-179694105/72057594037927936), (548897447/36028797018963968)), (25/9007199254740992), by norm_num⟩
  | 16 => ⟨((24676769/72057594037927936), (-1206050961/576460752303423488)), (111/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-114674500963/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111190208450653/39614081257132168796771975168), (-1086012128565/316912650057057350374175801344)), (46207/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945025294671241/19807040628566084398385987584), (-2443118216615/39614081257132168796771975168)), (25995/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944922388233639/1237940039285380274899124224), (-2595310968063/2475880078570760549798248448)), (55247/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885755410442029/77371252455336267181195264), (-2594746203517/154742504910672534362390528)), (6907/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387463333178483/2417851639229258349412352), (-151998415355/604462909807314587353088)), (12953/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314762721210069/151115727451828646838272), (-1063689027403/302231454903657293676544)), (45345/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118013607124643/4722366482869645213696), (-3455865128581/75557863725914323419136)), (147407/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648929173986865/2361183241434822606848), (-2590915502015/4722366482869645213696)), (55293/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((12670984487959/4611686018427387904), (-13909810615/2305843009213693952)), (152107/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456005280667243/18446744073709551616), (-556093070525/9223372036854775808)), (190209/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823270501473249/9223372036854775808), (-1250386637435/2305843009213693952)), (107045/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594517492221981/1152921504606846976), (-624679425891/144115188075855872)), (107111/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195044238305585/144115188075855872), (-4368134675179/144115188075855872)), (187591/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492329217697835/36028797018963968), (-3271484359277/18014398509481984)), (140841/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490116522516887/9007199254740992), (-510160848959/562949953421312)), (352619/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114824022319097/2251799813685248), (-16276818945971/4503599627370496)), (706793/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218609606511703/2251799813685248), (-24294700557279/2251799813685248)), (266021/562949953421312), by norm_num⟩
  | 0 => ⟨((546392449191379/562949953421312), (-24054521530903/1125899906842624)), (535949/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546392449191379/562949953421312), (-24054521530903/1125899906842624)), (2044483186961936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2120259903874693/2251799813685248), (-11673514540253/281474976710656)), (4253089/2251799813685248), by norm_num⟩
  | 2 => ⟨((249066363073233/281474976710656), (-175865614103519/2251799813685248)), (8362061/2251799813685248), by norm_num⟩
  | 3 => ⟨((1749378726992103/2251799813685248), (-311233413401653/2251799813685248)), (8052343/1125899906842624), by norm_num⟩
  | 4 => ⟨((1316040473413545/2251799813685248), (-483582163232291/2251799813685248)), (921083/70368744177664), by norm_num⟩
  | 5 => ⟨((332647424953453/1125899906842624), (-141312228371009/562949953421312)), (23555939/1125899906842624), by norm_num⟩
  | 6 => ⟨((218688894757991/9007199254740992), (-668011763338689/4503599627370496)), (51490571/2251799813685248), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-34418957/1048576)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66638419/33554432), (-1154220875/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1220598525984063/9007199254740992), (-97899083559313/4503599627370496)), (208493865/9007199254740992), by norm_num⟩
  | 1 => ⟨((670083039/2147483648), (107489095/2147483648)), (231/4294967296), by norm_num⟩
  | 2 => ⟨((-1542923217/4294967296), (-61875697/1073741824)), (67/1073741824), by norm_num⟩
  | 3 => ⟨((1184237333/4294967296), (94982705/2147483648)), (13/268435456), by norm_num⟩
  | 4 => ⟨((-1363403615/8589934592), (-218705761/8589934592)), (121/4294967296), by norm_num⟩
  | 5 => ⟨((78483821/1073741824), (100717725/8589934592)), (225/17179869184), by norm_num⟩
  | 6 => ⟨((-240954235/8589934592), (-154607421/34359738368)), (175/34359738368), by norm_num⟩
  | 7 => ⟨((634077291/68719476736), (101713355/68719476736)), (29/17179869184), by norm_num⟩
  | 8 => ⟨((-730008459/274877906944), (-234203655/549755813888)), (269/549755813888), by norm_num⟩
  | 9 => ⟨((373534799/549755813888), (14979829/137438953472)), (139/1099511627776), by norm_num⟩
  | 10 => ⟨((-43004783/274877906944), (-110375459/4398046511104)), (129/4398046511104), by norm_num⟩
  | 11 => ⟨((1152258005/35184372088832), (92417777/17592186044416)), (109/17592186044416), by norm_num⟩
  | 12 => ⟨((-442195351/70368744177664), (-283733061/281474976710656)), (337/281474976710656), by norm_num⟩
  | 13 => ⟨((626579953/562949953421312), (100510695/562949953421312)), (241/1125899906842624), by norm_num⟩
  | 14 => ⟨((-1648861325/9007199254740992), (-264496489/9007199254740992)), (5/140737488355328), by norm_num⟩
  | 15 => ⟨((1012438269/36028797018963968), (81203423/18014398509481984)), (99/18014398509481984), by norm_num⟩
  | 16 => ⟨((-1165612633/288230376151711744), (-186977791/288230376151711744)), (115/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-3885086255801/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444723606033169/158456325028528675187087900672), (-574808774731/79228162514264337593543950336)), (23163/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889882593470873/39614081257132168796771975168), (-1293086998911/9903520314283042199192993792)), (13033/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944832833914859/1237940039285380274899124224), (-5494502791255/2475880078570760549798248448)), (55407/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885665511545739/77371252455336267181195264), (-5493246168775/154742504910672534362390528)), (27713/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774842020261395/4835703278458516698824704), (-5148583226683/9671406556917033397649408)), (103963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314725505734245/151115727451828646838272), (-1125918846075/151115727451828646838272)), (91009/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943987221724071/37778931862957161709568), (-3657984869471/37778931862957161709568)), (36991/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162209337183607/590295810358705651712), (-1371196909861/1180591620717411303424)), (111039/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621631551009829/590295810358705651712), (-7538025270249/590295810358705651712)), (76393/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455925032750545/18446744073709551616), (-4708597906923/36893488147419103232)), (23893/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822905387289267/9223372036854775808), (-5293504974811/4611686018427387904)), (215259/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594147388728683/1152921504606846976), (-2644460700849/288230376151711744)), (13471/72057594037927936), by norm_num⟩
  | 5 => ⟨((597357398494449/72057594037927936), (-9245302216997/144115188075855872)), (188907/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491823884705683/36028797018963968), (-13847339899271/36028797018963968)), (141993/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489465375547705/9007199254740992), (-2159139666539/1125899906842624)), (356079/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114143791156265/2251799813685248), (-4304765795059/562949953421312)), (357727/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108212224266249/1125899906842624), (-6423393270969/281474976710656)), (540719/1125899906842624), by norm_num⟩
  | 0 => ⟨((272578418389281/281474976710656), (-12711937649411/281474976710656)), (549005/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((272578418389281/281474976710656), (-12711937649411/281474976710656)), (2094287874461936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1053555831913391/1125899906842624), (-98481219172857/1125899906842624)), (556447/281474976710656), by norm_num⟩
  | 2 => ⟨((244311535541929/281474976710656), (-46076681489595/281474976710656)), (2277459/562949953421312), by norm_num⟩
  | 3 => ⟨((818048787064095/1125899906842624), (-319945024995131/1125899906842624)), (9398311/1125899906842624), by norm_num⟩
  | 4 => ⟨((1006908332708715/2251799813685248), (-464927011777509/1125899906842624)), (18998527/1125899906842624), by norm_num⟩
  | 5 => ⟨((132548092818741/4503599627370496), (-1663163410583965/4503599627370496)), (130724347/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1220598525984063/9007199254740992), (-97899083559313/4503599627370496)), (208493865/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1154220875/33554432)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-34698381/16777216), (-150249647/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-343022298758273/9007199254740992), (1085748379697461/9007199254740992)), (197258323/9007199254740992), by norm_num⟩
  | 1 => ⟨((196106803/2147483648), (-620725371/2147483648)), (57/1073741824), by norm_num⟩
  | 2 => ⟨((-58780447/536870912), (1488434433/4294967296)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((375864949/4294967296), (-1189703297/4294967296)), (223/4294967296), by norm_num⟩
  | 4 => ⟨((-56330299/1073741824), (356597989/2147483648)), (135/4294967296), by norm_num⟩
  | 5 => ⟨((432237305/17179869184), (-1368135411/17179869184)), (131/8589934592), by norm_num⟩
  | 6 => ⟨((-345486597/34359738368), (546774239/17179869184)), (211/34359738368), by norm_num⟩
  | 7 => ⟨((473394673/137438953472), (-1498408415/137438953472)), (291/137438953472), by norm_num⟩
  | 8 => ⟨((-4434183/4294967296), (449128307/137438953472)), (11/17179869184), by norm_num⟩
  | 9 => ⟨((75610357/274877906944), (-29915629/34359738368)), (189/1099511627776), by norm_num⟩
  | 10 => ⟨((-72522287/1099511627776), (918202181/4398046511104)), (183/4398046511104), by norm_num⟩
  | 11 => ⟨((505893379/35184372088832), (-1601274669/35184372088832)), (161/17592186044416), by norm_num⟩
  | 12 => ⟨((-404359781/140737488355328), (4999595/549755813888)), (65/35184372088832), by norm_num⟩
  | 13 => ⟨((298342279/562949953421312), (-472162667/281474976710656)), (97/281474976710656), by norm_num⟩
  | 14 => ⟨((-408796309/4503599627370496), (1293939003/4503599627370496)), (67/1125899906842624), by norm_num⟩
  | 15 => ⟨((261400197/18014398509481984), (-827394725/18014398509481984)), (173/18014398509481984), by norm_num⟩
  | 16 => ⟨((-78351287/36028797018963968), (496001475/72057594037927936)), (209/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1222373700411/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889387262091091/316912650057057350374175801344), (2893262169129/633825300114114700748351602688)), (92485/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944874059883061/19807040628566084398385987584), (203395277209/2475880078570760549798248448)), (813/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((472380830836827/618970019642690137449562112), (1728494736985/1237940039285380274899124224)), (110589/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771189278790951/154742504910672534362390528), (3456168138369/154742504910672534362390528)), (110613/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387387948141255/2417851639229258349412352), (3239285161767/9671406556917033397649408)), (103725/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258786942882877/604462909807314587353088), (2833502274733/604462909807314587353088)), (90785/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887788631682795/75557863725914323419136), (2301403111771/37778931862957161709568)), (36893/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648768190960333/2361183241434822606848), (3450674546813/4722366482869645213696)), (55361/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202680382600271/73786976294838206464), (2371177228103/295147905179352825856)), (152309/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227933381982403/9223372036854775808), (2962230038881/36893488147419103232)), (190487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911323331141079/4611686018427387904), (6660231033341/9223372036854775808)), (107219/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796946506172529/576460752303423488), (207945365021/36028797018963968)), (53653/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194497100184377/144115188075855872), (5815748727539/144115188075855872)), (187983/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491507080404087/36028797018963968), (8710193298039/36028797018963968)), (282367/36028797018963968), by norm_num⟩
  | 3 => ⟨((93067897653275/562949953421312), (5432134578677/4503599627370496)), (353649/9007199254740992), by norm_num⟩
  | 2 => ⟨((278447539501715/562949953421312), (5414559889203/1125899906842624)), (709369/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215489690634017/2251799813685248), (32312027426315/2251799813685248)), (1069247/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089628928862849/1125899906842624), (63925215151889/2251799813685248)), (2159339/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089628928862849/1125899906842624), (63925215151889/2251799813685248)), (8237224587447356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2107238107263757/2251799813685248), (123731715918893/2251799813685248)), (4302153/2251799813685248), by norm_num⟩
  | 2 => ⟨((1965158215346955/2251799813685248), (115788350845769/1125899906842624)), (4262357/1125899906842624), by norm_num⟩
  | 3 => ⟨((845594492777501/1125899906842624), (404196549840987/2251799813685248)), (16632507/2251799813685248), by norm_num⟩
  | 4 => ⟨((74849719032799/140737488355328), (607134567589905/2251799813685248)), (7738591/562949953421312), by norm_num⟩
  | 5 => ⟨((14788484455011/70368744177664), (1291591951235327/4503599627370496)), (99234883/4503599627370496), by norm_num⟩
  | 6 => ⟨((-343022298758273/9007199254740992), (1085748379697461/9007199254740992)), (197258323/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-150249647/4194304)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17978733/8388608), (-622806761/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((885342639538951/9007199254740992), (576179332212911/9007199254740992)), (6579901/562949953421312), by norm_num⟩
  | 1 => ⟨((-1049038797/4294967296), (-682712485/4294967296)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((325845435/1073741824), (212059599/1073741824)), (81/2147483648), by norm_num⟩
  | 3 => ⟨((-1054291/4194304), (-702597743/4294967296)), (137/4294967296), by norm_num⟩
  | 4 => ⟨((670672567/4294967296), (436472451/4294967296)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((-1301999/16777216), (-216918659/4294967296)), (89/8589934592), by norm_num⟩
  | 6 => ⟨((1104331425/34359738368), (89837103/4294967296)), (75/17179869184), by norm_num⟩
  | 7 => ⟨((-784045857/68719476736), (-63781947/8589934592)), (109/68719476736), by norm_num⟩
  | 8 => ⟨((487070191/137438953472), (633968737/274877906944)), (69/137438953472), by norm_num⟩
  | 9 => ⟨((-1075843517/1099511627776), (-700156947/1099511627776)), (155/1099511627776), by norm_num⟩
  | 10 => ⟨((267337071/1099511627776), (695929861/4398046511104)), (157/4398046511104), by norm_num⟩
  | 11 => ⟨((-966265695/17592186044416), (-628843905/17592186044416)), (9/1099511627776), by norm_num⟩
  | 12 => ⟨((800360017/70368744177664), (16277275/2199023255552)), (121/70368744177664), by norm_num⟩
  | 13 => ⟨((-611944593/281474976710656), (-398252395/281474976710656)), (47/140737488355328), by norm_num⟩
  | 14 => ⟨((868928679/2251799813685248), (565497157/2251799813685248)), (135/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1151576881/18014398509481984), (-374722039/9007199254740992)), (181/18014398509481984), by norm_num⟩
  | 16 => ⟨((357695131/36028797018963968), (465574643/72057594037927936)), (57/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (751523672423/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778662896547751/633825300114114700748351602688), (889288482927/633825300114114700748351602688)), (721/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((1889622791658887/39614081257132168796771975168), (500131281919/19807040628566084398385987584)), (51915/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944695245037679/1237940039285380274899124224), (1062546670115/2475880078570760549798248448)), (55163/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885528407029219/77371252455336267181195264), (531142713741/77371252455336267181195264)), (110333/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387356999553729/2417851639229258349412352), (995615106731/9671406556917033397649408)), (103445/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258679013897019/604462909807314587353088), (217721459185/151115727451828646838272)), (45261/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471903494943169/18889465931478580854784), (707334803135/37778931862957161709568)), (147113/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297406033528571/4722366482869645213696), (530273761569/2361183241434822606848)), (27587/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810632435791421/295147905179352825856), (728757192089/295147905179352825856)), (151749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823245877213827/73786976294838206464), (455196496265/18446744073709551616)), (189717/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822399975384287/9223372036854775808), (2046863243497/9223372036854775808)), (213475/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24900765543625/18014398509481984), (1022481848989/576460752303423488)), (213529/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194286581654461/144115188075855872), (893604285365/72057594037927936)), (93449/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491197280830361/36028797018963968), (2676549328651/36028797018963968)), (140235/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488709540202163/9007199254740992), (1669119262547/4503599627370496)), (350801/9007199254740992), by norm_num⟩
  | 2 => ⟨((556714453699409/1125899906842624), (6654184700167/4503599627370496)), (702245/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107241657074653/1125899906842624), (4962863980723/1125899906842624)), (1054985/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177551720148475/2251799813685248), (19630346982473/2251799813685248)), (2116483/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177551720148475/2251799813685248), (19630346982473/2251799813685248)), (8073741921431731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2105580662447673/2251799813685248), (37966159850451/2251799813685248)), (516287/281474976710656), by norm_num⟩
  | 2 => ⟨((984108016583949/1125899906842624), (17750426019815/562949953421312)), (3931737/1125899906842624), by norm_num⟩
  | 3 => ⟨((859053519705503/1125899906842624), (31029999092667/562949953421312)), (222535/35184372088832), by norm_num⟩
  | 4 => ⟨((326015439686089/562949953421312), (189405326530435/2251799813685248)), (23303529/2251799813685248), by norm_num⟩
  | 5 => ⟨((1478553007051639/4503599627370496), (438753465969249/4503599627370496)), (15455661/1125899906842624), by norm_num⟩
  | 6 => ⟨((885342639538951/9007199254740992), (576179332212911/9007199254740992)), (6579901/562949953421312), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-622806761/16777216)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-579933/262144), (-1285736671/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((803038622050209/9007199254740992), (-571875560022175/9007199254740992)), (1581033/140737488355328), by norm_num⟩
  | 1 => ⟨((-982166957/4294967296), (699439931/4294967296)), (63/2147483648), by norm_num⟩
  | 2 => ⟨((314901063/1073741824), (-56063375/268435456)), (83/2147483648), by norm_num⟩
  | 3 => ⟨((-269235093/1073741824), (191732957/1073741824)), (9/268435456), by norm_num⟩
  | 4 => ⟨((690574379/4294967296), (-491785325/4294967296)), (47/2147483648), by norm_num⟩
  | 5 => ⟨((-177128831/2147483648), (504561781/8589934592)), (49/4294967296), by norm_num⟩
  | 6 => ⟨((302884321/8589934592), (-862783611/34359738368)), (85/17179869184), by norm_num⟩
  | 7 => ⟨((-443933111/34359738368), (79035581/8589934592)), (127/68719476736), by norm_num⟩
  | 8 => ⟨((284666487/68719476736), (-810889051/274877906944)), (165/274877906944), by norm_num⟩
  | 9 => ⟨((-81128347/68719476736), (462197633/549755813888)), (3/17179869184), by norm_num⟩
  | 10 => ⟨((665888325/2199023255552), (-474205409/2199023255552)), (25/549755813888), by norm_num⟩
  | 11 => ⟨((-621079939/8796093022208), (442295585/8796093022208)), (189/17592186044416), by norm_num⟩
  | 12 => ⟨((1062025727/70368744177664), (-378155259/35184372088832)), (41/17592186044416), by norm_num⟩
  | 13 => ⟨((-838166833/281474976710656), (596891747/281474976710656)), (131/281474976710656), by norm_num⟩
  | 14 => ⟨((614244423/1125899906842624), (-13669617/35184372088832)), (195/2251799813685248), by norm_num⟩
  | 15 => ⟨((-210067445/2251799813685248), (598389339/9007199254740992)), (17/1125899906842624), by norm_num⟩
  | 16 => ⟨((269406179/18014398509481984), (-767419175/72057594037927936)), (177/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-403045585493/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889278212799619/316912650057057350374175801344), (-238437569135/158456325028528675187087900672)), (92295/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889503031043989/39614081257132168796771975168), (-1072762366977/39614081257132168796771975168)), (103837/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889263267992393/2475880078570760549798248448), (-1139552855939/2475880078570760549798248448)), (55167/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770929618485567/154742504910672534362390528), (-1139263666143/154742504910672534362390528)), (55171/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387327195131413/2417851639229258349412352), (-133469065509/1208925819614629174706176)), (51727/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258574726571711/604462909807314587353088), (-466988204763/302231454903657293676544)), (90531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943722282819801/37778931862957161709568), (-1517136190469/75557863725914323419136)), (147127/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297279019087059/4722366482869645213696), (-284337211009/1180591620717411303424)), (13795/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621090301703109/590295810358705651712), (-1563037253135/590295810358705651712)), (151767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823027777277911/73786976294838206464), (-976285623919/36893488147419103232)), (94871/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227769345930047/1152921504606846976), (-2194959127721/9223372036854775808)), (106753/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593403979825771/1152921504606846976), (-2192856648911/1152921504606846976)), (53391/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194072410483937/144115188075855872), (-1916386928627/144115188075855872)), (93467/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490876457487281/36028797018963968), (-2869861730453/36028797018963968)), (280531/36028797018963968), by norm_num⟩
  | 3 => ⟨((744154634256345/4503599627370496), (-3579084367771/9007199254740992)), (350893/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226059539959039/4503599627370496), (-1783374924491/1125899906842624)), (702477/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106645779755711/1125899906842624), (-10638784187283/2251799813685248)), (527725/1125899906842624), by norm_num⟩
  | 0 => ⟨((2175190759098729/2251799813685248), (-21032946471773/2251799813685248)), (1058943/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175190759098729/2251799813685248), (-21032946471773/2251799813685248)), (4039546970847701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2100991582323895/2251799813685248), (-20317379246579/1125899906842624)), (4131231/2251799813685248), by norm_num⟩
  | 2 => ⟨((1959550053508815/2251799813685248), (-75826709838979/2251799813685248)), (7858207/2251799813685248), by norm_num⟩
  | 3 => ⟨((1702676542994561/2251799813685248), (-8248192868841/140737488355328)), (14205893/2251799813685248), by norm_num⟩
  | 4 => ⟨((319931974529497/562949953421312), (-199577307851521/2251799813685248)), (2893553/281474976710656), by norm_num⟩
  | 5 => ⟨((177399471935871/562949953421312), (-453689794513099/4503599627370496)), (30414413/2251799813685248), by norm_num⟩
  | 6 => ⟨((803038622050209/9007199254740992), (-571875560022175/9007199254740992)), (1581033/140737488355328), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1285736671/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2386755/1048576), (-165360613/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-285790998432813/18014398509481984), (-456853804896683/4503599627370496)), (311205011/18014398509481984), by norm_num⟩
  | 1 => ⟨((89909891/2147483648), (574905101/2147483648)), (99/2147483648), by norm_num⟩
  | 2 => ⟨((-237277357/4294967296), (-47412735/134217728)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((52182379/1073741824), (1334665875/4294967296)), (233/4294967296), by norm_num⟩
  | 4 => ⟨((-275424579/8589934592), (-220141235/1073741824)), (155/4294967296), by norm_num⟩
  | 5 => ⟨((145372251/8589934592), (929544543/8589934592)), (83/4294967296), by norm_num⟩
  | 6 => ⟨((-255763803/34359738368), (-817707113/17179869184)), (147/17179869184), by norm_num⟩
  | 7 => ⟨((192850097/68719476736), (616564557/34359738368)), (223/68719476736), by norm_num⟩
  | 8 => ⟨((-254471231/274877906944), (-1627149213/274877906944)), (37/34359738368), by norm_num⟩
  | 9 => ⟨((74618241/274877906944), (477126673/274877906944)), (11/34359738368), by norm_num⟩
  | 10 => ⟨((-157537453/2199023255552), (-1007331715/2199023255552)), (47/549755813888), by norm_num⟩
  | 11 => ⟨((151181953/8796093022208), (120836643/1099511627776)), (91/4398046511104), by norm_num⟩
  | 12 => ⟨((-265985227/70368744177664), (-850386209/35184372088832)), (323/70368744177664), by norm_num⟩
  | 13 => ⟨((26998087/35184372088832), (345264301/70368744177664)), (265/281474976710656), by norm_num⟩
  | 14 => ⟨((-162855999/1125899906842624), (-1041339753/1125899906842624)), (101/562949953421312), by norm_num⟩
  | 15 => ⟨((229219369/9007199254740992), (732841415/4503599627370496)), (287/9007199254740992), by norm_num⟩
  | 16 => ⟨((-37807691/9007199254740992), (-483502627/18014398509481984)), (191/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-1124108619793/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222306827068545/79228162514264337593543950336), (-1329881561467/316912650057057350374175801344)), (46231/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944694166598419/19807040628566084398385987584), (-2991635773817/39614081257132168796771975168)), (104037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889141186061559/2475880078570760549798248448), (-3177874529817/2475880078570760549798248448)), (110559/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770807294395897/154742504910672534362390528), (-3177043989763/154742504910672534362390528)), (27645/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549193844589653/9671406556917033397649408), (-2977596540549/9671406556917033397649408)), (103693/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258473900741695/604462909807314587353088), (-2604515053115/604462909807314587353088)), (45377/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943640121231537/37778931862957161709568), (-4230683956395/75557863725914323419136)), (147519/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297155356110457/4722366482869645213696), (-3171567182659/4722366482869645213696)), (55339/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202614947812891/73786976294838206464), (-272409786923/36893488147419103232)), (152245/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911406677934035/36893488147419103232), (-5444675260311/73786976294838206464)), (95199/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821912139977039/9223372036854775808), (-6120422177725/9223372036854775808)), (214327/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796579800895371/576460752303423488), (-6114380063767/1152921504606846976)), (26811/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193856615321331/144115188075855872), (-5343291703319/144115188075855872)), (93929/72057594037927936), by norm_num⟩
  | 4 => ⟨((372637212121321/9007199254740992), (-8001372153139/36028797018963968)), (70537/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487892931885753/9007199254740992), (-9978012389401/9007199254740992)), (44165/1125899906842624), by norm_num⟩
  | 2 => ⟨((2225206502586735/4503599627370496), (-19885062823425/4503599627370496)), (708549/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211961483809013/2251799813685248), (-29650701230443/2251799813685248)), (133451/281474976710656), by norm_num⟩
  | 0 => ⟨((543082715534591/562949953421312), (-29298448096485/1125899906842624)), (1077213/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543082715534591/562949953421312), (-29298448096485/1125899906842624)), (4109241489890670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2094141650468443/2251799813685248), (-56528935321823/1125899906842624)), (2134457/1125899906842624), by norm_num⟩
  | 2 => ⟨((242730678341031/281474976710656), (-210284408400103/2251799813685248)), (2092181/562949953421312), by norm_num⟩
  | 3 => ⟨((103432377354363/140737488355328), (-90669653288521/562949953421312)), (7998305/1125899906842624), by norm_num⟩
  | 4 => ⟨((1157837352645749/2251799813685248), (-66635961058577/281474976710656)), (28665699/2251799813685248), by norm_num⟩
  | 5 => ⟨((469137995822113/2251799813685248), (-274104666939465/1125899906842624)), (5381423/281474976710656), by norm_num⟩
  | 6 => ⟨((-285790998432813/18014398509481984), (-456853804896683/4503599627370496)), (311205011/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-165360613/4194304)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39186431/16777216), (-678734541/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-807608815540075/9007199254740992), (-327235759747947/9007199254740992)), (77436569/4503599627370496), by norm_num⟩
  | 1 => ⟨((1042864425/4294967296), (422559197/4294967296)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((-44127019/134217728), (-572155759/4294967296)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((637323641/2147483648), (258237753/2147483648)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-862952207/4294967296), (-349660399/4294967296)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((934767159/8589934592), (378759165/8589934592)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((-421899399/8589934592), (-341899611/17179869184)), (43/4294967296), by norm_num⟩
  | 7 => ⟨((652871287/34359738368), (264537517/34359738368)), (67/17179869184), by norm_num⟩
  | 8 => ⟨((-442002055/68719476736), (-179095219/68719476736)), (183/137438953472), by norm_num⟩
  | 9 => ⟨((1063967781/549755813888), (431110083/549755813888)), (111/274877906944), by norm_num⟩
  | 10 => ⟨((-1152511265/2199023255552), (-466987099/2199023255552)), (243/2199023255552), by norm_num⟩
  | 11 => ⟨((567465157/4398046511104), (459863457/8796093022208)), (241/8796093022208), by norm_num⟩
  | 12 => ⟨((-1024482755/35184372088832), (-415111109/35184372088832)), (219/35184372088832), by norm_num⟩
  | 13 => ⟨((853646379/140737488355328), (345889761/140737488355328)), (185/140737488355328), by norm_num⟩
  | 14 => ⟨((-1320981285/1125899906842624), (-535249621/1125899906842624)), (289/1125899906842624), by norm_num⟩
  | 15 => ⟨((476971151/2251799813685248), (193264379/2251799813685248)), (211/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1291661821/36028797018963968), (-65421205/4503599627370496)), (9/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-3590804507597/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778357041003735/633825300114114700748351602688), (-4247699458183/633825300114114700748351602688)), (92619/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889278254903429/39614081257132168796771975168), (-298604256767/2475880078570760549798248448)), (104223/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944511911212479/1237940039285380274899124224), (-158595637983/77371252455336267181195264)), (6923/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885344737528533/77371252455336267181195264), (-2536848571635/77371252455336267181195264)), (110803/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387270726285293/2417851639229258349412352), (-4755142875783/9671406556917033397649408)), (103915/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258376345316751/604462909807314587353088), (-2079651067733/302231454903657293676544)), (90963/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943560404690479/37778931862957161709568), (-3378075931777/37778931862957161709568)), (36971/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297034989843889/4722366482869645213696), (-5064739724667/4722366482869645213696)), (110975/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620752794406255/590295810358705651712), (-6960160347561/590295810358705651712)), (152689/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822602946883865/73786976294838206464), (-2173604368739/18446744073709551616)), (95505/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910836394598681/4611686018427387904), (-1221658958639/1152921504606846976)), (53773/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99557309820163/72057594037927936), (-4881671026735/576460752303423488)), (215349/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193640605160135/144115188075855872), (-2132940217877/36028797018963968)), (188719/144115188075855872), by norm_num⟩
  | 4 => ⟨((186277183115819/4503599627370496), (-12775332954369/36028797018963968)), (141829/18014398509481984), by norm_num⟩
  | 3 => ⟨((743732930710883/4503599627370496), (-124454439385/70368744177664)), (177793/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112157026153165/2251799813685248), (-15871754760181/2251799813685248)), (357111/2251799813685248), by norm_num⟩
  | 1 => ⟨((138157986303681/140737488355328), (-11830945506029/562949953421312)), (539487/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084543902304355/1125899906842624), (-23371288508121/562949953421312)), (1094321/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084543902304355/1125899906842624), (-23371288508121/562949953421312)), (4174503330710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042766413234587/1125899906842624), (-45025651545811/562949953421312)), (1099557/562949953421312), by norm_num⟩
  | 2 => ⟨((1917137658192349/2251799813685248), (-20850537814521/140737488355328)), (8850505/2251799813685248), by norm_num⟩
  | 3 => ⟨((1582788166801851/2251799813685248), (-568055486919857/2251799813685248)), (17692729/2251799813685248), by norm_num⟩
  | 4 => ⟨((484619310181113/1125899906842624), (-399285716838277/1125899906842624)), (8449751/562949953421312), by norm_num⟩
  | 5 => ⟨((267969796146023/4503599627370496), (-687455669845381/2251799813685248)), (6633607/281474976710656), by norm_num⟩
  | 6 => ⟨((-807608815540075/9007199254740992), (-327235759747947/9007199254740992)), (77436569/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-678734541/16777216)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile002Terms1
