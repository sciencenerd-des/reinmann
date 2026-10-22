/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile047Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨47,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37201/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37201/1280))
  have he : value ((69/80), (37201/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-20060163/33554432), (-5407667549/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((84142619920391/562949953421312), (-1191876688520603/2251799813685248)), (22118897/2251799813685248), by norm_num⟩
  | 1 => ⟨((-222485427/2147483648), (6302993517/17179869184)), (119/17179869184), by norm_num⟩
  | 2 => ⟨((308430293/8589934592), (-2184451093/17179869184)), (85/34359738368), by norm_num⟩
  | 3 => ⟨((-1140200469/137438953472), (4037722977/137438953472)), (81/137438953472), by norm_num⟩
  | 4 => ⟨((1580653481/1099511627776), (-5597472595/1099511627776)), (57/549755813888), by norm_num⟩
  | 5 => ⟨((-876500403/4398046511104), (1551948939/2199023255552)), (129/8796093022208), by norm_num⟩
  | 6 => ⟨((1620116755/70368744177664), (-5737221501/70368744177664)), (121/70368744177664), by norm_num⟩
  | 7 => ⟨((-160425623/70368744177664), (2272422233/281474976710656)), (49/281474976710656), by norm_num⟩
  | 8 => ⟨((444794273/2251799813685248), (-196890383/281474976710656)), (69/4503599627370496), by norm_num⟩
  | 9 => ⟨((-1096205853/72057594037927936), (3881927505/72057594037927936)), (87/72057594037927936), by norm_num⟩
  | 10 => ⟨((607865597/576460752303423488), (-4305195369/1152921504606846976)), (49/576460752303423488), by norm_num⟩
  | 11 => ⟨((-306429327/4611686018427387904), (16955307/72057594037927936)), (101/18446744073709551616), by norm_num⟩
  | 12 => ⟨((4425013/1152921504606846976), (-2005763967/147573952589676412928)), (95/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-483199651/2361183241434822606848), (1711125709/2361183241434822606848)), (83/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((1531101603/151115727451828646838272), (-5421997535/151115727451828646838272)), (67/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((-1132030677/2417851639229258349412352), (250549487/151115727451828646838272)), (101/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((12260373/604462909807314587353088), (-347335341/4835703278458516698824704)), (71/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-421907946869/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781046288697927/633825300114114700748351602688), (-2002092175653/633825300114114700748351602688)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892303677100401/39614081257132168796771975168), (-563057390271/9903520314283042199192993792)), (3249/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892238405491809/2475880078570760549798248448), (-149552971141/154742504910672534362390528)), (6905/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773904138555451/154742504910672534362390528), (-1196341429639/77371252455336267181195264)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776048368599811/4835703278458516698824704), (-2242965200227/9671406556917033397649408)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261013532913121/604462909807314587353088), (-981209779903/302231454903657293676544)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945703198360311/37778931862957161709568), (-199287728523/4722366482869645213696)), (9211/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300249317131273/4722366482869645213696), (-2391165608687/4722366482869645213696)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((406293178694023/147573952589676412928), (-3287386079945/590295810358705651712)), (297/9223372036854775808), by norm_num⟩
  | 8 => ⟨((228516021813779/9223372036854775808), (-4108532582157/73786976294838206464)), (23769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456972278668231/2305843009213693952), (-2310568258629/4611686018427387904)), (26751/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599133829921559/1152921504606846976), (-577491631325/144115188075855872)), (13383/576460752303423488), by norm_num⟩
  | 5 => ⟨((299770243344849/36028797018963968), (-4041087286561/144115188075855872)), (23437/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498379198300659/36028797018963968), (-6058922083919/36028797018963968)), (17595/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497670032120821/9007199254740992), (-3784455411019/4503599627370496)), (22023/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122364077482055/2251799813685248), (-3780897775897/1125899906842624)), (44135/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120581231886719/1125899906842624), (-5662448053443/562949953421312)), (8303/140737488355328), by norm_num⟩
  | 0 => ⟨((557601516546673/562949953421312), (-22578549384323/1125899906842624)), (133737/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557601516546673/562949953421312), (-22578549384323/1125899906842624)), (510166172507857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1104155002210215/1125899906842624), (-44728073256275/1125899906842624)), (270297/1125899906842624), by norm_num⟩
  | 2 => ⟨((1081053174417531/1125899906842624), (-43864224097537/562949953421312)), (275815/562949953421312), by norm_num⟩
  | 3 => ⟨((515578551094855/562949953421312), (-5264628589075/35184372088832)), (1145281/1125899906842624), by norm_num⟩
  | 4 => ⟨((229794730727269/281474976710656), (-308583546485333/1125899906842624)), (305069/140737488355328), by norm_num⟩
  | 5 => ⟨((166459310148875/281474976710656), (-503852056762801/1125899906842624)), (5322709/1125899906842624), by norm_num⟩
  | 6 => ⟨((84142619920391/562949953421312), (-1191876688520603/2251799813685248)), (22118897/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-5407667549/268435456)), (1/134217728), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-4285475141/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((380235338008761/1125899906842624), (-214364130876069/1125899906842624)), (10208541/1125899906842624), by norm_num⟩
  | 1 => ⟨((-3187036247/8589934592), (898372911/4294967296)), (11/1073741824), by norm_num⟩
  | 2 => ⟨((1750658593/8589934592), (-15421305/134217728)), (99/17179869184), by norm_num⟩
  | 3 => ⟨((-5128786783/68719476736), (2891440671/68719476736)), (147/68719476736), by norm_num⟩
  | 4 => ⟨((2817274093/137438953472), (-1588286127/137438953472)), (83/137438953472), by norm_num⟩
  | 5 => ⟨((-4952147103/1099511627776), (2791857051/1099511627776)), (149/1099511627776), by norm_num⟩
  | 6 => ⟨((3626993109/4398046511104), (-63899343/137438953472)), (7/274877906944), by norm_num⟩
  | 7 => ⟨((-4553896229/35184372088832), (2567336355/35184372088832)), (143/35184372088832), by norm_num⟩
  | 8 => ⟨((5002966359/281474976710656), (-2820507269/281474976710656)), (5/8796093022208), by norm_num⟩
  | 9 => ⟨((-305351129/140737488355328), (1377175087/1125899906842624)), (159/2251799813685248), by norm_num⟩
  | 10 => ⟨((2146960017/9007199254740992), (-2420770359/18014398509481984)), (71/9007199254740992), by norm_num⟩
  | 11 => ⟨((-857700603/36028797018963968), (967086569/72057594037927936)), (29/36028797018963968), by norm_num⟩
  | 12 => ⟨((5025495587/2305843009213693952), (-354151063/288230376151711744)), (173/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-1698791141/9223372036854775808), (957722363/9223372036854775808)), (119/18446744073709551616), by norm_num⟩
  | 14 => ⟨((2132928941/147573952589676412928), (-2404949845/295147905179352825856)), (19/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-4998958817/4722366482869645213696), (1409123975/2361183241434822606848)), (181/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((5491917587/75557863725914323419136), (-3096161831/75557863725914323419136)), (101/37778931862957161709568), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-83587189023/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890253910567297/316912650057057350374175801344), (-792840744157/633825300114114700748351602688)), (11535/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891698052957807/39614081257132168796771975168), (-891870039889/39614081257132168796771975168)), (25955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945797557003571/1237940039285380274899124224), (-947520260065/2475880078570760549798248448)), (27579/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773261054230229/154742504910672534362390528), (-118427144887/19342813113834066795298816)), (6895/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775747032859115/4835703278458516698824704), (-888094056213/9671406556917033397649408)), (12929/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78780400962677/37778931862957161709568), (-48560799055/37778931862957161709568)), (5657/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((59079695101685/2361183241434822606848), (-1262375470381/75557863725914323419136)), (36773/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299607562877979/4722366482869645213696), (-946601995139/4722366482869645213696)), (27583/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624290888904041/590295810358705651712), (-1301285945133/590295810358705651712)), (37931/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827026771247517/73786976294838206464), (-1626169846547/73786976294838206464)), (11855/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826651244307993/9223372036854775808), (-914419790389/4611686018427387904)), (53357/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399474367325017/288230376151711744), (-457021995969/288230376151711744)), (53369/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299500213854729/36028797018963968), (-799365907881/72057594037927936)), (46711/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496762414331519/36028797018963968), (-2396408323953/36028797018963968)), (35047/18014398509481984), by norm_num⟩
  | 3 => ⟨((747827492460443/4503599627370496), (-2992556070673/9007199254740992)), (5479/562949953421312), by norm_num⟩
  | 2 => ⟨((2240715839094265/4503599627370496), (-373516099615/281474976710656)), (175467/4503599627370496), by norm_num⟩
  | 1 => ⟨((558797091789055/562949953421312), (-1117784948877/281474976710656)), (263553/2251799813685248), by norm_num⟩
  | 0 => ⟨((554658741725629/562949953421312), (-17796309201081/2251799813685248)), (528519/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554658741725629/562949953421312), (-17796309201081/2251799813685248)), (2016139992720793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1092908965048289/1125899906842624), (-8767101239499/562949953421312)), (1049825/2251799813685248), by norm_num⟩
  | 2 => ⟨((1060611649729235/1125899906842624), (-68081672155063/2251799813685248)), (1035413/1125899906842624), by norm_num⟩
  | 3 => ⟨((1996160202502949/2251799813685248), (-128267555902373/2251799813685248)), (4026709/2251799813685248), by norm_num⟩
  | 4 => ⟨((881118064768193/1125899906842624), (-28426437910749/281474976710656)), (7597881/2251799813685248), by norm_num⟩
  | 5 => ⟨((169517743421143/281474976710656), (-177969979803353/1125899906842624)), (1639/274877906944), by norm_num⟩
  | 6 => ⟨((380235338008761/1125899906842624), (-214364130876069/1125899906842624)), (10208541/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-4285475141/134217728)), (1/67108864), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-20060163/16777216), (-5407667549/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-72569192479983/281474976710656), (-712586449894377/4503599627370496)), (60620825/4503599627370496), by norm_num⟩
  | 1 => ⟨((383767175/1073741824), (942091539/4294967296)), (81/4294967296), by norm_num⟩
  | 2 => ⟨((-2128057083/8589934592), (-2612032377/17179869184)), (227/17179869184), by norm_num⟩
  | 3 => ⟨((3933484713/34359738368), (301753813/4294967296)), (53/8589934592), by norm_num⟩
  | 4 => ⟨((-2726483839/68719476736), (-836639219/34359738368)), (149/68719476736), by norm_num⟩
  | 5 => ⟨((1511883669/137438953472), (1855725171/274877906944)), (167/274877906944), by norm_num⟩
  | 6 => ⟨((-2794554407/1099511627776), (-1715054227/1099511627776)), (39/274877906944), by norm_num⟩
  | 7 => ⟨((4427514305/8796093022208), (1358611431/4398046511104)), (125/4398046511104), by norm_num⟩
  | 8 => ⟨((-1534459529/17592186044416), (-941717683/17592186044416)), (175/35184372088832), by norm_num⟩
  | 9 => ⟨((945427819/70368744177664), (580221295/70368744177664)), (109/140737488355328), by norm_num⟩
  | 10 => ⟨((-2097026007/1125899906842624), (-1286972015/1125899906842624)), (61/562949953421312), by norm_num⟩
  | 11 => ⟨((528562787/2251799813685248), (1297543307/9007199254740992)), (249/18014398509481984), by norm_num⟩
  | 12 => ⟨((-1953982963/72057594037927936), (-2398369293/144115188075855872)), (29/18014398509481984), by norm_num⟩
  | 13 => ⟨((416737779/144115188075855872), (1023029485/576460752303423488)), (25/144115188075855872), by norm_num⟩
  | 14 => ⟨((-5282022703/18446744073709551616), (-3241645729/18446744073709551616)), (319/18446744073709551616), by norm_num⟩
  | 15 => ⟨((3905300421/147573952589676412928), (2396733437/147573952589676412928)), (119/73786976294838206464), by norm_num⟩
  | 16 => ⟨((-338368497/147573952589676412928), (-1661289025/1180591620717411303424)), (167/1180591620717411303424), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-421907946869/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780116478297963/633825300114114700748351602688), (-4000243207357/633825300114114700748351602688)), (23149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891257349617297/39614081257132168796771975168), (-1124943289765/9903520314283042199192993792)), (26049/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472781577845927/618970019642690137449562112), (-4780423071615/2475880078570760549798248448)), (6921/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772791627096371/154742504910672534362390528), (-4779763787401/154742504910672534362390528)), (27693/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551053314496815/9671406556917033397649408), (-4480327990753/9671406556917033397649408)), (25971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260100095091737/604462909807314587353088), (-1959793176353/302231454903657293676544)), (22733/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889921230256199/75557863725914323419136), (-3184006978235/37778931862957161709568)), (36957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299134716567445/4722366482869645213696), (-4774860666149/4722366482869645213696)), (6933/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623638960722853/590295810358705651712), (-6563564674917/590295810358705651712)), (19077/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913104608146769/36893488147419103232), (-4100826091879/36893488147419103232)), (47729/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912863930890439/4611686018427387904), (-4611501392901/4611686018427387904)), (26871/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399242387553003/288230376151711744), (-9218181556085/1152921504606846976)), (53803/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598591914691275/72057594037927936), (-8060483158361/144115188075855872)), (47145/144115188075855872), by norm_num⟩
  | 4 => ⟨((93470418662295/2251799813685248), (-12079868802623/36028797018963968)), (70853/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494092569276217/9007199254740992), (-7540413992831/4503599627370496)), (88803/9007199254740992), by norm_num⟩
  | 2 => ⟨((279692230960635/562949953421312), (-7526147920037/1125899906842624)), (11145/281474976710656), by norm_num⟩
  | 1 => ⟨((1115144507176591/1125899906842624), (-22507043625679/1125899906842624)), (134633/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104155002210215/1125899906842624), (-22364036628137/562949953421312)), (272847/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104155002210215/1125899906842624), (-22364036628137/562949953421312)), (1040828709128951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1081053174417531/1125899906842624), (-171344625381/2199023255552)), (278417/562949953421312), by norm_num⟩
  | 2 => ⟨((1031157102189711/1125899906842624), (-42117028712599/281474976710656)), (1156085/1125899906842624), by norm_num⟩
  | 3 => ⟨((919178922909079/1125899906842624), (-154291773242663/562949953421312)), (2463575/1125899906842624), by norm_num⟩
  | 4 => ⟨((665837240595509/1125899906842624), (-503852056762791/1125899906842624)), (5372921/1125899906842624), by norm_num⟩
  | 5 => ⟨((336570479681603/2251799813685248), (-297969172130149/562949953421312)), (5581889/562949953421312), by norm_num⟩
  | 6 => ⟨((-72569192479983/281474976710656), (-712586449894377/4503599627370496)), (60620825/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-5407667549/134217728)), (1/67108864), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-2911141/2097152), (-6278107605/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-528163132906137/2251799813685248), (-23975433907629/281474976710656)), (48902297/4503599627370496), by norm_num⟩
  | 1 => ⟨((3242667275/8589934592), (588790471/4294967296)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((-2609435825/8589934592), (-1895243413/17179869184)), (123/8589934592), by norm_num⟩
  | 3 => ⟨((5599633263/34359738368), (2033517735/34359738368)), (133/17179869184), by norm_num⟩
  | 4 => ⟨((-4506131035/68719476736), (-1636410269/68719476736)), (27/8589934592), by norm_num⟩
  | 5 => ⟨((5801870501/274877906944), (1053480291/137438953472)), (35/34359738368), by norm_num⟩
  | 6 => ⟨((-3112583449/549755813888), (-1130340747/549755813888)), (303/1099511627776), by norm_num⟩
  | 7 => ⟨((5725154067/4398046511104), (519775215/1099511627776)), (281/4398046511104), by norm_num⟩
  | 8 => ⟨((-4607140005/17592186044416), (-836545937/8796093022208)), (57/4398046511104), by norm_num⟩
  | 9 => ⟨((3295513685/70368744177664), (1196772219/70368744177664)), (165/70368744177664), by norm_num⟩
  | 10 => ⟨((-4243139733/562949953421312), (-1540904465/562949953421312)), (215/562949953421312), by norm_num⟩
  | 11 => ⟨((2483298165/2251799813685248), (1803629139/4503599627370496)), (127/2251799813685248), by norm_num⟩
  | 12 => ⟨((-2664476143/18014398509481984), (-1935219411/36028797018963968)), (137/18014398509481984), by norm_num⟩
  | 13 => ⟨((5277918673/288230376151711744), (1916686455/288230376151711744)), (137/144115188075855872), by norm_num⟩
  | 14 => ⟨((-4853989949/2305843009213693952), (-1762735913/2305843009213693952)), (127/1152921504606846976), by norm_num⟩
  | 15 => ⟨((260406515/1152921504606846976), (756537069/9223372036854775808)), (55/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-3352864943/147573952589676412928), (-1217599441/147573952589676412928)), (89/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-909629853967/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444954504398849/158456325028528675187087900672), (-4310877011275/633825300114114700748351602688)), (23157/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236365192949217/4951760157141521099596496896), (-4849113073659/39614081257132168796771975168)), (13029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890769462833367/2475880078570760549798248448), (-160982803805/77371252455336267181195264)), (27695/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55388584911057/4835703278458516698824704), (-5150625029209/154742504910672534362390528)), (27703/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550718646281865/9671406556917033397649408), (-4827834666755/9671406556917033397649408)), (25981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259807195355829/604462909807314587353088), (-4223478965139/604462909807314587353088)), (22743/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944722573212287/37778931862957161709568), (-6861509979171/75557863725914323419136)), (36975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81173596709805/295147905179352825856), (-5144694414353/4722366482869645213696)), (27747/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50723365020093/18446744073709551616), (-7071617678901/590295810358705651712)), (38177/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825594858238903/73786976294838206464), (-4418007952187/36893488147419103232)), (23879/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912518177683439/4611686018427387904), (-9935696093863/9223372036854775808)), (13445/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596277603421773/1152921504606846976), (-4964833839725/576460752303423488)), (53845/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299144470688297/36028797018963968), (-4340837829729/72057594037927936)), (11797/36028797018963968), by norm_num⟩
  | 4 => ⟨((747308398930147/18014398509481984), (-6504471206765/18014398509481984)), (70927/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492953489517967/9007199254740992), (-16237419814445/9007199254740992)), (88915/9007199254740992), by norm_num⟩
  | 2 => ⟨((139703414173895/281474976710656), (-4050441267517/562949953421312)), (22325/562949953421312), by norm_num⟩
  | 1 => ⟨((556712926166651/562949953421312), (-6053362649495/281474976710656)), (134913/1125899906842624), by norm_num⟩
  | 0 => ⟨((550346630005337/562949953421312), (-6008719930741/140737488355328)), (273693/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550346630005337/562949953421312), (-6008719930741/140737488355328)), (1044055943015670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1073998624132365/1125899906842624), (-93987147367023/1125899906842624)), (558503/1125899906842624), by norm_num⟩
  | 2 => ⟨((508322033695673/562949953421312), (-179309131024589/1125899906842624)), (1158761/1125899906842624), by norm_num⟩
  | 3 => ⟨((889433766898075/1125899906842624), (-161909209848373/562949953421312)), (2461719/1125899906842624), by norm_num⟩
  | 4 => ⟨((1218996560161403/2251799813685248), (-1023234961017247/2251799813685248)), (10610841/2251799813685248), by norm_num⟩
  | 5 => ⟨((48732443440321/562949953421312), (-138480326951841/281474976710656)), (5282877/562949953421312), by norm_num⟩
  | 6 => ⟨((-528163132906137/2251799813685248), (-23975433907629/281474976710656)), (48902297/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-6278107605/134217728)), (1/67108864), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-6989308915/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-113260173136711/2251799813685248), (-116649417759561/562949953421312)), (20345429/2251799813685248), by norm_num⟩
  | 1 => ⟨((1548271085/17179869184), (6378408779/17179869184)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((-1387064689/17179869184), (-1428571791/4294967296)), (253/17179869184), by norm_num⟩
  | 3 => ⟨((1656857527/34359738368), (6825752091/34359738368)), (19/2147483648), by norm_num⟩
  | 4 => ⟨((-742172541/34359738368), (-1528763243/17179869184)), (137/34359738368), by norm_num⟩
  | 5 => ⟨((1063835743/137438953472), (4382681627/137438953472)), (99/68719476736), by norm_num⟩
  | 6 => ⟨((-1270758511/549755813888), (-5235140871/549755813888)), (119/274877906944), by norm_num⟩
  | 7 => ⟨((650541027/1099511627776), (2680032351/1099511627776)), (123/1099511627776), by norm_num⟩
  | 8 => ⟨((-1165613045/8796093022208), (-4801973343/8796093022208)), (111/4398046511104), by norm_num⟩
  | 9 => ⟨((928221427/35184372088832), (119499739/1099511627776)), (89/17592186044416), by norm_num⟩
  | 10 => ⟨((-1330519625/281474976710656), (-5481338597/281474976710656)), (257/281474976710656), by norm_num⟩
  | 11 => ⟨((866898595/1125899906842624), (1785680061/562949953421312)), (169/1125899906842624), by norm_num⟩
  | 12 => ⟨((-258878961/2251799813685248), (-4266012211/9007199254740992)), (51/2251799813685248), by norm_num⟩
  | 13 => ⟨((1141781735/72057594037927936), (2351897777/36028797018963968)), (113/36028797018963968), by norm_num⟩
  | 14 => ⟨((-1169027563/576460752303423488), (-4816040129/576460752303423488)), (233/576460752303423488), by norm_num⟩
  | 15 => ⟨((1117128643/4611686018427387904), (2301116135/2305843009213693952)), (7/144115188075855872), by norm_num⟩
  | 16 => ⟨((-62550807/2305843009213693952), (-4123046625/36893488147419103232)), (101/18446744073709551616), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-2356329294807/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889790560491099/316912650057057350374175801344), (-697757205821/158456325028528675187087900672)), (1445/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472663852240141/9903520314283042199192993792), (-784867914977/9903520314283042199192993792)), (26013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118155447698463/154742504910672534362390528), (-3335161884377/2475880078570760549798248448)), (27645/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772152944262227/154742504910672534362390528), (-3334569342829/154742504910672534362390528)), (13825/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550455043673541/9671406556917033397649408), (-1562764632503/4835703278458516698824704)), (3241/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157447137789149/75557863725914323419136), (-85444022019/18889465931478580854784)), (11347/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889072293299069/75557863725914323419136), (-4441909210467/75557863725914323419136)), (4611/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324624706016839/1180591620717411303424), (-3330399659931/4722366482869645213696)), (6919/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622765924573115/590295810358705651712), (-4577622494859/590295810358705651712)), (19035/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825119894172355/73786976294838206464), (-5719513201761/73786976294838206464)), (11903/18446744073709551616), by norm_num⟩
  | 7 => ⟨((28507891964835/144115188075855872), (-6430995380925/9223372036854775808)), (53597/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398937540239165/288230376151711744), (-3213337863541/576460752303423488)), (53639/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196120670581051/144115188075855872), (-5618483796619/144115188075855872)), (23491/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493939565666785/36028797018963968), (-8418016133835/36028797018963968)), (70567/36028797018963968), by norm_num⟩
  | 3 => ⟨((186515242950003/1125899906842624), (-2626385130485/2251799813685248)), (88375/9007199254740992), by norm_num⟩
  | 2 => ⟨((558409098186601/1125899906842624), (-5240047623999/1125899906842624)), (88623/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112268029974051/1125899906842624), (-1957076807541/140737488355328)), (133559/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098599713233809/1125899906842624), (-7764906164821/281474976710656)), (269617/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098599713233809/1125899906842624), (-7764906164821/281474976710656)), (1028507236960982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1071104653534711/1125899906842624), (-30306508186441/562949953421312)), (541035/1125899906842624), by norm_num⟩
  | 2 => ⟨((1015713061276363/1125899906842624), (-115326208852497/1125899906842624)), (543831/562949953421312), by norm_num⟩
  | 3 => ⟨((1808993645367549/2251799813685248), (-104039742722299/562949953421312)), (1092627/562949953421312), by norm_num⟩
  | 4 => ⟨((1376352241035325/2251799813685248), (-10447600198877/35184372088832)), (4318789/1125899906842624), by norm_num⟩
  | 5 => ⟨((321355712295805/1125899906842624), (-204346093073091/562949953421312)), (15688639/2251799813685248), by norm_num⟩
  | 6 => ⟨((-113260173136711/2251799813685248), (-116649417759561/562949953421312)), (20345429/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-6989308915/134217728)), (1/67108864), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-225263989/134217728), (-7590621055/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((1681454954511841/9007199254740992), (-19265314997/17592186044416)), (25875937/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6240768931/17179869184), (18304967/8589934592)), (49/8589934592), by norm_num⟩
  | 2 => ⟨((758998475/2147483648), (-35619821/17179869184)), (97/17179869184), by norm_num⟩
  | 3 => ⟨((-7877028457/34359738368), (46208647/34359738368)), (1/268435456), by norm_num⟩
  | 4 => ⟨((7663994809/68719476736), (-22479469/34359738368)), (127/68719476736), by norm_num⟩
  | 5 => ⟨((-93209033/2147483648), (34994421/137438953472)), (101/137438953472), by norm_num⟩
  | 6 => ⟨((7738726541/549755813888), (-45397333/549755813888)), (133/549755813888), by norm_num⟩
  | 7 => ⟨((-2151266645/549755813888), (3154969/137438953472)), (19/274877906944), by norm_num⟩
  | 8 => ⟨((2093085799/2199023255552), (-24557145/4398046511104)), (75/4398046511104), by norm_num⟩
  | 9 => ⟨((-7240812265/35184372088832), (21238221/17592186044416)), (33/8796093022208), by norm_num⟩
  | 10 => ⟨((5635988029/140737488355328), (-4132767/17592186044416)), (105/140737488355328), by norm_num⟩
  | 11 => ⟨((-3988045929/562949953421312), (46789779/1125899906842624)), (151/1125899906842624), by norm_num⟩
  | 12 => ⟨((323349127/281474976710656), (-30349569/4503599627370496)), (99/4503599627370496), by norm_num⟩
  | 13 => ⟨((-6195282195/36028797018963968), (18171549/18014398509481984)), (15/4503599627370496), by norm_num⟩
  | 14 => ⟨((3444417857/144115188075855872), (-40411659/288230376151711744)), (135/288230376151711744), by norm_num⟩
  | 15 => ⟨((-7149362843/2305843009213693952), (41939977/2305843009213693952)), (71/1152921504606846976), by norm_num⟩
  | 16 => ⟨((3478004429/9223372036854775808), (-40805713/18446744073709551616)), (35/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532090827/10141204801825835211973625643008), (-1910340677/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779380167133749/633825300114114700748351602688), (-9049069657/633825300114114700748351602688)), (23051/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890429609979325/39614081257132168796771975168), (-10178699411/39614081257132168796771975168)), (6483/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945123799344141/1237940039285380274899124224), (-10813016615/2475880078570760549798248448)), (27553/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771913769870815/154742504910672534362390528), (-5405467137/77371252455336267181195264)), (27553/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550231231972633/9671406556917033397649408), (-10133038963/9671406556917033397649408)), (25831/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157422710144637/75557863725914323419136), (-2216049453/151115727451828646838272)), (22603/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472188877470227/18889465931478580854784), (-3600044163/18889465931478580854784)), (36729/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649130957512861/2361183241434822606848), (-10796507153/4722366482869645213696)), (27547/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811220638204011/295147905179352825856), (-7419654353/295147905179352825856)), (9469/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456178933790777/18446744073709551616), (-18540307387/73786976294838206464)), (47345/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824052674899407/9223372036854775808), (-20845713853/9223372036854775808)), (53263/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595300581612365/1152921504606846976), (-20830559735/1152921504606846976)), (3329/72057594037927936), by norm_num⟩
  | 5 => ⟨((1195730469237457/144115188075855872), (-2276213283/18014398509481984)), (23303/72057594037927936), by norm_num⟩
  | 4 => ⟨((746680306337913/18014398509481984), (-27280529545/36028797018963968)), (69909/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491409335870939/9007199254740992), (-8510298301/2251799813685248)), (21847/2251799813685248), by norm_num⟩
  | 2 => ⟨((2232244318853819/4503599627370496), (-16976078445/1125899906842624)), (87389/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111265211206521/1125899906842624), (-12676556795/281474976710656)), (8193/70368744177664), by norm_num⟩
  | 0 => ⟨((548378941759023/562949953421312), (-100527908805/1125899906842624)), (524397/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548378941759023/562949953421312), (-100527908805/1125899906842624)), (2000415810591887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2136740286845515/2251799813685248), (-391703652609/2251799813685248)), (1021743/2251799813685248), by norm_num⟩
  | 2 => ⟨((1013779926672265/1125899906842624), (-46461111349/140737488355328)), (1939427/2251799813685248), by norm_num⟩
  | 3 => ⟨((1825650033941513/2251799813685248), (-83668791107/140737488355328)), (3493869/2251799813685248), by norm_num⟩
  | 4 => ⟨((740073836505139/1125899906842624), (-2170707081807/2251799813685248)), (2834737/1125899906842624), by norm_num⟩
  | 5 => ⟨((972925039177011/2251799813685248), (-2853687984515/2251799813685248)), (14928443/4503599627370496), by norm_num⟩
  | 6 => ⟨((1681454954511841/9007199254740992), (-19265314997/17592186044416)), (25875937/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-225263989/134217728), (-7590621055/134217728)), (1/67108864), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-240721955/134217728), (-8111501323/134217728)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-550719273942143/4503599627370496), (1016130203797013/9007199254740992)), (12725023/1125899906842624), by norm_num⟩
  | 1 => ⟨((4368547577/17179869184), (-2015097959/8589934592)), (407/17179869184), by norm_num⟩
  | 2 => ⟨((-2271034827/8589934592), (2095139203/8589934592)), (107/4294967296), by norm_num⟩
  | 3 => ⟨((3148322775/17179869184), (-2904479663/17179869184)), (299/17179869184), by norm_num⟩
  | 4 => ⟨((-3273376583/34359738368), (1509923917/17179869184)), (313/34359738368), by norm_num⟩
  | 5 => ⟨((2722718099/68719476736), (-1255919407/34359738368)), (263/68719476736), by norm_num⟩
  | 6 => ⟨((-943622187/68719476736), (217634249/17179869184)), (367/274877906944), by norm_num⟩
  | 7 => ⟨((1121261243/274877906944), (-258604399/68719476736)), (55/137438953472), by norm_num⟩
  | 8 => ⟨((-291449651/274877906944), (2151010921/2199023255552)), (231/2199023255552), by norm_num⟩
  | 9 => ⟨((4309706749/17592186044416), (-1987956207/8796093022208)), (215/8796093022208), by norm_num⟩
  | 10 => ⟨((-3584713299/70368744177664), (6459123/137438953472)), (45/8796093022208), by norm_num⟩
  | 11 => ⟨((1355309409/140737488355328), (-2500676643/281474976710656)), (137/140737488355328), by norm_num⟩
  | 12 => ⟨((-3757715583/2251799813685248), (3466673929/2251799813685248)), (383/2251799813685248), by norm_num⟩
  | 13 => ⟨((150268267/562949953421312), (-2218075625/9007199254740992)), (31/1125899906842624), by norm_num⟩
  | 14 => ⟨((-2856905845/72057594037927936), (658908371/18014398509481984)), (297/72057594037927936), by norm_num⟩
  | 15 => ⟨((3168409971/576460752303423488), (-1461505535/288230376151711744)), (83/144115188075855872), by norm_num⟩
  | 16 => ⟨((-1647130829/2305843009213693952), (3039115323/4611686018427387904)), (87/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509236873/10141204801825835211973625643008), (1560827513155/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889597609053341/316912650057057350374175801344), (3696030293937/633825300114114700748351602688)), (4339/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890221154611059/39614081257132168796771975168), (4157362271697/39614081257132168796771975168)), (9765/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890025614948027/2475880078570760549798248448), (4416387334595/2475880078570760549798248448)), (41511/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885845612052891/77371252455336267181195264), (4415476036817/154742504910672534362390528)), (20761/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193752749813567/1208925819614629174706176), (1034635160001/2417851639229258349412352)), (9735/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157399750681403/75557863725914323419136), (3620255038343/604462909807314587353088)), (8521/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888455919379327/75557863725914323419136), (5881099657937/75557863725914323419136)), (55409/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20281816330805/73786976294838206464), (1102309268237/1180591620717411303424)), (41577/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811064697149773/295147905179352825856), (3030060750685/295147905179352825856)), (3575/36893488147419103232), by norm_num⟩
  | 8 => ⟨((912161753057823/36893488147419103232), (7571283525285/73786976294838206464)), (71549/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911804077000623/4611686018427387904), (8512376380983/9223372036854775808)), (80559/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99678249262771/72057594037927936), (4252865749979/576460752303423488)), (80643/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195333377381635/144115188075855872), (929380307951/18014398509481984)), (70657/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492755851994709/36028797018963968), (11137625742063/36028797018963968)), (106173/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490637470170283/9007199254740992), (217123548381/140737488355328)), (66523/4503599627370496), by norm_num⟩
  | 2 => ⟨((557663260863851/1125899906842624), (3464188060503/562949953421312)), (133541/2251799813685248), by norm_num⟩
  | 1 => ⟨((555006337436911/562949953421312), (323239942661/17592186044416)), (100777/562949953421312), by norm_num⟩
  | 0 => ⟨((1094018586984831/1125899906842624), (20492159235335/562949953421312)), (408089/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094018586984831/1125899906842624), (20492159235335/562949953421312)), (1556735996726607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((33173379440859/35184372088832), (79647588403409/1125899906842624)), (411389/562949953421312), by norm_num⟩
  | 2 => ⟨((124405010701143/140737488355328), (75095262890717/562949953421312)), (1667913/1125899906842624), by norm_num⟩
  | 3 => ⟨((429854211767019/562949953421312), (531044121517243/2251799813685248)), (848423/281474976710656), by norm_num⟩
  | 4 => ⟨((593833079372775/1125899906842624), (405491733112313/1125899906842624)), (6783349/1125899906842624), by norm_num⟩
  | 5 => ⟨((20895971679083/140737488355328), (855473574767587/2251799813685248)), (12041513/1125899906842624), by norm_num⟩
  | 6 => ⟨((-550719273942143/4503599627370496), (1016130203797013/9007199254740992)), (12725023/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-240721955/134217728), (-8111501323/134217728)), (3/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile047Terms0
