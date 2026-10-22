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
namespace Reinmann.XiBand97.Tile021Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28251/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28251/1280))
  have he : value ((69/80), (28251/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-1026666057/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-110346508043093/18014398509481984), (1644716437151919/18014398509481984)), (135808585/9007199254740992), by norm_num⟩
  | 1 => ⟨((4558943/268435456), (-543608933/2147483648)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-6320037/268435456), (1507203997/4294967296)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((93455271/4294967296), (-348238067/1073741824)), (59/1073741824), by norm_num⟩
  | 4 => ⟨((-129556515/8589934592), (1931041875/8589934592)), (165/4294967296), by norm_num⟩
  | 5 => ⟨((35920693/4294967296), (-1070796985/8589934592)), (185/8589934592), by norm_num⟩
  | 6 => ⟨((-66395539/17179869184), (247406637/4294967296)), (345/34359738368), by norm_num⟩
  | 7 => ⟨((52596435/34359738368), (-1567901375/68719476736)), (275/68719476736), by norm_num⟩
  | 8 => ⟨((-72914141/137438953472), (543393209/68719476736)), (193/137438953472), by norm_num⟩
  | 9 => ⟨((22462325/137438953472), (-1339205229/549755813888)), (15/34359738368), by norm_num⟩
  | 10 => ⟨((-49823031/1099511627776), (742613063/1099511627776)), (67/549755813888), by norm_num⟩
  | 11 => ⟨((100464563/8796093022208), (-748712947/4398046511104)), (17/549755813888), by norm_num⟩
  | 12 => ⟨((-92848971/35184372088832), (691957691/17592186044416)), (253/35184372088832), by norm_num⟩
  | 13 => ⟨((79209849/140737488355328), (-147578007/17592186044416)), (109/70368744177664), by norm_num⟩
  | 14 => ⟨((-15686881/140737488355328), (935252841/562949953421312)), (347/1125899906842624), by norm_num⟩
  | 15 => ⟨((92785641/4503599627370496), (-21608929/70368744177664)), (259/4503599627370496), by norm_num⟩
  | 16 => ⟨((-128628211/36028797018963968), (1917205531/36028797018963968)), (361/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (2133401002289/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778277525370529/633825300114114700748351602688), (1261724691707/316912650057057350374175801344)), (92449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889189168231317/39614081257132168796771975168), (2838287234365/39614081257132168796771975168)), (104021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944464825786815/1237940039285380274899124224), (3014944271313/2475880078570760549798248448)), (110541/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770595847947595/154742504910672534362390528), (753529162725/38685626227668133590597632)), (110561/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548995707052251/9671406556917033397649408), (2824855285343/9671406556917033397649408)), (103673/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78643788991617/37778931862957161709568), (2470869605535/604462909807314587353088)), (90737/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471749710678313/18889465931478580854784), (4013516066347/75557863725914323419136)), (4609/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648472229746543/2361183241434822606848), (3008696536707/4722366482869645213696)), (110653/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202578731055367/73786976294838206464), (64603408143/9223372036854775808)), (76103/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911225780603953/36893488147419103232), (1291191338703/18446744073709551616)), (95173/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910752816653665/4611686018427387904), (2902770974241/4611686018427387904)), (107131/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592753734872183/1152921504606846976), (362470205407/72057594037927936)), (107207/576460752303423488), by norm_num⟩
  | 5 => ⟨((298375550147719/36028797018963968), (316738687625/9007199254740992)), (187785/144115188075855872), by norm_num⟩
  | 4 => ⟨((186252332724477/4503599627370496), (3794109271421/18014398509481984)), (70505/9007199254740992), by norm_num⟩
  | 3 => ⟨((371808176362071/2251799813685248), (9461670727485/9007199254740992)), (44141/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111946775180137/2251799813685248), (9426346904147/2251799813685248)), (354035/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105005368375455/1125899906842624), (28102979622643/2251799813685248)), (533325/1125899906842624), by norm_num⟩
  | 0 => ⟨((2168503671885171/2251799813685248), (6938131935495/281474976710656)), (1075779/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168503671885171/2251799813685248), (6938131935495/281474976710656)), (4103771214011764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2086920575814585/2251799813685248), (53451872539315/1125899906842624)), (4250009/2251799813685248), by norm_num⟩
  | 2 => ⟨((1929038741653263/2251799813685248), (198152272578005/2251799813685248)), (8281175/2251799813685248), by norm_num⟩
  | 3 => ⟨((817551835934655/1125899906842624), (169750174161369/1125899906842624)), (15645833/2251799813685248), by norm_num⟩
  | 4 => ⟨((284028748437275/562949953421312), (493044064369935/2251799813685248)), (27439673/2251799813685248), by norm_num⟩
  | 5 => ⟨((930513292739381/4503599627370496), (995034728585295/4503599627370496)), (79409533/4503599627370496), by norm_num⟩
  | 6 => ⟨((-110346508043093/18014398509481984), (1644716437151919/18014398509481984)), (135808585/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1026666057/16777216)), (1/16777216), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-40997585/16777216), (-1049114839/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((747342070922243/9007199254740992), (461927281511245/18014398509481984)), (254390533/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1009645237/4294967296), (-312027583/4294967296)), (87/2147483648), by norm_num⟩
  | 2 => ⟨((1430270179/4294967296), (110505089/1073741824)), (31/536870912), by norm_num⟩
  | 3 => ⟨((-1350753519/4294967296), (-208722995/2147483648)), (59/1073741824), by norm_num⟩
  | 4 => ⟨((119592903/536870912), (295678387/4294967296)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((-271065767/2147483648), (-335087981/8589934592)), (97/4294967296), by norm_num⟩
  | 6 => ⟨((63998929/1073741824), (79114645/4294967296)), (185/17179869184), by norm_num⟩
  | 7 => ⟨((-207225851/8589934592), (-128084953/17179869184)), (151/34359738368), by norm_num⟩
  | 8 => ⟨((1174230093/137438953472), (181445999/68719476736)), (27/17179869184), by norm_num⟩
  | 9 => ⟨((-1478597497/549755813888), (-114238939/137438953472)), (137/274877906944), by norm_num⟩
  | 10 => ⟨((52364777/68719476736), (258930629/1099511627776)), (157/1099511627776), by norm_num⟩
  | 11 => ⟨((-431594429/2199023255552), (-133382857/2199023255552)), (163/4398046511104), by norm_num⟩
  | 12 => ⟨((815199397/17592186044416), (251934727/17592186044416)), (155/17592186044416), by norm_num⟩
  | 13 => ⟨((-710656557/70368744177664), (-439252203/140737488355328)), (273/140737488355328), by norm_num⟩
  | 14 => ⟨((35954315/17592186044416), (177785029/281474976710656)), (223/562949953421312), by norm_num⟩
  | 15 => ⟨((-6791083/17592186044416), (-67160389/562949953421312)), (171/2251799813685248), by norm_num⟩
  | 16 => ⟨((1231397567/18014398509481984), (380559421/18014398509481984)), (245/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (97609824769/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778200261990421/633825300114114700748351602688), (461783199639/633825300114114700748351602688)), (184491/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889102448920211/39614081257132168796771975168), (519396269787/39614081257132168796771975168)), (207559/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944418889006695/1237940039285380274899124224), (551721041095/2475880078570760549798248448)), (110269/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442626068255711/38685626227668133590597632), (137891607527/38685626227668133590597632)), (110273/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548910172638421/9671406556917033397649408), (258464657543/4835703278458516698824704)), (103385/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39319565565059/18889465931478580854784), (452149006251/604462909807314587353088)), (45233/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886878331836083/75557863725914323419136), (734434510211/75557863725914323419136)), (294029/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648427297568137/2361183241434822606848), (275278428323/2361183241434822606848)), (27567/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405126781752543/147573952589676412928), (94572347981/73786976294838206464)), (151629/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227787427595767/9223372036854775808), (472534308281/36893488147419103232)), (189553/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821336206845031/9223372036854775808), (1062302532467/9223372036854775808)), (426539/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398146617150779/288230376151711744), (1061179118583/1152921504606846976)), (426597/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596679133511113/72057594037927936), (927269484853/144115188075855872)), (373337/144115188075855872), by norm_num⟩
  | 4 => ⟨((744903797900875/18014398509481984), (1388383725769/36028797018963968)), (560135/36028797018963968), by norm_num⟩
  | 3 => ⟨((743488650294753/4503599627370496), (1731077733711/9007199254740992)), (175099/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223407893934805/4503599627370496), (1724492719221/2251799813685248)), (175185/562949953421312), by norm_num⟩
  | 1 => ⟨((2209344683361689/2251799813685248), (2570338921739/1125899906842624)), (262995/281474976710656), by norm_num⟩
  | 0 => ⟨((2167418591388859/2251799813685248), (10150900290351/2251799813685248)), (1053747/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167418591388859/2251799813685248), (10150900290351/2251799813685248)), (4019725801708030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2086153609646751/2251799813685248), (9770517732051/1125899906842624)), (2038021/562949953421312), by norm_num⟩
  | 2 => ⟨((120782690265363/140737488355328), (18103563834547/1125899906842624)), (7623147/1125899906842624), by norm_num⟩
  | 3 => ⟨((828966753118507/1125899906842624), (7768353581125/281474976710656)), (13329711/1125899906842624), by norm_num⟩
  | 4 => ⟨((304743040001857/562949953421312), (45756869192969/1125899906842624)), (40728619/2251799813685248), by norm_num⟩
  | 5 => ⟨((328074981084071/1125899906842624), (198157400445107/4503599627370496)), (94811771/4503599627370496), by norm_num⟩
  | 6 => ⟨((747342070922243/9007199254740992), (461927281511245/18014398509481984)), (254390533/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1049114839/16777216)), (1/8388608), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2614043/1048576), (-1070280115/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((425930710553319/9007199254740992), (-19085471682399/281474976710656)), (188127777/9007199254740992), by norm_num⟩
  | 1 => ⟨((-293516659/2147483648), (841737493/4294967296)), (261/4294967296), by norm_num⟩
  | 2 => ⟨((424186131/2147483648), (-1216467139/4294967296)), (379/4294967296), by norm_num⟩
  | 3 => ⟨((-817370409/4294967296), (146501761/536870912)), (367/4294967296), by norm_num⟩
  | 4 => ⟨((590626087/4294967296), (-846889105/4294967296)), (267/4294967296), by norm_num⟩
  | 5 => ⟨((-682851585/8589934592), (979129741/8589934592)), (311/8589934592), by norm_num⟩
  | 6 => ⟨((82237289/2147483648), (-471674825/8589934592)), (151/8589934592), by norm_num⟩
  | 7 => ⟨((-543305915/34359738368), (389518741/17179869184)), (251/34359738368), by norm_num⟩
  | 8 => ⟨((196294509/34359738368), (-70365873/8589934592)), (365/137438953472), by norm_num⟩
  | 9 => ⟨((-504323649/274877906944), (723141447/274877906944)), (59/68719476736), by norm_num⟩
  | 10 => ⟨((583073133/1099511627776), (-418029523/549755813888)), (275/1099511627776), by norm_num⟩
  | 11 => ⟨((-612835679/4398046511104), (878735075/4398046511104)), (291/4398046511104), by norm_num⟩
  | 12 => ⟨((147610245/4398046511104), (-846623681/17592186044416)), (141/8796093022208), by norm_num⟩
  | 13 => ⟨((-262552913/35184372088832), (376470335/35184372088832)), (63/17592186044416), by norm_num⟩
  | 14 => ⟨((433643157/281474976710656), (-1243587685/562949953421312)), (209/281474976710656), by norm_num⟩
  | 15 => ⟨((-83559329/281474976710656), (239628715/562949953421312)), (81/562949953421312), by norm_num⟩
  | 16 => ⟨((483035049/9007199254740992), (-346308035/4503599627370496)), (59/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (-1252868810287/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889061625288369/316912650057057350374175801344), (-740840725369/316912650057057350374175801344)), (46173/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889015770680021/39614081257132168796771975168), (-208316442151/4951760157141521099596496896)), (207797/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944372813650967/1237940039285380274899124224), (-442559897347/618970019642690137449562112)), (110403/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770412060428351/154742504910672534362390528), (-1769733372639/154742504910672534362390528)), (220831/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548823657641231/9671406556917033397649408), (-103661711025/604462909807314587353088)), (207055/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258150331838051/604462909807314587353088), (-1450726513161/604462909807314587353088)), (11325/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((235844386099437/9444732965739290427392), (-2356423347377/75557863725914323419136)), (294497/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296762055468719/4722366482869645213696), (-1766436644065/4722366482869645213696)), (55229/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810189855367831/295147905179352825856), (-2427419849845/590295810358705651712)), (303829/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911069944775891/36893488147419103232), (-1516065267071/36893488147419103232)), (189945/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821156376303795/9223372036854775808), (-3408200945395/9223372036854775808)), (835/18014398509481984), by norm_num⟩
  | 6 => ⟨((199050773976623/144115188075855872), (-851130568905/288230376151711744)), (427701/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596600012194735/72057594037927936), (-2974823586445/144115188075855872)), (374441/144115188075855872), by norm_num⟩
  | 4 => ⟨((372392308733173/9007199254740992), (-556747662625/4503599627370496)), (562067/36028797018963968), by norm_num⟩
  | 3 => ⟨((743338806892959/4503599627370496), (-5553060588451/9007199254740992)), (703295/9007199254740992), by norm_num⟩
  | 2 => ⟨((555700837156847/1125899906842624), (-11062987241423/4503599627370496)), (352183/1125899906842624), by norm_num⟩
  | 1 => ⟨((276053132462125/281474976710656), (-16487044650899/2251799813685248)), (2118473/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082764429137623/1125899906842624), (-4068341034701/281474976710656)), (4258579/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082764429137623/1125899906842624), (-4068341034701/281474976710656)), (16245189675337981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520523174174649/562949953421312), (-31299798010133/1125899906842624)), (8313953/2251799813685248), by norm_num⟩
  | 2 => ⟨((120214707306047/140737488355328), (-115763542476513/2251799813685248)), (3959249/562949953421312), by norm_num⟩
  | 3 => ⟨((409250657864457/562949953421312), (-49441270190887/562949953421312)), (28683531/2251799813685248), by norm_num⟩
  | 4 => ⟨((1172691538644717/2251799813685248), (-143770310154955/1125899906842624)), (23371357/1125899906842624), by norm_num⟩
  | 5 => ⟨((143499194358377/562949953421312), (-598981224538315/4503599627370496)), (121245619/4503599627370496), by norm_num⟩
  | 6 => ⟨((425930710553319/9007199254740992), (-19085471682399/281474976710656)), (188127777/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1070280115/16777216)), (1/8388608), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-1090300747/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-784074243410195/18014398509481984), (-592748951909487/9007199254740992)), (257839041/9007199254740992), by norm_num⟩
  | 1 => ⟨((275213571/2147483648), (208057537/1073741824)), (91/1073741824), by norm_num⟩
  | 2 => ⟨((-405174783/2147483648), (-306306361/1073741824)), (269/2147483648), by norm_num⟩
  | 3 => ⟨((49708851/268435456), (300633463/1073741824)), (265/2147483648), by norm_num⟩
  | 4 => ⟨((-292729357/2147483648), (-885196887/4294967296)), (49/536870912), by norm_num⟩
  | 5 => ⟨((689538983/8589934592), (1042563287/8589934592)), (29/536870912), by norm_num⟩
  | 6 => ⟨((-338384243/8589934592), (-255813665/4294967296)), (457/17179869184), by norm_num⟩
  | 7 => ⟨((142335965/8589934592), (107603961/4294967296)), (193/17179869184), by norm_num⟩
  | 8 => ⟨((-838199127/137438953472), (-316833297/34359738368)), (285/68719476736), by norm_num⟩
  | 9 => ⟨((548450263/274877906944), (207310291/68719476736)), (375/274877906944), by norm_num⟩
  | 10 => ⟨((-645951333/1099511627776), (-976660003/1099511627776)), (111/274877906944), by norm_num⟩
  | 11 => ⟨((43226461/274877906944), (522857415/2199023255552)), (477/4398046511104), by norm_num⟩
  | 12 => ⟨((-169703569/4398046511104), (-1026347835/17592186044416)), (471/17592186044416), by norm_num⟩
  | 13 => ⟨((614992989/70368744177664), (232462967/17592186044416)), (107/17592186044416), by norm_num⟩
  | 14 => ⟨((-258687047/140737488355328), (-782254881/281474976710656)), (181/140737488355328), by norm_num⟩
  | 15 => ⟨((50779215/140737488355328), (1228427607/2251799813685248)), (571/2251799813685248), by norm_num⟩
  | 16 => ⟨((-37379075/562949953421312), (-226064383/2251799813685248)), (211/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-2807304808201/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778046683336415/633825300114114700748351602688), (-1659874953247/316912650057057350374175801344)), (92527/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472232347433901/9903520314283042199192993792), (-466735965745/4951760157141521099596496896)), (52057/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888653522671831/2475880078570760549798248448), (-1983113559339/1237940039285380274899124224)), (221291/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442579897679585/38685626227668133590597632), (-3965070307059/154742504910672534362390528)), (110673/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548736579704783/9671406556917033397649408), (-3716024664755/9671406556917033397649408)), (207569/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258073751413875/604462909807314587353088), (-3250293243065/604462909807314587353088)), (90841/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886629920301099/75557863725914323419136), (-1319856063793/18889465931478580854784)), (147671/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324166886301529/1180591620717411303424), (-1978777289769/2361183241434822606848)), (110801/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620248730455745/590295810358705651712), (-5438367058221/590295810358705651712)), (152429/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910987311827781/36893488147419103232), (-3396527971273/36893488147419103232)), (190653/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227621042238415/1152921504606846976), (-954431388653/1152921504606846976)), (429291/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592215516561481/1152921504606846976), (-3813518512577/576460752303423488)), (429693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193030225283857/144115188075855872), (-6664201102437/144115188075855872)), (188217/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489308640217917/36028797018963968), (-9977412926517/36028797018963968)), (141389/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486341598233325/9007199254740992), (-6219382269681/4503599627370496)), (177133/2251799813685248), by norm_num⟩
  | 2 => ⟨((2222100684272873/4503599627370496), (-3097342332219/562949953421312)), (355459/1125899906842624), by norm_num⟩
  | 1 => ⟨((2207295118959981/2251799813685248), (-36921881648573/2251799813685248)), (134045/140737488355328), by norm_num⟩
  | 0 => ⟨((1081484507247787/1125899906842624), (-72863349735831/2251799813685248)), (4337507/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081484507247787/1125899906842624), (-72863349735831/2251799813685248)), (16546276101119231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1037642391995159/1125899906842624), (-139977956133703/2251799813685248)), (8613501/2251799813685248), by norm_num⟩
  | 2 => ⟨((1903905080905931/2251799813685248), (-258010610617221/2251799813685248)), (16947483/2251799813685248), by norm_num⟩
  | 3 => ⟨((197524501305743/281474976710656), (-436297853384965/2251799813685248)), (8135499/562949953421312), by norm_num⟩
  | 4 => ⟨((1024364421980261/2251799813685248), (-612342290016211/2251799813685248)), (29141461/1125899906842624), by norm_num⟩
  | 5 => ⟨((598951456322411/4503599627370496), (-34820016645927/140737488355328)), (42362581/1125899906842624), by norm_num⟩
  | 6 => ⟨((-784074243410195/18014398509481984), (-592748951909487/9007199254740992)), (257839041/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1090300747/16777216)), (1/8388608), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-1109294219/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1345423371985057/18014398509481984), (24668460600139/2251799813685248)), (115346889/9007199254740992), by norm_num⟩
  | 1 => ⟨((960952811/4294967296), (-70476631/2147483648)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((-1439378675/4294967296), (105564559/2147483648)), (63/1073741824), by norm_num⟩
  | 3 => ⟨((718665525/2147483648), (-210828771/4294967296)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-538232377/2147483648), (78948319/2147483648)), (3/67108864), by norm_num⟩
  | 5 => ⟨((644960041/4294967296), (-94603211/4294967296)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((-1288085073/17179869184), (94468631/8589934592)), (117/8589934592), by norm_num⟩
  | 7 => ⟨((1102502293/34359738368), (-40428961/8589934592)), (101/17179869184), by norm_num⟩
  | 8 => ⟨((-1651400851/137438953472), (242228687/137438953472)), (305/137438953472), by norm_num⟩
  | 9 => ⟨((1099367739/274877906944), (-80628033/137438953472)), (205/274877906944), by norm_num⟩
  | 10 => ⟨((-1317364567/1099511627776), (193232001/1099511627776)), (31/137438953472), by norm_num⟩
  | 11 => ⟨((358770141/1099511627776), (-105249335/2199023255552)), (17/274877906944), by norm_num⟩
  | 12 => ⟨((-716519527/8796093022208), (52549805/4398046511104)), (137/8796093022208), by norm_num⟩
  | 13 => ⟨((660461745/35184372088832), (-193754027/70368744177664)), (255/70368744177664), by norm_num⟩
  | 14 => ⟨((-565304733/140737488355328), (82919313/140737488355328)), (55/70368744177664), by norm_num⟩
  | 15 => ⟨((903200871/1125899906842624), (-264964333/2251799813685248)), (177/1125899906842624), by norm_num⟩
  | 16 => ⟨((-84554625/562949953421312), (198440551/9007199254740992)), (267/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (243910001949/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888986514352829/316912650057057350374175801344), (4614595683293/633825300114114700748351602688)), (92655/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888846243341115/39614081257132168796771975168), (5190230382009/39614081257132168796771975168)), (52133/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888564797147993/2475880078570760549798248448), (1378290829719/618970019642690137449562112)), (110817/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885115217681121/77371252455336267181195264), (5511525038455/154742504910672534362390528)), (110855/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548652540242291/9671406556917033397649408), (5165314435113/9671406556917033397649408)), (103967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78624985062253/37778931862957161709568), (282369392123/37778931862957161709568)), (22753/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471627207997719/18889465931478580854784), (7338342881401/75557863725914323419136)), (147969/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296575982735809/4722366482869645213696), (343806526839/295147905179352825856)), (27761/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810060810562539/295147905179352825856), (1889777405849/147573952589676412928)), (152793/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821813923567657/73786976294838206464), (9441939093227/73786976294838206464)), (191153/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910392530840935/4611686018427387904), (10612632969093/9223372036854775808)), (215271/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796014568396691/576460752303423488), (10600704686921/1152921504606846976)), (215549/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192863661444369/144115188075855872), (9262207405751/144115188075855872)), (188921/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489051856193571/36028797018963968), (13866518044873/36028797018963968)), (142005/18014398509481984), by norm_num⟩
  | 3 => ⟨((371502132994685/2251799813685248), (8643158369373/4503599627370496)), (356117/9007199254740992), by norm_num⟩
  | 2 => ⟨((555349628881979/1125899906842624), (17216184747069/2251799813685248)), (22361/140737488355328), by norm_num⟩
  | 1 => ⟨((137884534464413/140737488355328), (12824673806081/562949953421312)), (67603/140737488355328), by norm_num⟩
  | 0 => ⟨((540082815012847/562949953421312), (50601385159913/1125899906842624)), (137295/140737488355328), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540082815012847/562949953421312), (50601385159913/1125899906842624)), (523738861620855287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1034014907571559/1125899906842624), (97091893780697/1125899906842624)), (2206217/1125899906842624), by norm_num⟩
  | 2 => ⟨((941255956059359/1125899906842624), (356672791119177/2251799813685248)), (8865681/2251799813685248), by norm_num⟩
  | 3 => ⟨((1517291012540113/2251799813685248), (149089802283893/562949953421312)), (4408007/562949953421312), by norm_num⟩
  | 4 => ⟨((216107988217273/562949953421312), (803668658970243/2251799813685248)), (33100581/2251799813685248), by norm_num⟩
  | 5 => ⟨((5626570749875/281474976710656), (1234065060510637/4503599627370496)), (49040861/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1345423371985057/18014398509481984), (24668460600139/2251799813685248)), (115346889/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1109294219/16777216)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22027651/8388608), (-563680401/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-222492143314745/9007199254740992), (1225496406905795/18014398509481984)), (229620239/9007199254740992), by norm_num⟩
  | 1 => ⟨((161500531/2147483648), (-55596997/268435456)), (335/4294967296), by norm_num⟩
  | 2 => ⟨((-245845995/2147483648), (1354130439/4294967296)), (1/8388608), by norm_num⟩
  | 3 => ⟨((498989099/4294967296), (-1374226835/4294967296)), (261/2147483648), by norm_num⟩
  | 4 => ⟨((-379795877/4294967296), (1045966109/4294967296)), (399/4294967296), by norm_num⟩
  | 5 => ⟨((115629707/2147483648), (-1273786915/8589934592)), (61/1073741824), by norm_num⟩
  | 6 => ⟨((-469382983/17179869184), (323172737/4294967296)), (497/17179869184), by norm_num⟩
  | 7 => ⟨((204149575/17179869184), (-562232371/17179869184)), (217/17179869184), by norm_num⟩
  | 8 => ⟨((-310768981/68719476736), (427932267/34359738368)), (83/17179869184), by norm_num⟩
  | 9 => ⟨((105127015/68719476736), (-579044173/137438953472)), (451/274877906944), by norm_num⟩
  | 10 => ⟨((-256049245/549755813888), (705165191/549755813888)), (551/1099511627776), by norm_num⟩
  | 11 => ⟨((566943761/4398046511104), (-390343863/1099511627776)), (153/1099511627776), by norm_num⟩
  | 12 => ⟨((-143839417/4398046511104), (396136883/4398046511104)), (39/1099511627776), by norm_num⟩
  | 13 => ⟨((134745333/17592186044416), (-185545789/8796093022208)), (587/70368744177664), by norm_num⟩
  | 14 => ⟨((-468840217/281474976710656), (1291196155/281474976710656)), (513/281474976710656), by norm_num⟩
  | 15 => ⟨((380638549/1125899906842624), (-262071711/281474976710656)), (419/1125899906842624), by norm_num⟩
  | 16 => ⟨((-289715651/4503599627370496), (797883205/4503599627370496)), (321/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (2499839728723/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777914946559819/633825300114114700748351602688), (1477869359721/316912650057057350374175801344)), (92491/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888781287707555/39614081257132168796771975168), (415555660685/4951760157141521099596496896)), (104071/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888496295931417/2475880078570760549798248448), (441409568595/309485009821345068724781056)), (221195/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442540627998237/38685626227668133590597632), (1765106025571/77371252455336267181195264)), (55311/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548589475573065/9671406556917033397649408), (1654221571729/4835703278458516698824704)), (51867/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157243149045973/75557863725914323419136), (1446878758463/302231454903657293676544)), (90793/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235802663266827/9444732965739290427392), (2350118835559/37778931862957161709568)), (295175/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81031958866131/295147905179352825856), (3523325639995/4722366482869645213696)), (221467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405008592128173/147573952589676412928), (4841563933543/590295810358705651712)), (304655/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821707296992777/73786976294838206464), (3023722307553/36893488147419103232)), (190513/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455167113665833/2305843009213693952), (6797178286359/9223372036854775808)), (428941/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591916705618745/1152921504606846976), (1697359822271/288230376151711744)), (429299/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149096246203255/18014398509481984), (5932062809351/144115188075855872)), (47005/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488920658518907/36028797018963968), (8880725564269/36028797018963968)), (564867/36028797018963968), by norm_num⟩
  | 3 => ⟨((371465202663987/2251799813685248), (11070566857497/9007199254740992)), (353749/4503599627370496), by norm_num⟩
  | 2 => ⟨((555287905885147/1125899906842624), (22050333290947/4503599627370496)), (88703/281474976710656), by norm_num⟩
  | 1 => ⟨((17233614255173/17592186044416), (32849267125801/2251799813685248)), (534885/562949953421312), by norm_num⟩
  | 0 => ⟨((2160307281588493/2251799813685248), (64798202156915/2251799813685248)), (2160971/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160307281588493/2251799813685248), (64798202156915/2251799813685248)), (8243450169089889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2070667523615509/2251799813685248), (124330792730933/2251799813685248)), (8541415/2251799813685248), by norm_num⟩
  | 2 => ⟨((1897240519059765/2251799813685248), (228659522155285/2251799813685248)), (8325959/1125899906842624), by norm_num⟩
  | 3 => ⟨((1575289414508189/2251799813685248), (385311436536507/2251799813685248)), (31441795/2251799813685248), by norm_num⟩
  | 4 => ⟨((1036092028321767/2251799813685248), (269551948435211/1125899906842624)), (6843949/281474976710656), by norm_num⟩
  | 5 => ⟨((347656871971153/2251799813685248), (15503189009909/70368744177664)), (19150123/562949953421312), by norm_num⟩
  | 6 => ⟨((-222492143314745/9007199254740992), (1225496406905795/18014398509481984)), (229620239/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-563680401/8388608)), (1/8388608), by norm_num⟩, -11, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile021Terms2
