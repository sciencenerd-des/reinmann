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
namespace Reinmann.XiBand97.Tile032Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63841/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63841/2560))
  have he : value ((69/80), (63841/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1160018897/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((8507071378985/2251799813685248), (619228826478641/1125899906842624)), (97118821/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2811743/1073741824), (-818665915/2147483648)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((7795807/8589934592), (567455971/4294967296)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((-14409711/68719476736), (-2097762701/68719476736)), (43/17179869184), by norm_num⟩
  | 4 => ⟨((9988051/274877906944), (727029151/137438953472)), (121/274877906944), by norm_num⟩
  | 5 => ⟨((-11077103/2199023255552), (-403150565/549755813888)), (17/274877906944), by norm_num⟩
  | 6 => ⟨((10237417/17592186044416), (1490360947/17592186044416)), (1/137438953472), by norm_num⟩
  | 7 => ⟨((-2027439/35184372088832), (-590308279/70368744177664)), (103/140737488355328), by norm_num⟩
  | 8 => ⟨((11242509/2251799813685248), (1636682077/2251799813685248)), (145/2251799813685248), by norm_num⟩
  | 9 => ⟨((-13853713/36028797018963968), (-504205141/9007199254740992)), (181/36028797018963968), by norm_num⟩
  | 10 => ⟨((3841065/144115188075855872), (559181395/144115188075855872)), (51/144115188075855872), by norm_num⟩
  | 11 => ⟨((-484077/288230376151711744), (-140943639/576460752303423488)), (105/4611686018427387904), by norm_num⟩
  | 12 => ⟨((14316229/147573952589676412928), (2084153301/147573952589676412928)), (197/147573952589676412928), by norm_num⟩
  | 13 => ⟨((-12213235/2361183241434822606848), (-1777999981/2361183241434822606848)), (85/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((1209367/4722366482869645213696), (88029691/2361183241434822606848)), (137/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-14306463/1208925819614629174706176), (-2082731763/1208925819614629174706176)), (205/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((2479121/4835703278458516698824704), (1443639649/19342813113834066795298816)), (145/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (2037189986031/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445261328140625/158456325028528675187087900672), (1208392186501/316912650057057350374175801344)), (11555/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946151259824633/19807040628566084398385987584), (679682769987/9903520314283042199192993792)), (13001/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((473059275866995/618970019642690137449562112), (1444237450781/1237940039285380274899124224)), (55263/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773902755282245/154742504910672534362390528), (2888275892083/154742504910672534362390528)), (55273/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552095354069439/9671406556917033397649408), (1353773588361/4835703278458516698824704)), (51829/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261012236380555/604462909807314587353088), (2368892279937/604462909807314587353088)), (45361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891404128092627/75557863725914323419136), (3849053334373/75557863725914323419136)), (73731/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650123737078033/2361183241434822606848), (1443221449631/2361183241434822606848)), (13829/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625169950812177/590295810358705651712), (1984147418401/295147905179352825856)), (76087/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828124374870707/73786976294838206464), (2479761064813/36893488147419103232)), (47575/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827884366340069/9223372036854775808), (5578298261851/9223372036854775808)), (107103/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799564244860141/576460752303423488), (5576842627701/1152921504606846976)), (107175/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199075635270241/144115188075855872), (4878099069979/144115188075855872)), (23465/36028797018963968), by norm_num⟩
  | 4 => ⟨((749184930659335/18014398509481984), (457116909179/2251799813685248)), (17619/4503599627370496), by norm_num⟩
  | 3 => ⟨((1497656036070291/9007199254740992), (4568298994871/4503599627370496)), (44119/2251799813685248), by norm_num⟩
  | 2 => ⟨((561173299459015/1125899906842624), (9127980531963/2251799813685248)), (176905/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120546324295325/1125899906842624), (6835201073345/562949953421312)), (266431/1125899906842624), by norm_num⟩
  | 0 => ⟨((557549279137959/562949953421312), (27254380269387/1125899906842624)), (537161/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557549279137959/562949953421312), (27254380269387/1125899906842624)), (2049106602195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((275935273169639/281474976710656), (26992914699073/562949953421312)), (545011/562949953421312), by norm_num⟩
  | 2 => ⟨((1079429816545249/1125899906842624), (52923335339965/562949953421312)), (2241671/1125899906842624), by norm_num⟩
  | 3 => ⟨((512463498815345/562949953421312), (202955967257101/1125899906842624)), (4719781/1125899906842624), by norm_num⟩
  | 4 => ⟨((896424468723285/1125899906842624), (369508957071313/1125899906842624)), (5147295/562949953421312), by norm_num⟩
  | 5 => ⟨((592450496457081/1125899906842624), (294197440214769/562949953421312)), (23149955/1125899906842624), by norm_num⟩
  | 6 => ⟨((8507071378985/2251799813685248), (619228826478641/1125899906842624)), (97118821/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1160018897/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1838586453/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-279035986016631/1125899906842624), (-671326482077443/2251799813685248)), (77796115/2251799813685248), by norm_num⟩
  | 1 => ⟨((584702231/2147483648), (21980033/67108864)), (21/536870912), by norm_num⟩
  | 2 => ⟨((-20073783/134217728), (-193180275/1073741824)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((117617625/2147483648), (1131894529/17179869184)), (71/8589934592), by norm_num⟩
  | 4 => ⟨((-516864673/34359738368), (-155439155/8589934592)), (5/2147483648), by norm_num⟩
  | 5 => ⟨((454267105/137438953472), (546455571/137438953472)), (9/17179869184), by norm_num⟩
  | 6 => ⟨((-665417899/1099511627776), (-400228537/549755813888)), (27/274877906944), by norm_num⟩
  | 7 => ⟨((208867509/2199023255552), (251254851/2199023255552)), (69/4398046511104), by norm_num⟩
  | 8 => ⟨((-917857649/70368744177664), (-276031667/17592186044416)), (77/35184372088832), by norm_num⟩
  | 9 => ⟨((112041077/70368744177664), (269557139/140737488355328)), (153/562949953421312), by norm_num⟩
  | 10 => ⟨((-393887053/2251799813685248), (-473822057/2251799813685248)), (137/4503599627370496), by norm_num⟩
  | 11 => ⟨((157356057/9007199254740992), (757158887/36028797018963968)), (7/2251799813685248), by norm_num⟩
  | 12 => ⟨((-460995461/288230376151711744), (-138637343/72057594037927936)), (167/576460752303423488), by norm_num⟩
  | 13 => ⟨((311664787/2305843009213693952), (749827391/4611686018427387904)), (115/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-782625749/73786976294838206464), (-235362739/18446744073709551616)), (147/73786976294838206464), by norm_num⟩
  | 15 => ⟨((917122417/1180591620717411303424), (1103242229/1180591620717411303424)), (175/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-503780979/9444732965739290427392), (-606017735/9444732965739290427392)), (49/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-2949545082795/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890250817075037/316912650057057350374175801344), (-3497126093277/633825300114114700748351602688)), (723/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((472922680772243/9903520314283042199192993792), (-3933918841087/39614081257132168796771975168)), (52067/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945793434489089/1237940039285380274899124224), (-4179382819657/2475880078570760549798248448)), (27667/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443313073790397/38685626227668133590597632), (-1044731508057/38685626227668133590597632)), (13837/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551485308083643/9671406556917033397649408), (-122414304879/302231454903657293676544)), (811/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1260478206644087/604462909807314587353088), (-3427115067303/604462909807314587353088)), (5679/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1890535880973471/75557863725914323419136), (-5568151580341/75557863725914323419136)), (73855/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324898974095501/1180591620717411303424), (-4175316932831/4722366482869645213696)), (55417/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812136697079811/295147905179352825856), (-5739765781129/590295810358705651712)), (38119/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913501362049089/36893488147419103232), (-7172764236927/73786976294838206464)), (47679/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456655299389407/2305843009213693952), (-4033343682825/4611686018427387904)), (53681/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597863683462001/1152921504606846976), (-8063345681397/1152921504606846976)), (26867/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197967090525835/144115188075855872), (-7051666453511/144115188075855872)), (11769/18014398509481984), by norm_num⟩
  | 4 => ⟨((1496703372894451/36028797018963968), (-5284986799593/18014398509481984)), (141465/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495566517015841/9007199254740992), (-6599643643199/4503599627370496)), (177245/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120247499601563/2251799813685248), (-13179499656183/2251799813685248)), (44467/562949953421312), by norm_num⟩
  | 1 => ⟨((1117373838481805/1125899906842624), (-4929929388507/281474976710656)), (268361/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108658922037133/1125899906842624), (-39240933136071/1125899906842624)), (542969/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108658922037133/1125899906842624), (-39240933136071/1125899906842624)), (2071262363914107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((545157143685037/562949953421312), (-38640033955033/562949953421312)), (553579/562949953421312), by norm_num⟩
  | 2 => ⟨((1050549013423499/1125899906842624), (-74837524773907/562949953421312)), (1148159/562949953421312), by norm_num⟩
  | 3 => ⟨((960343457332821/1125899906842624), (-69829020626497/281474976710656)), (4895811/1125899906842624), by norm_num⟩
  | 4 => ⟨((749837598319893/1125899906842624), (-238244421846243/562949953421312)), (5390479/562949953421312), by norm_num⟩
  | 5 => ⟨((595461112756977/2251799813685248), (-317336601601245/562949953421312)), (1467823/70368744177664), by norm_num⟩
  | 6 => ⟨((-279035986016631/1125899906842624), (-671326482077443/2251799813685248)), (77796115/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1838586453/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1160018897/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1362203672443687/4503599627370496), (9357534883415/2251799813685248)), (108577247/2251799813685248), by norm_num⟩
  | 1 => ⟨((900466571/2147483648), (-24742695/4294967296)), (145/2147483648), by norm_num⟩
  | 2 => ⟨((-624155865/2147483648), (17150329/4294967296)), (203/4294967296), by norm_num⟩
  | 3 => ⟨((72105313/536870912), (-7925135/4294967296)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((-1599347021/34359738368), (5493285/8589934592)), (265/34359738368), by norm_num⟩
  | 5 => ⟨((1773732605/137438953472), (-761531/4294967296)), (37/17179869184), by norm_num⟩
  | 6 => ⟨((-819638503/274877906944), (22521731/549755813888)), (69/137438953472), by norm_num⟩
  | 7 => ⟨((649291563/1099511627776), (-17840999/2199023255552)), (221/2199023255552), by norm_num⟩
  | 8 => ⟨((-1800218465/17592186044416), (6183219/4398046511104)), (309/17592186044416), by norm_num⟩
  | 9 => ⟨((277292523/17592186044416), (-15238687/70368744177664)), (3/1099511627776), by norm_num⟩
  | 10 => ⟨((-1230108995/562949953421312), (16900245/562949953421312)), (215/562949953421312), by norm_num⟩
  | 11 => ⟨((620106605/2251799813685248), (-17039065/4503599627370496)), (109/2251799813685248), by norm_num⟩
  | 12 => ⟨((-573100193/18014398509481984), (984215/2251799813685248)), (203/36028797018963968), by norm_num⟩
  | 13 => ⟨((977828389/288230376151711744), (-26868415/576460752303423488)), (349/576460752303423488), by norm_num⟩
  | 14 => ⟨((-774604561/2305843009213693952), (1330269/288230376151711744)), (139/2305843009213693952), by norm_num⟩
  | 15 => ⟨((1145418597/36893488147419103232), (-15736699/36893488147419103232)), (207/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-793943671/295147905179352825856), (21815697/590295810358705651712)), (289/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (4074379972063/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890056286878127/316912650057057350374175801344), (4828811275181/633825300114114700748351602688)), (92675/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891252726651493/39614081257132168796771975168), (5431796651003/39614081257132168796771975168)), (52145/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891121111431511/2475880078570760549798248448), (1442643809377/618970019642690137449562112)), (110843/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443196525791419/38685626227668133590597632), (2884888818125/77371252455336267181195264)), (110883/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775523895856229/4835703278458516698824704), (5408318888233/9671406556917033397649408)), (103995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260094918699653/604462909807314587353088), (591428895355/75557863725914323419136)), (45519/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118119510875447/4722366482869645213696), (480436589369/4722366482869645213696)), (148015/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299127360650511/4722366482869645213696), (2881923587747/2361183241434822606848)), (111081/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202953491356025/73786976294838206464), (1980756791525/147573952589676412928)), (9553/36893488147419103232), by norm_num⟩
  | 8 => ⟨((228274257089935/9223372036854775808), (9900388391379/73786976294838206464)), (95615/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825708922072833/9223372036854775808), (5566632789013/4611686018427387904)), (107683/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596948256466531/1152921504606846976), (11127422695389/1152921504606846976)), (26957/144115188075855872), by norm_num⟩
  | 5 => ⟨((598581276214849/72057594037927936), (9729916569177/144115188075855872)), (94513/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495489501740159/36028797018963968), (14581705699537/36028797018963968)), (284195/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494036849681707/9007199254740992), (18204057919685/9007199254740992)), (356391/9007199254740992), by norm_num⟩
  | 2 => ⟨((139837425870085/281474976710656), (9084695259359/1125899906842624)), (89529/562949953421312), by norm_num⟩
  | 1 => ⟨((278751467963801/281474976710656), (27167222187471/1125899906842624)), (541493/1125899906842624), by norm_num⟩
  | 0 => ⟨((275935273169639/281474976710656), (53985829398147/1125899906842624)), (1100313/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((275935273169639/281474976710656), (53985829398147/1125899906842624)), (4197360996726607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1079429816545249/1125899906842624), (26461667669983/281474976710656)), (2262835/1125899906842624), by norm_num⟩
  | 2 => ⟨((512463498815345/562949953421312), (202955967257105/1125899906842624)), (4764341/1125899906842624), by norm_num⟩
  | 3 => ⟨((896424468723283/1125899906842624), (46188619633915/140737488355328)), (10391783/1125899906842624), by norm_num⟩
  | 4 => ⟨((296225248228537/562949953421312), (147098720107387/281474976710656)), (11684259/562949953421312), by norm_num⟩
  | 5 => ⟨((8507071378949/2251799813685248), (154807206619661/281474976710656)), (49017869/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1362203672443687/4503599627370496), (9357534883415/2251799813685248)), (108577247/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1160018897/33554432)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-673370117/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-856122463878073/4503599627370496), (-91004274714093/562949953421312)), (12637193/281474976710656), by norm_num⟩
  | 1 => ⟨((657022453/2147483648), (139680605/536870912)), (157/2147483648), by norm_num⟩
  | 2 => ⟨((-1057436845/4294967296), (-899229045/4294967296)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((567292983/4294967296), (964835545/8589934592)), (69/2147483648), by norm_num⟩
  | 4 => ⟨((-456511417/8589934592), (-776421453/17179869184)), (7/536870912), by norm_num⟩
  | 5 => ⟨((293890713/17179869184), (499840849/34359738368)), (73/17179869184), by norm_num⟩
  | 6 => ⟨((-630665141/137438953472), (-268154271/68719476736)), (79/68719476736), by norm_num⟩
  | 7 => ⟨((1160018729/1099511627776), (30826975/34359738368)), (293/1099511627776), by norm_num⟩
  | 8 => ⟨((-933489061/4398046511104), (-793825637/4398046511104)), (119/2199023255552), by norm_num⟩
  | 9 => ⟨((667730083/17592186044416), (283914017/8796093022208)), (43/4398046511104), by norm_num⟩
  | 10 => ⟨((-859736089/140737488355328), (-731107173/140737488355328)), (223/140737488355328), by norm_num⟩
  | 11 => ⟨((503160675/562949953421312), (855761165/1125899906842624)), (263/1125899906842624), by norm_num⟩
  | 12 => ⟨((-1079741155/9007199254740992), (-918196309/9007199254740992)), (71/2251799813685248), by norm_num⟩
  | 13 => ⟨((1069400831/72057594037927936), (909403047/72057594037927936)), (283/72057594037927936), by norm_num⟩
  | 14 => ⟨((-983505281/576460752303423488), (-418179355/288230376151711744)), (263/576460752303423488), by norm_num⟩
  | 15 => ⟨((422104183/2305843009213693952), (358951311/2305843009213693952)), (227/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-679350475/36893488147419103232), (-577709849/36893488147419103232)), (23/4611686018427387904), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-3174301483433/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779820388608587/633825300114114700748351602688), (-1880438404713/316912650057057350374175801344)), (46285/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890924349529423/39614081257132168796771975168), (-4230448045999/39614081257132168796771975168)), (104165/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945386309451717/1237940039285380274899124224), (-4494212313535/2475880078570760549798248448)), (110703/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221554758720269/19342813113834066795298816), (-1123373417661/38685626227668133590597632)), (55367/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550721998084381/9671406556917033397649408), (-2105943377709/4835703278458516698824704)), (103845/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629905168407235/302231454903657293676544), (-3684637347027/604462909807314587353088)), (45449/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889450642264667/75557863725914323419136), (-5986104000011/75557863725914323419136)), (147771/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298782011121359/4722366482869645213696), (-2244162632997/2361183241434822606848)), (55441/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811577186739851/295147905179352825856), (-1542352884213/147573952589676412928)), (76275/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912802028161397/36893488147419103232), (-3854355423427/36893488147419103232)), (190819/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912523923060595/4611686018427387904), (-8668101010343/9223372036854775808)), (53713/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798145260549915/576460752303423488), (-2165713151673/288230376151711744)), (215079/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598295394327015/72057594037927936), (-7574091529999/144115188075855872)), (188449/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494639356683871/36028797018963968), (-5674664096841/18014398509481984)), (283183/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492987274737277/9007199254740992), (-14165994138131/9007199254740992)), (44359/1125899906842624), by norm_num⟩
  | 2 => ⟨((279417363028639/562949953421312), (-3533748686811/562949953421312)), (356215/2251799813685248), by norm_num⟩
  | 1 => ⟨((556754925644735/562949953421312), (-10562496676597/562949953421312)), (537683/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100943863826803/1125899906842624), (-2621249633571/70368744177664)), (1088847/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100943863826803/1125899906842624), (-2621249633571/70368744177664)), (4153621677878951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((537489354441719/562949953421312), (-20505188300307/281474976710656)), (2210545/1125899906842624), by norm_num⟩
  | 2 => ⟨((1020385394487461/1125899906842624), (-611806184727/4398046511104)), (2271605/562949953421312), by norm_num⟩
  | 3 => ⟨((112871465766757/140737488355328), (-70972202496765/281474976710656)), (37105/4398046511104), by norm_num⟩
  | 4 => ⟨((1305204978339787/2251799813685248), (-910715303292017/2251799813685248)), (40052747/2251799813685248), by norm_num⟩
  | 5 => ⟨((388203989768551/2251799813685248), (-1055751173335091/2251799813685248)), (39414559/1125899906842624), by norm_num⟩
  | 6 => ⟨((-856122463878073/4503599627370496), (-91004274714093/562949953421312)), (12637193/281474976710656), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-673370117/16777216)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1499302675/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((91777903195145/562949953421312), (-309467796707339/2251799813685248)), (51412611/4503599627370496), by norm_num⟩
  | 1 => ⟨((-627303799/2147483648), (528804641/2147483648)), (45/2147483648), by norm_num⟩
  | 2 => ⟨((561988761/2147483648), (-947490723/4294967296)), (41/2147483648), by norm_num⟩
  | 3 => ⟨((-671299123/4294967296), (565891825/4294967296)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((37587705/536870912), (-253485509/4294967296)), (23/4294967296), by norm_num⟩
  | 5 => ⟨((-431028009/17179869184), (363348049/17179869184)), (17/8589934592), by norm_num⟩
  | 6 => ⟨((257432839/34359738368), (-868043077/137438953472)), (83/137438953472), by norm_num⟩
  | 7 => ⟨((-65893961/34359738368), (444378401/274877906944)), (87/549755813888), by norm_num⟩
  | 8 => ⟨((944529029/2199023255552), (-99527401/274877906944)), (5/137438953472), by norm_num⟩
  | 9 => ⟨((-752163925/8796093022208), (634059247/8796093022208)), (65/8796093022208), by norm_num⟩
  | 10 => ⟨((269539367/17592186044416), (-56804083/4398046511104)), (95/70368744177664), by norm_num⟩
  | 11 => ⟨((-351236155/140737488355328), (592170203/281474976710656)), (63/281474976710656), by norm_num⟩
  | 12 => ⟨((839107609/2251799813685248), (-353675523/1125899906842624)), (77/2251799813685248), by norm_num⟩
  | 13 => ⟨((-925217849/18014398509481984), (194985067/4503599627370496)), (87/18014398509481984), by norm_num⟩
  | 14 => ⟨((473647955/72057594037927936), (-798551635/144115188075855872)), (91/144115188075855872), by norm_num⟩
  | 15 => ⟨((-226310189/288230376151711744), (763099975/1152921504606846976)), (89/1152921504606846976), by norm_num⟩
  | 16 => ⟨((25343339/288230376151711744), (-683645803/9223372036854775808)), (41/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-228088774191/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222448082433551/79228162514264337593543950336), (-1080667875135/633825300114114700748351602688)), (23077/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890659594892381/39614081257132168796771975168), (-151948131749/4951760157141521099596496896)), (25963/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890491871383075/2475880078570760549798248448), (-1291355452025/2475880078570760549798248448)), (6897/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772157945548279/154742504910672534362390528), (-645563190215/77371252455336267181195264)), (13795/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550460043627227/9671406556917033397649408), (-1210187646713/9671406556917033397649408)), (6467/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((39361930886077/18889465931478580854784), (-1058670916265/604462909807314587353088)), (22637/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889080491041421/75557863725914323419136), (-429971056803/18889465931478580854784)), (36789/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298505482080799/4722366482869645213696), (-1289514288287/4722366482869645213696)), (6899/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622775906953477/590295810358705651712), (-221554275389/73786976294838206464)), (75901/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825133612408631/73786976294838206464), (-553642814773/18446744073709551616)), (94895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824522222244881/9223372036854775808), (-2490057543525/9223372036854775808)), (106783/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99735588999067/72057594037927936), (-2488389662885/1152921504606846976)), (1669/18014398509481984), by norm_num⟩
  | 5 => ⟨((598069957105439/72057594037927936), (-2175465995121/144115188075855872)), (93501/144115188075855872), by norm_num⟩
  | 4 => ⟨((746986599203423/18014398509481984), (-3259452584785/36028797018963968)), (140323/36028797018963968), by norm_num⟩
  | 3 => ⟨((746086152786253/4503599627370496), (-4067767411731/9007199254740992)), (175533/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233761993085813/4503599627370496), (-8115921407841/4503599627370496)), (87863/1125899906842624), by norm_num⟩
  | 1 => ⟨((2224786348410107/2251799813685248), (-12124958807713/2251799813685248)), (528145/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197945741672591/2251799813685248), (-24054884511289/2251799813685248)), (1060177/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197945741672591/2251799813685248), (-24054884511289/2251799813685248)), (4044254311568450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1072561338825789/1125899906842624), (-23479587597747/1125899906842624)), (261537/281474976710656), by norm_num⟩
  | 2 => ⟨((127657499516821/140737488355328), (-89469046958317/2251799813685248)), (4073617/2251799813685248), by norm_num⟩
  | 3 => ⟨((1849135603950939/2251799813685248), (-10144236400979/140737488355328)), (1928437/562949953421312), by norm_num⟩
  | 4 => ⟨((1506776332845267/2251799813685248), (-133284094544773/1125899906842624)), (13780771/2251799813685248), by norm_num⟩
  | 5 => ⟨((976692645776889/2251799813685248), (-178372267360749/1125899906842624)), (10852677/1125899906842624), by norm_num⟩
  | 6 => ⟨((91777903195145/562949953421312), (-309467796707339/2251799813685248)), (51412611/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1499302675/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1628292381/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-280816929471875/9007199254740992), (1657869100282249/9007199254740992)), (281108785/9007199254740992), by norm_num⟩
  | 1 => ⟨((260565049/4294967296), (-1538307337/4294967296)), (131/2147483648), by norm_num⟩
  | 2 => ⟨((-253518087/4294967296), (748351965/2147483648)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((41110285/1073741824), (-970817123/4294967296)), (169/4294967296), by norm_num⟩
  | 4 => ⟨((-79996921/4294967296), (472280723/4294967296)), (83/4294967296), by norm_num⟩
  | 5 => ⟨((249066913/34359738368), (-1470425363/34359738368)), (65/8589934592), by norm_num⟩
  | 6 => ⟨((-161553945/68719476736), (953771879/68719476736)), (85/34359738368), by norm_num⟩
  | 7 => ⟨((44909923/68719476736), (-66284085/17179869184)), (191/274877906944), by norm_num⟩
  | 8 => ⟨((-87390675/549755813888), (515931495/549755813888)), (187/1099511627776), by norm_num⟩
  | 9 => ⟨((37789867/1099511627776), (-892405629/4398046511104)), (325/8796093022208), by norm_num⟩
  | 10 => ⟨((-117657097/17592186044416), (1389232937/35184372088832)), (255/35184372088832), by norm_num⟩
  | 11 => ⟨((20813649/17592186044416), (-983026353/140737488355328)), (91/70368744177664), by norm_num⟩
  | 12 => ⟨((-216007951/1125899906842624), (318813493/281474976710656)), (119/562949953421312), by norm_num⟩
  | 13 => ⟨((129332943/4503599627370496), (-1527095167/9007199254740992)), (287/9007199254740992), by norm_num⟩
  | 14 => ⟨((-17976449/4503599627370496), (424512855/18014398509481984)), (321/72057594037927936), by norm_num⟩
  | 15 => ⟨((74625183/144115188075855872), (-440567399/144115188075855872)), (335/576460752303423488), by norm_num⟩
  | 16 => ⟨((-145213901/2305843009213693952), (857304573/2305843009213693952)), (41/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (2264704954981/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779376322082761/633825300114114700748351602688), (1340956690169/316912650057057350374175801344)), (5779/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945212531443429/19807040628566084398385987584), (1508350145661/19807040628566084398385987584)), (104039/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890242484339199/2475880078570760549798248448), (1602347273053/1237940039285380274899124224)), (110561/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442977084317743/38685626227668133590597632), (1602038216141/77371252455336267181195264)), (110583/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550225800942991/9671406556917033397649408), (375395627277/1208925819614629174706176)), (103695/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39355518476087/18889465931478580854784), (2627112876321/604462909807314587353088)), (90757/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236093325731495/9444732965739290427392), (4267827719287/75557863725914323419136)), (36881/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324563670906977/1180591620717411303424), (1599897091505/2361183241434822606848)), (110681/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25350475543427/9223372036854775808), (4397968004019/590295810358705651712)), (152249/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228087604600677/9223372036854775808), (5494837362411/73786976294838206464)), (190405/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824034065268159/9223372036854775808), (3089043643327/4611686018427387904)), (107167/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398819916018825/288230376151711744), (3086791717761/576460752303423488)), (6703/36028797018963968), by norm_num⟩
  | 5 => ⟨((1195709574555893/144115188075855872), (5396821535767/144115188075855872)), (93933/72057594037927936), by norm_num⟩
  | 4 => ⟨((186665512295039/4503599627370496), (8085111519211/36028797018963968)), (282163/36028797018963968), by norm_num⟩
  | 3 => ⟨((372838666757955/2251799813685248), (2522173532373/2251799813685248)), (353341/9007199254740992), by norm_num⟩
  | 2 => ⟨((558027001357579/1125899906842624), (5031091718083/1125899906842624)), (354299/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111129434698577/1125899906842624), (15027111178949/1125899906842624)), (66731/140737488355328), by norm_num⟩
  | 0 => ⟨((1096353230878401/1125899906842624), (7447560789461/281474976710656)), (538659/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096353230878401/1125899906842624), (7447560789461/281474976710656)), (2054821016551780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1066793718491703/1125899906842624), (116033864595819/2251799813685248)), (4310205/2251799813685248), by norm_num⟩
  | 2 => ⟨((503900420669765/562949953421312), (27485613314923/281474976710656)), (1076509/281474976710656), by norm_num⟩
  | 3 => ⟨((27854807149061/35184372088832), (393641019847911/2251799813685248)), (4274841/562949953421312), by norm_num⟩
  | 4 => ⟨((671261566275063/1125899906842624), (38954776093985/140737488355328)), (1032901/70368744177664), by norm_num⟩
  | 5 => ⟨((627895455103503/2251799813685248), (743194846527977/2251799813685248)), (28854805/1125899906842624), by norm_num⟩
  | 6 => ⟨((-280816929471875/9007199254740992), (1657869100282249/9007199254740992)), (281108785/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1628292381/33554432)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-870014173/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-30878597802171/9007199254740992), (-749121809949583/4503599627370496)), (241432065/9007199254740992), by norm_num⟩
  | 1 => ⟨((7654457/1073741824), (742795473/2147483648)), (121/2147483648), by norm_num⟩
  | 2 => ⟨((-3979249/536870912), (-386149941/1073741824)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((11032821/2147483648), (267658743/1073741824)), (89/2147483648), by norm_num⟩
  | 4 => ⟨((-11471053/4294967296), (-556580709/4294967296)), (187/8589934592), by norm_num⟩
  | 5 => ⟨((38165415/34359738368), (462950819/8589934592)), (157/17179869184), by norm_num⟩
  | 6 => ⟨((-13227125/34359738368), (-320893055/17179869184)), (55/17179869184), by norm_num⟩
  | 7 => ⟨((7858581/68719476736), (1525207655/274877906944)), (33/34359738368), by norm_num⟩
  | 8 => ⟨((-4085365/137438953472), (-1585790079/1099511627776)), (277/1099511627776), by norm_num⟩
  | 9 => ⟨((3775679/549755813888), (732790615/2199023255552)), (129/2199023255552), by norm_num⟩
  | 10 => ⟨((-6281043/4398046511104), (-1219036197/17592186044416)), (27/2199023255552), by norm_num⟩
  | 11 => ⟨((4749477/17592186044416), (460893547/35184372088832)), (329/140737488355328), by norm_num⟩
  | 12 => ⟨((-26336693/562949953421312), (-1277868251/562949953421312)), (115/281474976710656), by norm_num⟩
  | 13 => ⟨((8425479/1125899906842624), (1635232201/4503599627370496)), (297/4503599627370496), by norm_num⟩
  | 14 => ⟨((-10011595/9007199254740992), (-242883555/4503599627370496)), (89/9007199254740992), by norm_num⟩
  | 15 => ⟨((5551607/36028797018963968), (1077465929/144115188075855872)), (199/144115188075855872), by norm_num⟩
  | 16 => ⟨((-5772121/288230376151711744), (-560131853/576460752303423488)), (209/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-1036490222601/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779199302049769/633825300114114700748351602688), (-2454402699701/633825300114114700748351602688)), (46221/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890225982835267/39614081257132168796771975168), (-690190814881/9903520314283042199192993792)), (104013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890031045402827/2475880078570760549798248448), (-2932773767335/2475880078570760549798248448)), (110531/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771696992377643/154742504910672534362390528), (-2932169540707/154742504910672534362390528)), (110551/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775013882497953/4835703278458516698824704), (-2748267083975/9671406556917033397649408)), (6479/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259203409637405/604462909807314587353088), (-2404091984635/604462909807314587353088)), (90727/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118029085807149/4722366482869645213696), (-1952723286527/37778931862957161709568)), (147471/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81127745163481/295147905179352825856), (-2928032702001/4722366482869645213696)), (110639/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622140904249585/590295810358705651712), (-4024335678965/590295810358705651712)), (152185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824339322198741/73786976294838206464), (-5027856690891/73786976294838206464)), (95159/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823627908963491/9223372036854775808), (-1413204109707/2305843009213693952)), (107113/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797437095863299/576460752303423488), (-1412104001251/288230376151711744)), (107187/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195355554905555/144115188075855872), (-4937416938125/144115188075855872)), (5867/4503599627370496), by norm_num⟩
  | 4 => ⟨((1492794604205787/36028797018963968), (-7396239826593/36028797018963968)), (70487/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490695481677863/9007199254740992), (-576751203243/562949953421312)), (88255/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115398831929409/2251799813685248), (-18404273812781/4503599627370496)), (707793/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220313367337033/2251799813685248), (-13738633995683/1125899906842624)), (1066085/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188895123885673/2251799813685248), (-13609894444053/562949953421312)), (2149803/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2188895123885673/2251799813685248), (-13609894444053/562949953421312)), (8200847634322356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((531607890568389/562949953421312), (-52918792166399/1125899906842624)), (1070861/562949953421312), by norm_num⟩
  | 2 => ⟨((2003068641965091/2251799813685248), (-780821170915/8796093022208)), (4246293/1125899906842624), by norm_num⟩
  | 3 => ⟨((220508493934983/281474976710656), (-355621160097667/2251799813685248)), (16616769/2251799813685248), by norm_num⟩
  | 4 => ⟨((1325814714871655/2251799813685248), (-557189753355289/2251799813685248)), (31283763/2251799813685248), by norm_num⟩
  | 5 => ⟨((160685269193337/562949953421312), (-656124376140843/2251799813685248)), (52320341/2251799813685248), by norm_num⟩
  | 6 => ⟨((-30878597802171/9007199254740992), (-749121809949583/4503599627370496)), (241432065/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-870014173/16777216)), (1/16777216), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile032Terms0
