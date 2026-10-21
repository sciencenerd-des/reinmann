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
namespace Reinmann.XiBand58.Tile004Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2599/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2599/160))
  have he : value ((15/16), (2599/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-755599471/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((76625960907707/562949953421312), (567546951971659/1125899906842624)), (42221417/2251799813685248), by norm_num⟩
  | 1 => ⟨((-101305139/1073741824), (-750338687/2147483648)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((140438743/4294967296), (1040190291/8589934592)), (21/4294967296), by norm_num⟩
  | 3 => ⟨((-259585917/34359738368), (-961339957/34359738368)), (41/34359738368), by norm_num⟩
  | 4 => ⟨((359862493/274877906944), (666350081/137438953472)), (59/274877906944), by norm_num⟩
  | 5 => ⟨((-99775069/549755813888), (-11546967/17179869184)), (17/549755813888), by norm_num⟩
  | 6 => ⟨((368846975/17592186044416), (1365972927/17592186044416)), (65/17592186044416), by norm_num⟩
  | 7 => ⟨((-292188847/140737488355328), (-270520081/35184372088832)), (27/70368744177664), by norm_num⟩
  | 8 => ⟨((405059751/2251799813685248), (375020463/562949953421312)), (77/2251799813685248), by norm_num⟩
  | 9 => ⟨((-249569799/18014398509481984), (-57765417/1125899906842624)), (25/9007199254740992), by norm_num⟩
  | 10 => ⟨((69195441/72057594037927936), (128127795/36028797018963968)), (57/288230376151711744), by norm_num⟩
  | 11 => ⟨((-34881909/576460752303423488), (-1033441977/4611686018427387904)), (59/4611686018427387904), by norm_num⟩
  | 12 => ⟨((257901833/73786976294838206464), (477551595/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-440034285/2361183241434822606848), (-203700641/295147905179352825856)), (49/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((174290585/18889465931478580854784), (1290921371/37778931862957161709568)), (5/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((-128862963/302231454903657293676544), (-954451743/604462909807314587353088)), (61/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((178641999/9671406556917033397649408), (1323151069/19342813113834066795298816)), (87/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (425648253895/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780965918507257/633825300114114700748351602688), (2019668291295/633825300114114700748351602688)), (5775/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892213263738215/39614081257132168796771975168), (2271991053521/39614081257132168796771975168)), (25991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118258896539719/154742504910672534362390528), (2413830029651/2475880078570760549798248448)), (27619/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773808081460963/154742504910672534362390528), (2413649496271/154742504910672534362390528)), (27623/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552006687673443/9671406556917033397649408), (1131302289757/4835703278458516698824704)), (25901/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260934743580961/604462909807314587353088), (989793588249/302231454903657293676544)), (5667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236409796446131/9444732965739290427392), (804117365977/18889465931478580854784)), (36843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650076652424365/2361183241434822606848), (603009336679/1180591620717411303424)), (3455/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625040708595247/590295810358705651712), (1658019925949/295147905179352825856)), (297/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1827963182868923/73786976294838206464), (4144282514257/73786976294838206464)), (47537/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827703521230769/9223372036854775808), (2330631353855/4611686018427387904)), (209/36028797018963968), by norm_num⟩
  | 6 => ⟨((799474132114475/576460752303423488), (1164985920809/288230376151711744)), (26767/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198918634694431/144115188075855872), (2037983325521/72057594037927936)), (46877/144115188075855872), by norm_num⟩
  | 4 => ⟨((749067876529867/18014398509481984), (3055490705621/18014398509481984)), (70383/36028797018963968), by norm_num⟩
  | 3 => ⟨((187170729485367/1125899906842624), (477095676855/562949953421312)), (88097/9007199254740992), by norm_num⟩
  | 2 => ⟨((561030023793255/1125899906842624), (1906433761909/562949953421312)), (88277/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120125605947007/1125899906842624), (11419106577969/1125899906842624)), (132863/1125899906842624), by norm_num⟩
  | 0 => ⟨((278573368767193/281474976710656), (11380095149029/562949953421312)), (133761/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278573368767193/281474976710656), (11380095149029/562949953421312)), (510257723094749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1102346589404167/1125899906842624), (45051130009543/1125899906842624)), (540345/1125899906842624), by norm_num⟩
  | 2 => ⟨((269370836493335/281474976710656), (88217361442175/1125899906842624)), (1101325/1125899906842624), by norm_num⟩
  | 3 => ⟨((512118373481345/562949953421312), (168847580858607/1125899906842624)), (2280515/1125899906842624), by norm_num⟩
  | 4 => ⟨((906431737017241/1125899906842624), (307202968754331/1125899906842624)), (4833195/1125899906842624), by norm_num⟩
  | 5 => ⟨((322961581860345/562949953421312), (494641697530159/1125899906842624)), (10419637/1125899906842624), by norm_num⟩
  | 6 => ⟨((76625960907707/562949953421312), (567546951971659/1125899906842624)), (42221417/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-755599471/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-1197596827/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((215842372566171/1125899906842624), (1356440308862465/4503599627370496)), (101420385/4503599627370496), by norm_num⟩
  | 1 => ⟨((-226142009/1073741824), (-710583683/2147483648)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((124221195/1073741824), (390327983/2147483648)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((-727844967/17179869184), (-571758825/8589934592)), (95/17179869184), by norm_num⟩
  | 4 => ⟨((799619425/68719476736), (1256282543/68719476736)), (107/68719476736), by norm_num⟩
  | 5 => ⟨((-702777381/274877906944), (-17252093/4294967296)), (97/274877906944), by norm_num⟩
  | 6 => ⟨((514719911/1099511627776), (50542297/68719476736)), (73/1099511627776), by norm_num⟩
  | 7 => ⟨((-646260137/8796093022208), (-1015339677/8796093022208)), (47/4398046511104), by norm_num⟩
  | 8 => ⟨((44374333/4398046511104), (1115464647/70368744177664)), (53/35184372088832), by norm_num⟩
  | 9 => ⟨((-693336001/562949953421312), (-1089300595/562949953421312)), (53/281474976710656), by norm_num⟩
  | 10 => ⟨((609365961/4503599627370496), (59835951/281474976710656)), (95/4503599627370496), by norm_num⟩
  | 11 => ⟨((-243438885/18014398509481984), (-764933947/36028797018963968)), (39/18014398509481984), by norm_num⟩
  | 12 => ⟨((713186535/576460752303423488), (1120487779/576460752303423488)), (117/576460752303423488), by norm_num⟩
  | 13 => ⟨((-482163379/4611686018427387904), (-757527165/4611686018427387904)), (81/4611686018427387904), by norm_num⟩
  | 14 => ⟨((302691779/36893488147419103232), (237779615/18446744073709551616)), (13/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-177355151/295147905179352825856), (-278642781/295147905179352825856)), (31/295147905179352825856), by norm_num⟩
  | 16 => ⟨((389689097/9444732965739290427392), (612240767/9444732965739290427392)), (139/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (653893174917/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890189813589763/316912650057057350374175801344), (1550365522313/633825300114114700748351602688)), (46177/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891553791164665/39614081257132168796771975168), (1743999501541/39614081257132168796771975168)), (25977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891441781277041/2475880078570760549798248448), (1852804556795/2475880078570760549798248448)), (27603/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443276915032059/38685626227668133590597632), (1852585300433/154742504910672534362390528)), (55213/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551350193564339/9671406556917033397649408), (868282892215/4835703278458516698824704)), (6471/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157545057764039/75557863725914323419136), (1519262154947/604462909807314587353088)), (5663/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((945172723523901/37778931862957161709568), (617091090591/18889465931478580854784)), (2301/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1299453858936201/4722366482869645213696), (1850891272405/4722366482869645213696)), (55235/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624079372564013/590295810358705651712), (636088715831/147573952589676412928)), (75967/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826762115883207/73786976294838206464), (198719551381/4611686018427387904)), (94985/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456588287479157/2305843009213693952), (446959056811/1152921504606846976)), (106895/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199699866123787/144115188075855872), (1787036798695/576460752303423488)), (106941/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197739131628271/144115188075855872), (3125516344645/144115188075855872)), (93627/144115188075855872), by norm_num⟩
  | 4 => ⟨((374092207050425/9007199254740992), (4684680063653/36028797018963968)), (549/140737488355328), by norm_num⟩
  | 3 => ⟨((186895156883511/1125899906842624), (5849563504923/9007199254740992)), (175863/9007199254740992), by norm_num⟩
  | 2 => ⟨((279965394018187/562949953421312), (11680282159449/4503599627370496)), (352277/4503599627370496), by norm_num⟩
  | 1 => ⟨((1116843159350255/1125899906842624), (17473363165635/2251799813685248)), (264897/1125899906842624), by norm_num⟩
  | 0 => ⟨((1107789548860737/1125899906842624), (17379399155939/1125899906842624)), (266279/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1107789548860737/1125899906842624), (17379399155939/1125899906842624)), (1015773775340843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1089702231604809/1125899906842624), (34199695076659/1125899906842624)), (1064425/1125899906842624), by norm_num⟩
  | 2 => ⟨((2107258961851891/2251799813685248), (132400700342001/2251799813685248)), (4250145/2251799813685248), by norm_num⟩
  | 3 => ⟨((982105593928319/1125899906842624), (247804054921329/2251799813685248)), (8454463/2251799813685248), by norm_num⟩
  | 4 => ⟨((1686081825653987/2251799813685248), (216155758657839/1125899906842624)), (8305091/1125899906842624), by norm_num⟩
  | 5 => ⟨((1179491471069171/2251799813685248), (323702217193961/1125899906842624)), (15626123/1125899906842624), by norm_num⟩
  | 6 => ⟨((215842372566171/1125899906842624), (1356440308862465/4503599627370496)), (101420385/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-1197596827/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-755599471/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-66307712909765/281474976710656), (618013452752209/4503599627370496)), (27307459/1125899906842624), by norm_num⟩
  | 1 => ⟨((701309269/2147483648), (-408529551/2147483648)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((-972221085/4294967296), (566342213/4294967296)), (13/536870912), by norm_num⟩
  | 3 => ⟨((14039423/134217728), (-32713209/536870912)), (49/4294967296), by norm_num⟩
  | 4 => ⟨((-311404367/8589934592), (725602195/34359738368)), (69/17179869184), by norm_num⟩
  | 5 => ⟨((690716989/68719476736), (-402359293/68719476736)), (39/34359738368), by norm_num⟩
  | 6 => ⟨((-1276716089/549755813888), (185929473/137438953472)), (147/549755813888), by norm_num⟩
  | 7 => ⟨((505686947/1099511627776), (-589149669/2199023255552)), (119/2199023255552), by norm_num⟩
  | 8 => ⟨((-701030963/8796093022208), (51045929/1099511627776)), (21/2199023255552), by norm_num⟩
  | 9 => ⟨((431926787/35184372088832), (-503215527/70368744177664)), (53/35184372088832), by norm_num⟩
  | 10 => ⟨((-958044271/562949953421312), (279041939/281474976710656)), (119/562949953421312), by norm_num⟩
  | 11 => ⟨((241478431/1125899906842624), (-70333503/562949953421312)), (61/2251799813685248), by norm_num⟩
  | 12 => ⟨((-892693833/36028797018963968), (520015673/36028797018963968)), (115/36028797018963968), by norm_num⟩
  | 13 => ⟨((380780439/144115188075855872), (-221813783/144115188075855872)), (25/72057594037927936), by norm_num⟩
  | 14 => ⟨((-603284315/2305843009213693952), (702855307/4611686018427387904)), (161/4611686018427387904), by norm_num⟩
  | 15 => ⟨((446042477/18446744073709551616), (-259830493/18446744073709551616)), (121/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-1236692341/590295810358705651712), (720403095/590295810358705651712)), (85/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (425648253895/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444988956720493/158456325028528675187087900672), (2017507376589/316912650057057350374175801344)), (46299/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472769157618045/9903520314283042199192993792), (4538845632513/39614081257132168796771975168)), (52099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890934310808763/2475880078570760549798248448), (2410940665395/1237940039285380274899124224)), (27685/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443149910439599/38685626227668133590597632), (4821158783319/154742504910672534362390528)), (27693/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550873344455393/9671406556917033397649408), (2259534300791/4835703278458516698824704)), (51943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259942637545009/604462909807314587353088), (3953417211089/604462909807314587353088)), (45467/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944832696124157/37778931862957161709568), (6422863192415/75557863725914323419136)), (73917/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298942864810301/4722366482869645213696), (1203971867265/1180591620717411303424)), (55467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623375208129211/590295810358705651712), (6619797664127/590295810358705651712)), (38157/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456469897773723/18446744073709551616), (8271675275047/73786976294838206464)), (47731/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825357123854465/9223372036854775808), (2325352577731/2305843009213693952)), (107493/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798299462881195/576460752303423488), (2324032221605/288230376151711744)), (53807/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196859661267193/144115188075855872), (8128169863765/144115188075855872)), (94299/144115188075855872), by norm_num⟩
  | 4 => ⟨((373760176129627/9007199254740992), (12180365721055/36028797018963968)), (70861/18014398509481984), by norm_num⟩
  | 3 => ⟨((746742765899137/4503599627370496), (15204644017627/9007199254740992)), (177631/9007199254740992), by norm_num⟩
  | 2 => ⟨((69885160995725/140737488355328), (15173409963945/2251799813685248)), (178351/2251799813685248), by norm_num⟩
  | 1 => ⟨((557118366620475/562949953421312), (5670495065989/281474976710656)), (134665/562949953421312), by norm_num⟩
  | 0 => ⟨((137793323675521/140737488355328), (22525565004771/562949953421312)), (272945/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((137793323675521/140737488355328), (22525565004771/562949953421312)), (1041202547313499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((538741672986671/562949953421312), (88217361442173/1125899906842624)), (1112627/1125899906842624), by norm_num⟩
  | 2 => ⟨((512118373481347/562949953421312), (42211895214651/281474976710656)), (1151959/562949953421312), by norm_num⟩
  | 3 => ⟨((906431737017249/1125899906842624), (307202968754327/1125899906842624)), (4882795/1125899906842624), by norm_num⟩
  | 4 => ⟨((645923163720705/1125899906842624), (123660424382539/281474976710656)), (10526567/1125899906842624), by norm_num⟩
  | 5 => ⟨((76625960907717/562949953421312), (1135093903943337/2251799813685248)), (42654707/2251799813685248), by norm_num⟩
  | 6 => ⟨((-66307712909765/281474976710656), (618013452752209/4503599627370496)), (27307459/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-755599471/33554432)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-219305955/8388608)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((66159436313253/562949953421312), (-421887667534947/2251799813685248)), (63512243/4503599627370496), by norm_num⟩
  | 1 => ⟨((-406187077/2147483648), (647546775/2147483648)), (25/1073741824), by norm_num⟩
  | 2 => ⟨((653732881/4294967296), (-521093165/2147483648)), (41/2147483648), by norm_num⟩
  | 3 => ⟨((-350714161/4294967296), (559111397/4294967296)), (45/4294967296), by norm_num⟩
  | 4 => ⟨((564452667/17179869184), (-112481885/2147483648)), (37/8589934592), by norm_num⟩
  | 5 => ⟨((-363380609/34359738368), (1158608705/68719476736)), (97/68719476736), by norm_num⟩
  | 6 => ⟨((779784705/274877906944), (-77696199/17179869184)), (53/137438953472), by norm_num⟩
  | 7 => ⟨((-717151467/1099511627776), (571644381/549755813888)), (99/1099511627776), by norm_num⟩
  | 8 => ⟨((144276345/1099511627776), (-920026139/4398046511104)), (81/4398046511104), by norm_num⟩
  | 9 => ⟨((-825613581/35184372088832), (658099977/17592186044416)), (59/17592186044416), by norm_num⟩
  | 10 => ⟨((531509519/140737488355328), (-847336843/140737488355328)), (39/70368744177664), by norm_num⟩
  | 11 => ⟨((-155533013/281474976710656), (991808029/1125899906842624)), (93/1125899906842624), by norm_num⟩
  | 12 => ⟨((667521941/9007199254740992), (-1064168963/9007199254740992)), (51/4503599627370496), by norm_num⟩
  | 13 => ⟨((-82641163/9007199254740992), (1053977769/72057594037927936)), (103/72057594037927936), by norm_num⟩
  | 14 => ⟨((304013305/288230376151711744), (-969321017/576460752303423488)), (97/576460752303423488), by norm_num⟩
  | 15 => ⟨((-130477477/1152921504606846976), (104004133/576460752303423488)), (85/4611686018427387904), by norm_num⟩
  | 16 => ⟨((104997699/9223372036854775808), (-669552779/36893488147419103232)), (35/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (-1316374864331/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889820185665587/316912650057057350374175801344), (-779657917849/316912650057057350374175801344)), (46177/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945361111453683/19807040628566084398385987584), (-1753995150035/39614081257132168796771975168)), (25977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472639588351245/618970019642690137449562112), (-931666415587/1237940039285380274899124224)), (55207/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221528044978563/19342813113834066795298816), (-232876250519/19342813113834066795298816)), (27607/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550522235069213/9671406556917033397649408), (-436557235653/2417851639229258349412352)), (25885/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259636133954017/604462909807314587353088), (-1527607464353/604462909807314587353088)), (45305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944584333938295/37778931862957161709568), (-2481719427413/75557863725914323419136)), (73633/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324642874214949/1180591620717411303424), (-116295460455/295147905179352825856)), (13809/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622866485906063/590295810358705651712), (-2557586851687/590295810358705651712)), (1187/9223372036854775808), by norm_num⟩
  | 8 => ⟨((912623274639987/36893488147419103232), (-798903543871/18446744073709551616)), (94987/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824648882227531/9223372036854775808), (-3593183895665/9223372036854775808)), (53449/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595895592038847/1152921504606846976), (-3590832617905/1152921504606846976)), (106945/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196249758618427/144115188075855872), (-1569667560949/72057594037927936)), (46815/72057594037927936), by norm_num⟩
  | 4 => ⟨((93383553855515/2251799813685248), (-4703720264625/36028797018963968)), (140549/36028797018963968), by norm_num⟩
  | 3 => ⟨((746187479113235/4503599627370496), (-5870416035571/9007199254740992)), (687/35184372088832), by norm_num⟩
  | 2 => ⟨((2234161536539661/4503599627370496), (-5856584449173/2251799813685248)), (88075/1125899906842624), by norm_num⟩
  | 1 => ⟨((2225371320037119/2251799813685248), (-17500734258059/2251799813685248)), (132461/562949953421312), by norm_num⟩
  | 0 => ⟨((2199058676154319/2251799813685248), (-4340777999347/281474976710656)), (1065277/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2199058676154319/2251799813685248), (-4340777999347/281474976710656)), (4063709267623137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2147017297520937/2251799813685248), (-67825748720365/2251799813685248)), (1056755/1125899906842624), by norm_num⟩
  | 2 => ⟨((1022533822873013/1125899906842624), (-129339255501233/2251799813685248)), (4157647/2251799813685248), by norm_num⟩
  | 3 => ⟨((924943018324149/1125899906842624), (-58732469277001/562949953421312)), (125461/35184372088832), by norm_num⟩
  | 4 => ⟨((1495197877256323/2251799813685248), (-6031196365297/35184372088832)), (14868141/2251799813685248), by norm_num⟩
  | 5 => ⟨((463323455629147/1125899906842624), (-512604401746337/2251799813685248)), (24842231/2251799813685248), by norm_num⟩
  | 6 => ⟨((66159436313253/562949953421312), (-421887667534947/2251799813685248)), (63512243/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-219305955/8388608)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-112727759/67108864), (-976598149/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-566240857941271/4503599627370496), (309920891965981/2251799813685248)), (75819053/4503599627370496), by norm_num⟩
  | 1 => ⟨((483783445/2147483648), (-264789435/1073741824)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((-866823569/4294967296), (948877955/4294967296)), (15/536870912), by norm_num⟩
  | 3 => ⟨((517713113/4294967296), (-283360177/2147483648)), (73/4294967296), by norm_num⟩
  | 4 => ⟨((-927617373/17179869184), (1015426561/17179869184)), (133/17179869184), by norm_num⟩
  | 5 => ⟨((664826885/34359738368), (-727760063/34359738368)), (97/34359738368), by norm_num⟩
  | 6 => ⟨((-794139911/137438953472), (434656995/68719476736)), (59/68719476736), by norm_num⟩
  | 7 => ⟨((406545059/274877906944), (-445029021/274877906944)), (123/549755813888), by norm_num⟩
  | 8 => ⟨((-728430959/2199023255552), (797384963/2199023255552)), (7/137438953472), by norm_num⟩
  | 9 => ⟨((580076919/8796093022208), (-634987581/8796093022208)), (91/8796093022208), by norm_num⟩
  | 10 => ⟨((-415743325/35184372088832), (910196009/70368744177664)), (33/17592186044416), by norm_num⟩
  | 11 => ⟨((541754211/281474976710656), (-593037207/281474976710656)), (11/35184372088832), by norm_num⟩
  | 12 => ⟨((-647128825/2251799813685248), (5534271/17592186044416)), (107/2251799813685248), by norm_num⟩
  | 13 => ⟨((713537969/18014398509481984), (-781082189/18014398509481984)), (15/2251799813685248), by norm_num⟩
  | 14 => ⟨((-730564807/144115188075855872), (799720805/144115188075855872)), (125/144115188075855872), by norm_num⟩
  | 15 => ⟨((698131419/1152921504606846976), (-95527155/144115188075855872)), (121/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-312720895/4611686018427387904), (342323369/4611686018427387904)), (55/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790893836630535/5070602400912917605986812821504), (1505189682707/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779371171881783/633825300114114700748351602688), (3564949014951/633825300114114700748351602688)), (11569/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59075596859291/1237940039285380274899124224), (4009959330631/39614081257132168796771975168)), (52071/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472558982903679/618970019642690137449562112), (532481242157/309485009821345068724781056)), (55339/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771901540981489/154742504910672534362390528), (4259026629627/154742504910672534362390528)), (55353/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550219170767919/9671406556917033397649408), (3991962785423/9671406556917033397649408)), (25955/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259370531328715/604462909807314587353088), (3492092852311/604462909807314587353088)), (11359/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888736274132061/75557863725914323419136), (709126405015/9444732965739290427392)), (73863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649123255666143/2361183241434822606848), (2126661971431/2361183241434822606848)), (55423/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622418510276397/590295810358705651712), (5845989758917/590295810358705651712)), (76249/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456171225208051/18446744073709551616), (7303991869291/73786976294838206464)), (95373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912007361140121/4611686018427387904), (256630808007/288230376151711744)), (26845/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595258554872031/1152921504606846976), (8206181234551/1152921504606846976)), (107487/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597844560262381/72057594037927936), (7173655618287/144115188075855872)), (23543/36028797018963968), by norm_num⟩
  | 4 => ⟨((186661182391945/4503599627370496), (5373491554721/18014398509481984)), (141501/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491304460922937/9007199254740992), (13410115977373/9007199254740992)), (44325/2251799813685248), by norm_num⟩
  | 2 => ⟨((139499184426469/281474976710656), (3343680497879/562949953421312)), (177937/2251799813685248), by norm_num⟩
  | 1 => ⟨((138876622316635/140737488355328), (19973687224181/1125899906842624)), (67125/281474976710656), by norm_num⟩
  | 0 => ⟨((548009241369149/562949953421312), (39594329612623/1125899906842624)), (543401/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((548009241369149/562949953421312), (39594329612623/1125899906842624)), (2072910313132857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1065537705683617/1125899906842624), (77086989355499/1125899906842624)), (1096179/1125899906842624), by norm_num⟩
  | 2 => ⟨((501566876167919/562949953421312), (145908341010987/1125899906842624)), (1112463/562949953421312), by norm_num⟩
  | 3 => ⟨((874845157293791/1125899906842624), (259997501955397/1125899906842624)), (4541317/1125899906842624), by norm_num⟩
  | 4 => ⟨((1239462485033995/2251799813685248), (808091568750633/2251799813685248)), (1144347/140737488355328), by norm_num⟩
  | 5 => ⟨((392244134204483/2251799813685248), (889598780363591/2251799813685248)), (16648815/1125899906842624), by norm_num⟩
  | 6 => ⟨((-566240857941271/4503599627370496), (309920891965981/2251799813685248)), (75819053/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-112727759/67108864), (-976598149/33554432)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-3825815/2097152), (-1060617947/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((713091484906133/4503599627370496), (-278650767041347/9007199254740992)), (3338571/562949953421312), by norm_num⟩
  | 1 => ⟨((-1323329885/4294967296), (258555105/4294967296)), (51/4294967296), by norm_num⟩
  | 2 => ⟨((1287540527/4294967296), (-251562501/4294967296)), (51/4294967296), by norm_num⟩
  | 3 => ⟨((-1670292119/8589934592), (326345349/8589934592)), (17/2147483648), by norm_num⟩
  | 4 => ⟨((1625119193/17179869184), (-317519363/17179869184)), (17/4294967296), by norm_num⟩
  | 5 => ⟨((-1264934373/34359738368), (61786415/8589934592)), (55/34359738368), by norm_num⟩
  | 6 => ⟨((410241439/34359738368), (-320615499/137438953472)), (73/137438953472), by norm_num⟩
  | 7 => ⟨((-456167417/137438953472), (178253987/274877906944)), (21/137438953472), by norm_num⟩
  | 8 => ⟨((1775321613/2199023255552), (-173433121/1099511627776)), (21/549755813888), by norm_num⟩
  | 9 => ⟨((-767692521/4398046511104), (299986907/8796093022208)), (37/4398046511104), by norm_num⟩
  | 10 => ⟨((597544267/17592186044416), (-233499027/35184372088832)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-1691298115/281474976710656), (330449547/281474976710656)), (43/140737488355328), by norm_num⟩
  | 12 => ⟨((137129757/140737488355328), (-214341709/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | 13 => ⟨((-10263161/70368744177664), (256670589/9007199254740992)), (35/4503599627370496), by norm_num⟩
  | 14 => ⟨((1460749835/72057594037927936), (-285404517/72057594037927936)), (5/4503599627370496), by norm_num⟩
  | 15 => ⟨((-757996781/288230376151711744), (148099079/288230376151711744)), (85/576460752303423488), by norm_num⟩
  | 16 => ⟨((1474993629/4611686018427387904), (-288187501/4611686018427387904)), (21/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790799712358623/5070602400912917605986812821504), (-251340807771/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779155017582321/633825300114114700748351602688), (-297571664871/633825300114114700748351602688)), (11529/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890176353002365/39614081257132168796771975168), (-334714535697/39614081257132168796771975168)), (51881/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472494639431671/618970019642690137449562112), (-88892005101/618970019642690137449562112)), (13781/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771644779043891/154742504910672534362390528), (-355493598817/154742504910672534362390528)), (27563/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549979106327417/9671406556917033397649408), (-333196197933/9671406556917033397649408)), (51681/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259161124457857/604462909807314587353088), (-145733823481/302231454903657293676544)), (45223/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888397205039023/75557863725914323419136), (-473486804661/75557863725914323419136)), (73489/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324498318420793/1180591620717411303424), (-354985549557/4722366482869645213696)), (55119/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622072036347909/590295810358705651712), (-243947351947/295147905179352825856)), (4737/36893488147419103232), by norm_num⟩
  | 8 => ⟨((114015899854029/4611686018427387904), (-609552911861/73786976294838206464)), (94745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823533962339897/9223372036854775808), (-685313536847/9223372036854775808)), (106595/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594782233961765/1152921504606846976), (-171193023641/288230376151711744)), (106605/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597638662611677/72057594037927936), (-299283517879/72057594037927936)), (93289/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492681716159895/36028797018963968), (-896634897141/36028797018963968)), (139955/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490562147438261/9007199254740992), (-1118669452821/9007199254740992)), (174979/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230554230948067/4503599627370496), (-2230979300591/4503599627370496)), (350067/4503599627370496), by norm_num⟩
  | 1 => ⟨((277500748266357/281474976710656), (-1665307499919/1125899906842624)), (525379/2251799813685248), by norm_num⟩
  | 0 => ⟨((547127379054939/562949953421312), (-1649520959381/562949953421312)), (1051883/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547127379054939/562949953421312), (-1649520959381/562949953421312)), (4012615212447356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1063489378311045/1125899906842624), (-12825269084293/2251799813685248)), (1025401/1125899906842624), by norm_num⟩
  | 2 => ⟨((251125461736255/281474976710656), (-24228685626907/2251799813685248)), (3897607/2251799813685248), by norm_num⟩
  | 3 => ⟨((448031480011115/562949953421312), (-1351017046085/70368744177664)), (7038585/2251799813685248), by norm_num⟩
  | 4 => ⟨((44545565296247/70368744177664), (-8601804306035/281474976710656)), (2868445/562949953421312), by norm_num⟩
  | 5 => ⟨((900255576075209/2251799813685248), (-174246558972309/4503599627370496)), (30455557/4503599627370496), by norm_num⟩
  | 6 => ⟨((713091484906133/4503599627370496), (-278650767041347/9007199254740992)), (3338571/562949953421312), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3825815/2097152), (-1060617947/33554432)), (1/33554432), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-566699603/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-911875365935933/9007199254740992), (-450672480644085/4503599627370496)), (29101099/1125899906842624), by norm_num⟩
  | 1 => ⟨((452087287/2147483648), (893733099/4294967296)), (233/4294967296), by norm_num⟩
  | 2 => ⟨((-940089085/4294967296), (-929232867/4294967296)), (245/4294967296), by norm_num⟩
  | 3 => ⟨((651620099/4294967296), (322047571/2147483648)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((-84687869/1073741824), (-334839549/4294967296)), (181/8589934592), by norm_num⟩
  | 5 => ⟨((563531113/17179869184), (278511707/8589934592)), (153/17179869184), by norm_num⟩
  | 6 => ⟨((-195305001/17179869184), (-386099209/34359738368)), (107/34359738368), by norm_num⟩
  | 7 => ⟨((464143237/137438953472), (458783277/137438953472)), (257/274877906944), by norm_num⟩
  | 8 => ⟨((-120644841/137438953472), (-954013005/1099511627776)), (135/549755813888), by norm_num⟩
  | 9 => ⟨((222999017/1099511627776), (881695233/4398046511104)), (63/1099511627776), by norm_num⟩
  | 10 => ⟨((-23185671/549755813888), (-366686739/8796093022208)), (53/4398046511104), by norm_num⟩
  | 11 => ⟨((561026879/70368744177664), (138637025/17592186044416)), (163/70368744177664), by norm_num⟩
  | 12 => ⟨((-777748399/562949953421312), (-96095863/70368744177664)), (57/140737488355328), by norm_num⟩
  | 13 => ⟨((995250665/4503599627370496), (491878719/2251799813685248)), (295/4503599627370496), by norm_num⟩
  | 14 => ⟨((-591304451/18014398509481984), (-73059503/2251799813685248)), (177/18014398509481984), by norm_num⟩
  | 15 => ⟨((655777621/144115188075855872), (648204653/144115188075855872)), (99/72057594037927936), by norm_num⟩
  | 16 => ⟨((-340912807/576460752303423488), (-336975921/576460752303423488)), (13/72057594037927936), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (-3076771317735/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222369365653127/79228162514264337593543950336), (-1820975456987/316912650057057350374175801344)), (92559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944975442337945/19807040628566084398385987584), (-4096479673183/39614081257132168796771975168)), (13019/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944869261865823/1237940039285380274899124224), (-2175821176717/1237940039285380274899124224)), (3459/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771404212319867/154742504910672534362390528), (-1087666684401/38685626227668133590597632)), (55359/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549753009354665/9671406556917033397649408), (-2038856817179/4835703278458516698824704)), (51915/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314740681084421/151115727451828646838272), (-891740794329/151115727451828646838272)), (90883/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472018436453469/18889465931478580854784), (-2897186285297/37778931862957161709568)), (4617/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648874876731141/2361183241434822606848), (-4344080040977/4722366482869645213696)), (110861/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621735693207033/590295810358705651712), (-746293658521/73786976294838206464)), (76259/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455957929316323/18446744073709551616), (-7458796655973/73786976294838206464)), (190775/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911527677816847/4611686018427387904), (-2096363968159/2305843009213693952)), (107399/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594299769955605/1152921504606846976), (-8378345974113/1152921504606846976)), (107509/576460752303423488), by norm_num⟩
  | 5 => ⟨((597425419528211/72057594037927936), (-7323058299853/144115188075855872)), (47097/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492033349809175/36028797018963968), (-5484304562893/18014398509481984)), (283077/36028797018963968), by norm_num⟩
  | 3 => ⟨((372434156686091/2251799813685248), (-6841411531395/4503599627370496)), (354713/9007199254740992), by norm_num⟩
  | 2 => ⟨((557214552392149/1125899906842624), (-13640963060391/2251799813685248)), (356017/2251799813685248), by norm_num⟩
  | 1 => ⟨((554337557805307/562949953421312), (-20356961194053/1125899906842624)), (134323/281474976710656), by norm_num⟩
  | 0 => ⟨((136422216456309/140737488355328), (-2518561932349/70368744177664)), (543845/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((136422216456309/140737488355328), (-2518561932349/70368744177664)), (2074604036571311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1056471803964525/1125899906842624), (-78122821172095/1125899906842624)), (2186539/1125899906842624), by norm_num⟩
  | 2 => ⟨((985904244807197/1125899906842624), (-146610826260629/1125899906842624)), (2203425/562949953421312), by norm_num⟩
  | 3 => ⟨((844224641795699/1125899906842624), (-513524284233727/2251799813685248)), (17730969/2251799813685248), by norm_num⟩
  | 4 => ⟨((1148927083588511/2251799813685248), (-385051861427331/1125899906842624)), (17338631/1125899906842624), by norm_num⟩
  | 5 => ⟨((161420587884951/1125899906842624), (-392927035068907/1125899906842624)), (29552687/1125899906842624), by norm_num⟩
  | 6 => ⟨((-911875365935933/9007199254740992), (-450672480644085/4503599627370496)), (29101099/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-566699603/16777216)), (1/16777216), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile004Terms0
