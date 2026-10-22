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
namespace Reinmann.XiBand97.Tile033Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32189/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32189/1280))
  have he : value ((69/80), (32189/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-584888211/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((23481667074961/281474976710656), (1224157200836713/2251799813685248)), (92632763/2251799813685248), by norm_num⟩
  | 1 => ⟨((-124177943/2147483648), (-101151599/268435456)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((86073591/4294967296), (1121807131/8589934592)), (89/8589934592), by norm_num⟩
  | 3 => ⟨((-79548889/17179869184), (-1036769933/34359738368)), (21/8589934592), by norm_num⟩
  | 4 => ⟨((220556353/274877906944), (179658539/34359738368)), (119/274877906944), by norm_num⟩
  | 5 => ⟨((-244604823/2199023255552), (-1593981565/2199023255552)), (67/1099511627776), by norm_num⟩
  | 6 => ⟨((113031429/8796093022208), (736575885/8796093022208)), (63/8796093022208), by norm_num⟩
  | 7 => ⟨((-179079809/140737488355328), (-1166983995/140737488355328)), (51/70368744177664), by norm_num⟩
  | 8 => ⟨((248257329/2251799813685248), (404445833/562949953421312)), (9/140737488355328), by norm_num⟩
  | 9 => ⟨((-152958993/18014398509481984), (-996766183/18014398509481984)), (91/18014398509481984), by norm_num⟩
  | 10 => ⟨((21204619/36028797018963968), (1105449071/288230376151711744)), (103/288230376151711744), by norm_num⟩
  | 11 => ⟨((-42757591/1152921504606846976), (-1114529319/4611686018427387904)), (53/2305843009213693952), by norm_num⟩
  | 12 => ⟨((158065619/73786976294838206464), (1030043807/73786976294838206464)), (25/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-134846447/1180591620717411303424), (-878734721/1180591620717411303424)), (173/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((26705267/4722366482869645213696), (174026427/4722366482869645213696)), (139/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-157957807/604462909807314587353088), (-514670623/302231454903657293676544)), (105/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((218976017/19342813113834066795298816), (1426969965/19342813113834066795298816)), (147/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (230974033417/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890522932096879/316912650057057350374175801344), (548023933319/158456325028528675187087900672)), (46209/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892303173745213/39614081257132168796771975168), (616492798621/9903520314283042199192993792)), (51991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946118919632159/1237940039285380274899124224), (2619934060693/2475880078570760549798248448)), (3453/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1773903536993999/154742504910672534362390528), (654938416559/38685626227668133590597632)), (55257/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776048067850171/4835703278458516698824704), (1227913688891/4835703278458516698824704)), (51813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261012969073611/604462909807314587353088), (1074328627073/302231454903657293676544)), (45347/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891405410133619/75557863725914323419136), (3491208561525/75557863725914323419136)), (73705/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650124257826615/2361183241434822606848), (2618091842955/4722366482869645213696)), (55295/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25393304887123/9223372036854775808), (3599365026527/590295810358705651712)), (9507/73786976294838206464), by norm_num⟩
  | 8 => ⟨((914063261056177/36893488147419103232), (562304909751/9223372036854775808)), (23777/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913943524852151/4611686018427387904), (632461170345/1152921504606846976)), (13381/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599131507559003/1152921504606846976), (2529185271253/576460752303423488)), (53557/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199078651925987/144115188075855872), (4424590155129/144115188075855872)), (93799/144115188075855872), by norm_num⟩
  | 4 => ⟨((187296892225421/4503599627370496), (6633916103423/36028797018963968)), (70423/18014398509481984), by norm_num⟩
  | 3 => ⟨((93603996591795/562949953421312), (2071799232551/2251799813685248)), (44079/2251799813685248), by norm_num⟩
  | 2 => ⟨((561178238167237/1125899906842624), (2069848799573/562949953421312)), (176705/2251799813685248), by norm_num⟩
  | 1 => ⟨((560283025553737/562949953421312), (12399573006923/1125899906842624)), (266031/1125899906842624), by norm_num⟩
  | 0 => ⟨((139394699803461/140737488355328), (6180243633401/281474976710656)), (535961/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139394699803461/140737488355328), (6180243633401/281474976710656)), (2044528965476607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((137996874233117/140737488355328), (3060638697115/70368744177664)), (67827/70368744177664), by norm_num⟩
  | 2 => ⟨((1080347104856037/1125899906842624), (24008305294887/281474976710656)), (1111301/562949953421312), by norm_num⟩
  | 3 => ⟨((1028446205886891/1125899906842624), (92147811577913/562949953421312)), (4644509/1125899906842624), by norm_num⟩
  | 4 => ⟨((454630431829249/562949953421312), (42085920170225/140737488355328)), (2501373/281474976710656), by norm_num⟩
  | 5 => ⟨((316811882896773/562949953421312), (543807915986483/1125899906842624)), (22144643/1125899906842624), by norm_num⟩
  | 6 => ⟨((23481667074961/281474976710656), (1224157200836713/2251799813685248)), (92632763/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-584888211/33554432)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-463512941/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-174165166789885/562949953421312), (-263052982467567/1125899906842624)), (1216461/35184372088832), by norm_num⟩
  | 1 => ⟨((364952073/1073741824), (137802715/536870912)), (21/536870912), by norm_num⟩
  | 2 => ⟨((-801881665/4294967296), (-605567025/4294967296)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((587304701/8589934592), (887044501/17179869184)), (71/8589934592), by norm_num⟩
  | 4 => ⟨((-322610081/17179869184), (-487258995/34359738368)), (5/2147483648), by norm_num⟩
  | 5 => ⟨((567077439/137438953472), (6691359/2147483648)), (9/17179869184), by norm_num⟩
  | 6 => ⟨((-207666081/274877906944), (-627303187/1099511627776)), (27/274877906944), by norm_num⟩
  | 7 => ⟨((1042946325/8796093022208), (393807423/4398046511104)), (69/4398046511104), by norm_num⟩
  | 8 => ⟨((-1145793649/70368744177664), (-865283349/70368744177664)), (77/35184372088832), by norm_num⟩
  | 9 => ⟨((1118918207/562949953421312), (844987485/562949953421312)), (153/562949953421312), by norm_num⟩
  | 10 => ⟨((-491702917/2251799813685248), (-185662727/1125899906842624)), (17/562949953421312), by norm_num⟩
  | 11 => ⟨((392866085/18014398509481984), (296685605/18014398509481984)), (111/36028797018963968), by norm_num⟩
  | 12 => ⟨((-1150953357/576460752303423488), (-869179871/576460752303423488)), (165/576460752303423488), by norm_num⟩
  | 13 => ⟨((778124001/4611686018427387904), (293812827/2305843009213693952)), (57/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-61061185/4611686018427387904), (-737797445/73786976294838206464)), (73/36893488147419103232), by norm_num⟩
  | 15 => ⟨((1144875831/1180591620717411303424), (864590229/1180591620717411303424)), (87/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-628887329/9444732965739290427392), (-474924725/9444732965739290427392)), (49/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-3249733360285/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780500239003113/633825300114114700748351602688), (-963261029365/158456325028528675187087900672)), (23145/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472922267556233/9903520314283042199192993792), (-4334287800367/39614081257132168796771975168)), (6511/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945792504878065/1237940039285380274899124224), (-4604733111367/2475880078570760549798248448)), (27679/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886625160013271/77371252455336267181195264), (-4604229332483/154742504910672534362390528)), (55373/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775741666636571/4835703278458516698824704), (-4315929634095/9671406556917033397649408)), (25965/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78779772225259/37778931862957161709568), (-1887951476115/302231454903657293676544)), (45455/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118158290146471/4722366482869645213696), (-1533709509507/18889465931478580854784)), (9237/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1299593265642197/4722366482869645213696), (-2300124781495/2361183241434822606848)), (27725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406067362295633/147573952589676412928), (-3161957191625/295147905179352825856)), (149/1152921504606846976), by norm_num⟩
  | 8 => ⟨((228374662699479/9223372036854775808), (-987843631157/9223372036854775808)), (95427/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913307211096275/4611686018427387904), (-8887643509683/9223372036854775808)), (13431/1152921504606846976), by norm_num⟩
  | 6 => ⟨((798928032488519/576460752303423488), (-4441977574361/576460752303423488)), (26891/288230376151711744), by norm_num⟩
  | 5 => ⟨((598979738397271/72057594037927936), (-3884654372663/72057594037927936)), (94249/144115188075855872), by norm_num⟩
  | 4 => ⟨((23385782180749/562949953421312), (-11645652605265/36028797018963968)), (141633/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495546568451233/9007199254740992), (-14542507794343/9007199254740992)), (177499/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120222601431671/2251799813685248), (-1815080229043/281474976710656)), (178185/2251799813685248), by norm_num⟩
  | 1 => ⟨((4364547480141/4398046511104), (-2715774597357/140737488355328)), (67249/281474976710656), by norm_num⟩
  | 0 => ⟨((1108510436367967/1125899906842624), (-43232727293405/1125899906842624)), (544881/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108510436367967/1125899906842624), (-43232727293405/1125899906842624)), (2078556065085982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((544864739472339/562949953421312), (-21282499938997/281474976710656)), (1114777/1125899906842624), by norm_num⟩
  | 2 => ⟨((131035540243139/140737488355328), (-2574847842625/17592186044416)), (1163253/562949953421312), by norm_num⟩
  | 3 => ⟨((237975015073749/281474976710656), (-153430200090155/562949953421312)), (156665/35184372088832), by norm_num⟩
  | 4 => ⟨((11268075633547/17592186044416), (-518874602721879/1125899906842624)), (5604867/562949953421312), by norm_num⟩
  | 5 => ⟨((27848427488259/140737488355328), (-664694910915021/1125899906842624)), (49384223/2251799813685248), by norm_num⟩
  | 6 => ⟨((-174165166789885/562949953421312), (-263052982467567/1125899906842624)), (1216461/35184372088832), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-463512941/16777216)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-584888211/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1299646591491535/4503599627370496), (408494597614065/4503599627370496)), (29317151/562949953421312), by norm_num⟩
  | 1 => ⟨((859114047/2147483648), (-135014953/1073741824)), (157/2147483648), by norm_num⟩
  | 2 => ⟨((-1190984959/4294967296), (46792617/536870912)), (219/4294967296), by norm_num⟩
  | 3 => ⟨((550351911/4294967296), (-172982243/4294967296)), (51/2147483648), by norm_num⟩
  | 4 => ⟨((-762949751/17179869184), (59951077/4294967296)), (285/34359738368), by norm_num⟩
  | 5 => ⟨((423069175/34359738368), (-1038873/268435456)), (159/68719476736), by norm_num⟩
  | 6 => ⟨((-1563995765/549755813888), (491582731/549755813888)), (37/68719476736), by norm_num⟩
  | 7 => ⟨((154868465/274877906944), (-194708105/1099511627776)), (59/549755813888), by norm_num⟩
  | 8 => ⟨((-858773119/8796093022208), (67480687/2199023255552)), (165/8796093022208), by norm_num⟩
  | 9 => ⟨((33069787/2199023255552), (-83153863/17592186044416)), (205/70368744177664), by norm_num⟩
  | 10 => ⟨((-1173618157/562949953421312), (92220585/140737488355328)), (115/281474976710656), by norm_num⟩
  | 11 => ⟨((1183258351/4503599627370496), (-371912369/4503599627370496)), (117/2251799813685248), by norm_num⟩
  | 12 => ⟨((-136695365/4503599627370496), (343720013/36028797018963968)), (109/18014398509481984), by norm_num⟩
  | 13 => ⟨((116615393/36028797018963968), (-146614497/144115188075855872)), (47/72057594037927936), by norm_num⟩
  | 14 => ⟨((-1478064107/4611686018427387904), (116143343/1152921504606846976)), (301/4611686018427387904), by norm_num⟩
  | 15 => ⟨((1092817033/36893488147419103232), (-343485571/36893488147419103232)), (7/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-1514966091/590295810358705651712), (238086055/295147905179352825856)), (313/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (3695584534673/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890057390140645/316912650057057350374175801344), (4379876298179/633825300114114700748351602688)), (92631/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59101729349081/1237940039285380274899124224), (2463404093943/19807040628566084398385987584)), (104237/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236390506251617/309485009821345068724781056), (327130726209/154742504910672534362390528)), (1731/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1772789224832525/154742504910672534362390528), (5233369073211/154742504910672534362390528)), (27705/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551050912731077/9671406556917033397649408), (4905515680593/9671406556917033397649408)), (25983/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260097843965689/604462909807314587353088), (4291558259697/604462909807314587353088)), (90979/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944958645922239/37778931862957161709568), (6972341958373/75557863725914323419136)), (18489/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1299131517600821/4722366482869645213696), (2613997997591/2361183241434822606848)), (110997/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623634164010921/590295810358705651712), (7186445687179/590295810358705651712)), (152723/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826202623639691/73786976294838206464), (4489991481215/36893488147419103232)), (191057/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825719625202559/9223372036854775808), (5049126180795/4611686018427387904)), (215149/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596960289892285/1152921504606846976), (5046482249551/576460752303423488)), (215413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197174576354821/144115188075855872), (4412695987439/72057594037927936)), (188783/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495510522214485/36028797018963968), (6613088138049/18014398509481984)), (35471/4503599627370496), by norm_num⟩
  | 3 => ⟨((1494068337558563/9007199254740992), (8255928753827/4503599627370496)), (355751/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118738691744633/2251799813685248), (16480528675997/2251799813685248)), (357315/2251799813685248), by norm_num⟩
  | 1 => ⟨((557542107916695/562949953421312), (24642350809661/1125899906842624)), (269943/562949953421312), by norm_num⟩
  | 0 => ⟨((1103974993864935/1125899906842624), (3060638697115/70368744177664)), (1095473/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1103974993864935/1125899906842624), (3060638697115/70368744177664)), (4178897861960982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080347104856035/1125899906842624), (24008305294887/281474976710656)), (280447/140737488355328), by norm_num⟩
  | 2 => ⟨((1028446205886887/1125899906842624), (92147811577913/562949953421312)), (4688337/1125899906842624), by norm_num⟩
  | 3 => ⟨((909260863658491/1125899906842624), (168343680680899/562949953421312)), (2524977/281474976710656), by norm_num⟩
  | 4 => ⟨((2475092835131/4398046511104), (543807915986475/1125899906842624)), (22353609/1125899906842624), by norm_num⟩
  | 5 => ⟨((187853336599681/2251799813685248), (306039300209169/562949953421312)), (23376721/562949953421312), by norm_num⟩
  | 6 => ⟨((-1299646591491535/4503599627370496), (408494597614065/4503599627370496)), (29317151/562949953421312), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-584888211/16777216)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-679034185/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1048940307917429/4503599627370496), (-201682731426157/2251799813685248)), (98109933/4503599627370496), by norm_num⟩
  | 1 => ⟨((804998541/2147483648), (154779355/1073741824)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-323898793/1073741824), (-124553881/1073741824)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((1390119993/8589934592), (534564635/8589934592)), (137/8589934592), by norm_num⟩
  | 4 => ⟨((-559327955/8589934592), (-430174295/17179869184)), (7/1073741824), by norm_num⟩
  | 5 => ⟨((720162893/34359738368), (34616941/4294967296)), (147/68719476736), by norm_num⟩
  | 6 => ⟨((-1545409951/274877906944), (-297140359/137438953472)), (5/8589934592), by norm_num⟩
  | 7 => ⟨((355320195/274877906944), (273273691/549755813888)), (149/1099511627776), by norm_num⟩
  | 8 => ⟨((-571865793/2199023255552), (-439817039/4398046511104)), (61/2199023255552), by norm_num⟩
  | 9 => ⟨((818117767/17592186044416), (78650913/4398046511104)), (89/17592186044416), by norm_num⟩
  | 10 => ⟨((-1053367801/140737488355328), (-101267009/35184372088832)), (29/35184372088832), by norm_num⟩
  | 11 => ⟨((1232967327/1125899906842624), (237066129/562949953421312)), (69/562949953421312), by norm_num⟩
  | 12 => ⟨((-1322922907/9007199254740992), (-7948817/140737488355328)), (75/4503599627370496), by norm_num⟩
  | 13 => ⟨((81890857/4503599627370496), (125963101/18014398509481984)), (75/36028797018963968), by norm_num⟩
  | 14 => ⟨((-1205012571/576460752303423488), (-231691189/288230376151711744)), (35/144115188075855872), by norm_num⟩
  | 15 => ⟨((1034342889/4611686018427387904), (397752089/4611686018427387904)), (61/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-416177665/18446744073709551616), (-160039323/18446744073709551616)), (25/9223372036854775808), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-903517344641/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779818150536005/633825300114114700748351602688), (-2140954440597/316912650057057350374175801344)), (5789/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((7386412894219/154742504910672534362390528), (-4816528477725/39614081257132168796771975168)), (52113/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945384819895599/1237940039285380274899124224), (-5116833556703/2475880078570760549798248448)), (27693/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443108726282835/38685626227668133590597632), (-1279003614751/38685626227668133590597632)), (13851/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550718834214167/9671406556917033397649408), (-2397696602715/4835703278458516698824704)), (6495/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629903685747159/302231454903657293676544), (-1048774659725/151115727451828646838272)), (11371/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889445454570831/75557863725914323419136), (-1703850779671/18889465931478580854784)), (36973/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298777797635611/4722366482869645213696), (-638765506411/590295810358705651712)), (27745/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405787013975843/147573952589676412928), (-3512049671253/295147905179352825856)), (76349/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912797686982823/36893488147419103232), (-8776641882081/73786976294838206464)), (47755/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912518499820393/4611686018427387904), (-9868933225805/9223372036854775808)), (3361/288230376151711744), by norm_num⟩
  | 6 => ⟨((1596278327701093/1152921504606846976), (-9862946015515/1152921504606846976)), (107681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74786162898207/9007199254740992), (-8623340654643/144115188075855872)), (47183/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494618062703877/36028797018963968), (-12921533049075/36028797018963968)), (141839/36028797018963968), by norm_num⟩
  | 3 => ⟨((746477691902985/4503599627370496), (-8064160823953/4503599627370496)), (11113/562949953421312), by norm_num⟩
  | 2 => ⟨((1117629676038313/2251799813685248), (-1005807080347/140737488355328)), (178573/2251799813685248), by norm_num⟩
  | 1 => ⟨((278357640494851/281474976710656), (-24050792611413/1125899906842624)), (134887/562949953421312), by norm_num⟩
  | 0 => ⟨((1100707310641675/1125899906842624), (-47746944468581/1125899906842624)), (136807/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100707310641675/1125899906842624), (-47746944468581/1125899906842624)), (521877289892101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((268513392186241/281474976710656), (-93357163488451/1125899906842624)), (1116381/1125899906842624), by norm_num⟩
  | 2 => ⟨((1016853719945473/1125899906842624), (-11132272283185/70368744177664)), (1157541/562949953421312), by norm_num⟩
  | 3 => ⟨((55636942347841/70368744177664), (-40216336865493/140737488355328)), (2457105/562949953421312), by norm_num⟩
  | 4 => ⟨((611892327491951/1125899906842624), (-63593973198601/140737488355328)), (10579339/1125899906842624), by norm_num⟩
  | 5 => ⟨((205318146668739/2251799813685248), (-1105964437185569/2251799813685248)), (5264977/281474976710656), by norm_num⟩
  | 6 => ⟨((-1048940307917429/4503599627370496), (-201682731426157/2251799813685248)), (98109933/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-679034185/16777216)), (1/33554432), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1511914093/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((455783299613089/4503599627370496), (-52827349892379/281474976710656)), (63274069/4503599627370496), by norm_num⟩
  | 1 => ⟨((-389410993/2147483648), (722151981/2147483648)), (7/268435456), by norm_num⟩
  | 2 => ⟨((348865417/2147483648), (-646961325/2147483648)), (103/4294967296), by norm_num⟩
  | 3 => ⟨((-416721943/4294967296), (772799387/4294967296)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((46666593/1073741824), (-346167655/4294967296)), (115/17179869184), by norm_num⟩
  | 5 => ⟨((-535137983/34359738368), (496199339/17179869184)), (21/8589934592), by norm_num⟩
  | 6 => ⟨((639225699/137438953472), (-592713243/68719476736)), (51/68719476736), by norm_num⟩
  | 7 => ⟨((-654479257/549755813888), (606856895/274877906944)), (107/549755813888), by norm_num⟩
  | 8 => ⟨((586334703/2199023255552), (-271835397/549755813888)), (49/1099511627776), by norm_num⟩
  | 9 => ⟨((-29182521/549755813888), (54118183/549755813888)), (5/549755813888), by norm_num⟩
  | 10 => ⟨((669287147/70368744177664), (-155146827/8796093022208)), (29/17592186044416), by norm_num⟩
  | 11 => ⟨((-436073303/281474976710656), (808685953/281474976710656)), (77/281474976710656), by norm_num⟩
  | 12 => ⟨((520892313/2251799813685248), (-241495119/562949953421312)), (47/1125899906842624), by norm_num⟩
  | 13 => ⟨((-574346913/18014398509481984), (1065110563/18014398509481984)), (53/9007199254740992), by norm_num⟩
  | 14 => ⟨((588052297/144115188075855872), (-1090526821/144115188075855872)), (55/72057594037927936), by norm_num⟩
  | 15 => ⟨((-561945745/1152921504606846976), (521056469/576460752303423488)), (107/1152921504606846976), by norm_num⟩
  | 16 => ⟨((503435805/9223372036854775808), (-466803931/4611686018427387904)), (49/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-1401941092949/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444895952506953/158456325028528675187087900672), (-830286753127/316912650057057350374175801344)), (23091/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890658590027531/39614081257132168796771975168), (-1867888753701/39614081257132168796771975168)), (51961/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472622685285053/618970019642690137449562112), (-1984318734965/2475880078570760549798248448)), (27607/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772156744949407/154742504910672534362390528), (-495991651985/38685626227668133590597632)), (55221/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550458843347947/9671406556917033397649408), (-1859594634247/9671406556917033397649408)), (51777/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78723791464507/37778931862957161709568), (-25418301997/9444732965739290427392)), (177/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1889078523106037/75557863725914323419136), (-2642802378001/75557863725914323419136)), (73645/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298503883769383/4722366482869645213696), (-990744279985/2361183241434822606848)), (27623/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202846688824881/73786976294838206464), (-2723550614351/590295810358705651712)), (37991/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825130319228571/73786976294838206464), (-3402944616461/73786976294838206464)), (47503/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824518108479239/9223372036854775808), (-3826259868073/9223372036854775808)), (53461/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797882399860891/576460752303423488), (-3823695253727/1152921504606846976)), (26743/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196135294597793/144115188075855872), (-3342850104003/144115188075855872)), (93657/144115188075855872), by norm_num⟩
  | 4 => ⟨((746982562268483/18014398509481984), (-5008513537679/36028797018963968)), (70299/18014398509481984), by norm_num⟩
  | 3 => ⟨((373040053912223/2251799813685248), (-6250570035079/9007199254740992)), (21993/1125899906842624), by norm_num⟩
  | 2 => ⟨((558432960312343/1125899906842624), (-6235484076527/2251799813685248)), (352481/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112363131604515/1125899906842624), (-2328896922197/281474976710656)), (530205/2251799813685248), by norm_num⟩
  | 0 => ⟨((1098883287655789/1125899906842624), (-18481079843641/1125899906842624)), (1066365/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098883287655789/1125899906842624), (-18481079843641/1125899906842624)), (4067859658248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1072211590249069/1125899906842624), (-72150462592935/2251799813685248)), (1058281/1125899906842624), by norm_num⟩
  | 2 => ⟨((509963747653039/562949953421312), (-137419963824173/2251799813685248)), (520863/281474976710656), by norm_num⟩
  | 3 => ⟨((1839472634776077/2251799813685248), (-7780354111433/70368744177664)), (2014499/562949953421312), by norm_num⟩
  | 4 => ⟨((737559535701397/1125899906842624), (-12711386145313/70368744177664)), (14946865/2251799813685248), by norm_num⟩
  | 5 => ⟨((892849808742531/2251799813685248), (-532930020168477/2251799813685248)), (24982913/2251799813685248), by norm_num⟩
  | 6 => ⟨((455783299613089/4503599627370496), (-52827349892379/281474976710656)), (63274069/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1511914093/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-820994399/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((400335618447841/9007199254740992), (408282951376135/2251799813685248)), (123847691/4503599627370496), by norm_num⟩
  | 1 => ⟨((-371464321/4294967296), (-189419255/536870912)), (29/536870912), by norm_num⟩
  | 2 => ⟨((22588631/268435456), (1474371403/4294967296)), (227/4294967296), by norm_num⟩
  | 3 => ⟨((-234429047/4294967296), (-478165713/2147483648)), (149/4294967296), by norm_num⟩
  | 4 => ⟨((228088931/8589934592), (465233757/4294967296)), (73/4294967296), by norm_num⟩
  | 5 => ⟨((-355072453/34359738368), (-1448484943/34359738368)), (229/34359738368), by norm_num⟩
  | 6 => ⟨((115156515/34359738368), (939540517/68719476736)), (75/34359738368), by norm_num⟩
  | 7 => ⟨((-32012033/34359738368), (-65295051/17179869184)), (21/34359738368), by norm_num⟩
  | 8 => ⟨((15573135/68719476736), (1016466419/1099511627776)), (165/1099511627776), by norm_num⟩
  | 9 => ⟨((-215494553/4398046511104), (-3433945/17179869184)), (145/4398046511104), by norm_num⟩
  | 10 => ⟨((167733215/17592186044416), (684251999/17592186044416)), (227/35184372088832), by norm_num⟩
  | 11 => ⟨((-59344321/35184372088832), (-60522405/8796093022208)), (81/70368744177664), by norm_num⟩
  | 12 => ⟨((76985811/281474976710656), (628112865/562949953421312)), (53/281474976710656), by norm_num⟩
  | 13 => ⟨((-92189213/2251799813685248), (-94019323/562949953421312)), (1/35184372088832), by norm_num⟩
  | 14 => ⟨((205019343/36028797018963968), (1672714559/72057594037927936)), (287/72057594037927936), by norm_num⟩
  | 15 => ⟨((-106386459/144115188075855872), (-867987263/288230376151711744)), (151/288230376151711744), by norm_num⟩
  | 16 => ⟨((414036981/4611686018427387904), (211128153/576460752303423488)), (37/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (866499186405/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889688957820029/316912650057057350374175801344), (2052254760127/633825300114114700748351602688)), (46201/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945213473700287/19807040628566084398385987584), (2308442595769/39614081257132168796771975168)), (51983/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890244603945807/2475880078570760549798248448), (2452300004361/2475880078570760549798248448)), (55239/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771910588773737/154742504910672534362390528), (2451827315893/154742504910672534362390528)), (110495/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775114025897123/4835703278458516698824704), (2298085979329/9671406556917033397649408)), (103607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4919448049671/2361183241434822606848), (2010323217511/604462909807314587353088)), (45337/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236093787007495/9444732965739290427392), (1632917097809/37778931862957161709568)), (147379/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162282210078133/590295810358705651712), (2448552487101/4722366482869645213696)), (27641/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622434928006399/590295810358705651712), (1682711246513/295147905179352825856)), (19009/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912353505653795/36893488147419103232), (131399160995/2305843009213693952)), (190163/73786976294838206464), by norm_num⟩
  | 7 => ⟨((14250326389617/72057594037927936), (4727614270439/9223372036854775808)), (13377/576460752303423488), by norm_num⟩
  | 6 => ⟨((797644166580537/576460752303423488), (4724171814179/1152921504606846976)), (214155/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597859117078843/72057594037927936), (4129780254997/144115188075855872)), (187525/144115188075855872), by norm_num⟩
  | 4 => ⟨((23333425489725/562949953421312), (386683557303/2251799813685248)), (140783/18014398509481984), by norm_num⟩
  | 3 => ⟨((745688661953805/4503599627370496), (482509540373/562949953421312)), (176223/4503599627370496), by norm_num⟩
  | 2 => ⟨((2232164498730429/4503599627370496), (7699905004533/2251799813685248)), (706357/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222371410134339/2251799813685248), (5749671844837/562949953421312)), (132901/281474976710656), by norm_num⟩
  | 0 => ⟨((2193041860285491/2251799813685248), (45594526153893/2251799813685248)), (535287/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193041860285491/2251799813685248), (45594526153893/2251799813685248)), (2041957857372093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2134893923932623/2251799813685248), (2775299558371/70368744177664)), (266079/140737488355328), by norm_num⟩
  | 2 => ⟨((2020554800764533/2251799813685248), (84198890196193/1125899906842624)), (8408291/2251799813685248), by norm_num⟩
  | 3 => ⟨((1800463729418453/2251799813685248), (75552218616865/562949953421312)), (4086809/562949953421312), by norm_num⟩
  | 4 => ⟨((1399031751400999/2251799813685248), (241636096548275/1125899906842624)), (3816157/281474976710656), by norm_num⟩
  | 5 => ⟨((765493370383917/2251799813685248), (600509102631779/2251799813685248)), (12759869/562949953421312), by norm_num⟩
  | 6 => ⟨((400335618447841/9007199254740992), (408282951376135/2251799813685248)), (123847691/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-820994399/16777216)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1754664633/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-660986422737351/9007199254740992), (-1344910547704741/9007199254740992)), (397302337/9007199254740992), by norm_num⟩
  | 1 => ⟨((655404389/4294967296), (333388193/1073741824)), (397/4294967296), by norm_num⟩
  | 2 => ⟨((-681437557/4294967296), (-346630629/1073741824)), (13/134217728), by norm_num⟩
  | 3 => ⟨((472336521/4294967296), (961064173/4294967296)), (291/4294967296), by norm_num⟩
  | 4 => ⟨((-122774523/2147483648), (-999238383/8589934592)), (305/8589934592), by norm_num⟩
  | 5 => ⟨((408483909/17179869184), (415571561/8589934592)), (1/67108864), by norm_num⟩
  | 6 => ⟨((-141569735/17179869184), (-1152209023/68719476736)), (179/34359738368), by norm_num⟩
  | 7 => ⟨((336441129/137438953472), (1369115033/274877906944)), (107/68719476736), by norm_num⟩
  | 8 => ⟨((-174902415/274877906944), (-711748669/549755813888)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((323288309/2199023255552), (1315590889/4398046511104)), (417/4398046511104), by norm_num⟩
  | 10 => ⟨((-33612957/1099511627776), (-1094277739/17592186044416)), (349/17592186044416), by norm_num⟩
  | 11 => ⟨((406668679/70368744177664), (827449669/70368744177664)), (133/35184372088832), by norm_num⟩
  | 12 => ⟨((-563762497/562949953421312), (-573544405/281474976710656)), (93/140737488355328), by norm_num⟩
  | 13 => ⟨((360711125/2251799813685248), (366969865/1125899906842624)), (15/140737488355328), by norm_num⟩
  | 14 => ⟨((-428615827/18014398509481984), (-872105579/18014398509481984)), (9/562949953421312), by norm_num⟩
  | 15 => ⟨((475350163/144115188075855872), (967196037/144115188075855872)), (161/72057594037927936), by norm_num⟩
  | 16 => ⟨((-247115719/576460752303423488), (-1005613809/1152921504606846976)), (337/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-2641173581877/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779197293952077/633825300114114700748351602688), (-3127141688549/633825300114114700748351602688)), (138761/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118138975548169/2475880078570760549798248448), (-439683763129/4951760157141521099596496896)), (19517/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472507093803855/618970019642690137449562112), (-3736627078921/2475880078570760549798248448)), (165929/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771694156083605/154742504910672534362390528), (-1867928325917/77371252455336267181195264)), (10373/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550024929579275/9671406556917033397649408), (-3501547162243/9671406556917033397649408)), (38909/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314800188091583/151115727451828646838272), (-765758866039/151115727451828646838272)), (68111/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888460724553537/75557863725914323419136), (-4975898621893/75557863725914323419136)), (110719/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298040147569031/4722366482869645213696), (-3730582020439/4722366482869645213696)), (83073/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622135244734929/590295810358705651712), (-1281842549531/147573952589676412928)), (14285/36893488147419103232), by norm_num⟩
  | 8 => ⟨((228041443166125/9223372036854775808), (-800742955857/9223372036854775808)), (35733/9223372036854775808), by norm_num⟩
  | 7 => ⟨((56988068603661/288230376151711744), (-7202193245741/9223372036854775808)), (321823/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797431637049941/576460752303423488), (-7196579035287/1152921504606846976)), (161053/576460752303423488), by norm_num⟩
  | 5 => ⟨((597672325026003/72057594037927936), (-6290694088371/144115188075855872)), (141081/72057594037927936), by norm_num⟩
  | 4 => ⟨((746387774714021/18014398509481984), (-1177928068709/4503599627370496)), (423879/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490666956884027/9007199254740992), (-5878610460113/4503599627370496)), (530965/9007199254740992), by norm_num⟩
  | 2 => ⟨((557681638103191/1125899906842624), (-11724169803401/2251799813685248)), (266321/1125899906842624), by norm_num⟩
  | 1 => ⟨((277521468124463/281474976710656), (-17503761901281/1125899906842624)), (803163/1125899906842624), by norm_num⟩
  | 0 => ⟨((547118313040313/562949953421312), (-8669590869165/281474976710656)), (811589/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547118313040313/562949953421312), (-8669590869165/281474976710656)), (3095966341258811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((531197843473171/562949953421312), (-67406232504471/1125899906842624)), (1627525/562949953421312), by norm_num⟩
  | 2 => ⟨((1996875545738673/2251799813685248), (-993817399015/8796093022208)), (13065325/2251799813685248), by norm_num⟩
  | 3 => ⟨((108879122550115/140737488355328), (-451229803052835/2251799813685248)), (26124767/2251799813685248), by norm_num⟩
  | 4 => ⟨((1257298921251743/2251799813685248), (-698172258137985/2251799813685248)), (50892039/2251799813685248), by norm_num⟩
  | 5 => ⟨((242773817792875/1125899906842624), (-779652988396135/2251799813685248)), (88389667/2251799813685248), by norm_num⟩
  | 6 => ⟨((-660986422737351/9007199254740992), (-1344910547704741/9007199254740992)), (397302337/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1754664633/33554432)), (3/33554432), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile033Terms0
