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
namespace Reinmann.XiBand97.Tile018Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27177/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27177/1280))
  have he : value ((69/80), (27177/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-987635957/67108864)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-339233650704477/1125899906842624), (-1036113820654313/2251799813685248)), (40839923/1125899906842624), by norm_num⟩
  | 1 => ⟨((448491761/2147483648), (684909223/2147483648)), (7/268435456), by norm_num⟩
  | 2 => ⟨((-621741599/8589934592), (-474742897/4294967296)), (5/536870912), by norm_num⟩
  | 3 => ⟨((574611249/34359738368), (438755601/17179869184)), (19/8589934592), by norm_num⟩
  | 4 => ⟨((-398290167/137438953472), (-1216488831/274877906944)), (27/68719476736), by norm_num⟩
  | 5 => ⟨((220858965/549755813888), (674564643/1099511627776)), (61/1099511627776), by norm_num⟩
  | 6 => ⟨((-816468101/17592186044416), (-623430107/8796093022208)), (115/17592186044416), by norm_num⟩
  | 7 => ⟨((646780071/140737488355328), (987723019/140737488355328)), (93/140737488355328), by norm_num⟩
  | 8 => ⟨((-448313783/1125899906842624), (-342318713/562949953421312)), (33/562949953421312), by norm_num⟩
  | 9 => ⟨((138109971/4503599627370496), (843652447/18014398509481984)), (83/18014398509481984), by norm_num⟩
  | 10 => ⟨((-612675437/288230376151711744), (-116955063/36028797018963968)), (47/144115188075855872), by norm_num⟩
  | 11 => ⟨((617708003/4611686018427387904), (943325931/4611686018427387904)), (97/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-285441707/36893488147419103232), (-871818279/73786976294838206464)), (23/18446744073709551616), by norm_num⟩
  | 13 => ⟨((487023051/1180591620717411303424), (743751855/1180591620717411303424)), (5/73786976294838206464), by norm_num⟩
  | 14 => ⟨((-385804177/18889465931478580854784), (-589176573/18889465931478580854784)), (129/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((35655877/37778931862957161709568), (435611819/302231454903657293676544)), (97/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-197718165/4835703278458516698824704), (-1207772417/19342813113834066795298816)), (137/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1400667033295/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781042540690045/633825300114114700748351602688), (-3323313211881/633825300114114700748351602688)), (17349/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892299232905613/39614081257132168796771975168), (-934628358817/9903520314283042199192993792)), (39043/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29566146971841/38685626227668133590597632), (-3971926596259/2475880078570760549798248448)), (10373/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886949413647303/77371252455336267181195264), (-3971652077361/154742504910672534362390528)), (41503/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((6062857134723/37778931862957161709568), (-3723132058757/9671406556917033397649408)), (4865/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1261008554706839/604462909807314587353088), (-3257448689327/604462909807314587353088)), (17033/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472849421507405/18889465931478580854784), (-1323201667479/18889465931478580854784)), (3461/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((325060560198007/1180591620717411303424), (-1984562887375/2361183241434822606848)), (20775/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625162102187965/590295810358705651712), (-2728384402075/295147905179352825856)), (7145/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828113585323983/73786976294838206464), (-6819791616939/73786976294838206464)), (35747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913935441437943/4611686018427387904), (-7670656549465/9223372036854775808)), (40245/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599113325596293/1152921504606846976), (-7668643610305/1152921504606846976)), (80565/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199060477117325/144115188075855872), (-6707796315909/144115188075855872)), (70579/144115188075855872), by norm_num⟩
  | 4 => ⟨((374585836999619/9007199254740992), (-314286096199/1125899906842624)), (26509/9007199254740992), by norm_num⟩
  | 3 => ⟨((1497616293016005/9007199254740992), (-12563487079503/9007199254740992)), (16605/1125899906842624), by norm_num⟩
  | 2 => ⟨((561148483645355/1125899906842624), (-3137881580749/562949953421312)), (33321/562949953421312), by norm_num⟩
  | 1 => ⟨((560223601445849/562949953421312), (-18797298199813/1125899906842624)), (201033/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114801905269433/1125899906842624), (-37474096660787/1125899906842624)), (406511/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114801905269433/1125899906842624), (-37474096660787/1125899906842624)), (1550716404441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102566020769139/1125899906842624), (-74209428567855/1125899906842624)), (832069/1125899906842624), by norm_num⟩
  | 2 => ⟨((134353060994999/140737488355328), (-145342927665857/1125899906842624)), (217417/140737488355328), by norm_num⟩
  | 3 => ⟨((503651837256303/562949953421312), (-277499157531943/1125899906842624)), (1884965/562949953421312), by norm_num⟩
  | 4 => ⟨((832804856414935/1125899906842624), (-124134445414405/281474976710656)), (8603993/1125899906842624), by norm_num⟩
  | 5 => ⟨((198514165219357/562949953421312), (-367278719400201/562949953421312)), (20317357/1125899906842624), by norm_num⟩
  | 6 => ⟨((-339233650704477/1125899906842624), (-1036113820654313/2251799813685248)), (40839923/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-987635957/67108864)), (3/134217728), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1565365957/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-25533521475559/281474976710656), (1697525358273345/4503599627370496)), (146520439/4503599627370496), by norm_num⟩
  | 1 => ⟨((214015507/2147483648), (-889264211/2147483648)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-117560033/2147483648), (488478295/2147483648)), (89/4294967296), by norm_num⟩
  | 3 => ⟨((344407725/17179869184), (-1431062021/17179869184)), (133/17179869184), by norm_num⟩
  | 4 => ⟨((-378370559/68719476736), (1572182323/68719476736)), (149/68719476736), by norm_num⟩
  | 5 => ⟨((332546037/274877906944), (-86360941/17179869184)), (67/137438953472), by norm_num⟩
  | 6 => ⟨((-121779721/549755813888), (1012023371/1099511627776)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((152901369/4398046511104), (-155109/1073741824)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-167979323/35184372088832), (697977461/35184372088832)), (143/70368744177664), by norm_num⟩
  | 9 => ⟨((164039243/281474976710656), (-681605881/281474976710656)), (71/281474976710656), by norm_num⟩
  | 10 => ⟨((-288344845/4503599627370496), (1198112955/4503599627370496)), (127/4503599627370496), by norm_num⟩
  | 11 => ⟨((115192433/18014398509481984), (-957281175/36028797018963968)), (13/4503599627370496), by norm_num⟩
  | 12 => ⟨((-337471527/576460752303423488), (701120575/288230376151711744)), (155/576460752303423488), by norm_num⟩
  | 13 => ⟨((28519259/576460752303423488), (-474005957/2305843009213693952)), (107/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-71615105/18446744073709551616), (1190282901/73786976294838206464)), (137/73786976294838206464), by norm_num⟩
  | 15 => ⟨((167844767/590295810358705651712), (-1394836717/1180591620717411303424)), (163/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-368792647/18889465931478580854784), (766192379/9444732965739290427392)), (91/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (2353781185205/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780504002836731/633825300114114700748351602688), (2790759038965/633825300114114700748351602688)), (23119/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891693529328821/39614081257132168796771975168), (3139330378399/39614081257132168796771975168)), (26013/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891590025580247/2475880078570760549798248448), (104225471271/77371252455336267181195264)), (6911/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1773255648562477/154742504910672534362390528), (1667425587501/77371252455336267181195264)), (13825/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193936082616813/1208925819614629174706176), (1563018157687/4835703278458516698824704)), (3241/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260481349357303/604462909807314587353088), (2734895101917/604462909807314587353088)), (45385/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890541379552529/75557863725914323419136), (4443479499571/75557863725914323419136)), (36887/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299600362881339/4722366482869645213696), (3331975186613/4722366482869645213696)), (55351/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203035011498759/73786976294838206464), (17892323707/2305843009213693952)), (76139/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827011930496851/73786976294838206464), (2861998489429/36893488147419103232)), (95223/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826632700877721/9223372036854775808), (3218684936447/4611686018427387904)), (107193/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597876618262969/1152921504606846976), (3217355624401/576460752303423488)), (107277/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197980017281823/144115188075855872), (5627381098505/144115188075855872)), (93961/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496725976609891/36028797018963968), (8435088434317/36028797018963968)), (70565/18014398509481984), by norm_num⟩
  | 3 => ⟨((373900096589543/2251799813685248), (10533388302281/9007199254740992)), (176743/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120289772840277/2251799813685248), (5258838371391/1125899906842624)), (22155/281474976710656), by norm_num⟩
  | 1 => ⟨((558729097250823/562949953421312), (15737225180487/1125899906842624)), (133551/562949953421312), by norm_num⟩
  | 0 => ⟨((277227759209449/281474976710656), (31317225695325/1125899906842624)), (269591/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277227759209449/281474976710656), (31317225695325/1125899906842624)), (1028408052684593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1091307416874287/1125899906842624), (30844675450835/562949953421312)), (136511/140737488355328), by norm_num⟩
  | 2 => ⟨((1054397726561049/1125899906842624), (119587977176311/1125899906842624)), (2236743/1125899906842624), by norm_num⟩
  | 3 => ⟨((487367160625135/562949953421312), (223986680329945/1125899906842624)), (145767/35184372088832), by norm_num⟩
  | 4 => ⟨((799304590566759/1125899906842624), (24239222276069/70368744177664)), (9932477/1125899906842624), by norm_num⟩
  | 5 => ⟨((433855276135937/1125899906842624), (275328512160371/562949953421312)), (20945313/1125899906842624), by norm_num⟩
  | 6 => ⟨((-25533521475559/281474976710656), (1697525358273345/4503599627370496)), (146520439/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1565365957/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-987635957/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-544643415052053/4503599627370496), (1248724408945339/4503599627370496)), (177740631/4503599627370496), by norm_num⟩
  | 1 => ⟨((180014633/1073741824), (-825452617/2147483648)), (119/2147483648), by norm_num⟩
  | 2 => ⟨((-499106541/4294967296), (286080077/1073741824)), (167/4294967296), by norm_num⟩
  | 3 => ⟨((461272389/8589934592), (-1057576527/8589934592)), (39/2147483648), by norm_num⟩
  | 4 => ⟨((-39966207/2147483648), (183264047/4294967296)), (109/17179869184), by norm_num⟩
  | 5 => ⟨((354591535/68719476736), (-50811583/4294967296)), (123/68719476736), by norm_num⟩
  | 6 => ⟨((-81928041/68719476736), (23479937/8589934592)), (115/274877906944), by norm_num⟩
  | 7 => ⟨((259603157/1099511627776), (-1190403813/2199023255552)), (23/274877906944), by norm_num⟩
  | 8 => ⟨((-359886393/8796093022208), (825125047/8796093022208)), (129/8796093022208), by norm_num⟩
  | 9 => ⟨((221737101/35184372088832), (-254192489/17592186044416)), (161/70368744177664), by norm_num⟩
  | 10 => ⟨((-122957157/140737488355328), (1127633965/562949953421312)), (181/562949953421312), by norm_num⟩
  | 11 => ⟨((123967137/1125899906842624), (-568448221/2251799813685248)), (185/4503599627370496), by norm_num⟩
  | 12 => ⟨((-57284981/4503599627370496), (525357709/18014398509481984)), (173/36028797018963968), by norm_num⟩
  | 13 => ⟨((390960473/288230376151711744), (-28011555/9007199254740992)), (75/144115188075855872), by norm_num⟩
  | 14 => ⟨((-619412913/4611686018427387904), (710075625/2305843009213693952)), (15/288230376151711744), by norm_num⟩
  | 15 => ⟨((457967269/36893488147419103232), (-1049998757/36893488147419103232)), (45/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-634877443/590295810358705651712), (363901839/147573952589676412928)), (63/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (1290941125353/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1780120021576469/633825300114114700748351602688), (3059955676419/633825300114114700748351602688)), (271/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((1891261544848541/39614081257132168796771975168), (860518544901/9903520314283042199192993792)), (39031/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891131030236131/2475880078570760549798248448), (3656756453785/2475880078570760549798248448)), (41479/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772796639955149/154742504910672534362390528), (457031643925/19342813113834066795298816)), (82977/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775529163159117/4835703278458516698824704), (3427202579617/9671406556917033397649408)), (77811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260104792572063/604462909807314587353088), (2998267517399/604462909807314587353088)), (8513/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944964724321061/37778931862957161709568), (4871182100181/75557863725914323419136)), (110707/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299141391939005/4722366482869645213696), (3652509308071/4722366482869645213696)), (83063/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811824485081325/295147905179352825856), (1255193695079/147573952589676412928)), (57133/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826222973394213/73786976294838206464), (6273830269665/73786976294838206464)), (142911/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456436262334303/2305843009213693952), (7055119137885/9223372036854775808)), (80443/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798494437042273/576460752303423488), (7051444421159/1152921504606846976)), (629/4503599627370496), by norm_num⟩
  | 5 => ⟨((598601569046199/72057594037927936), (6165880058963/144115188075855872)), (35263/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495560454716753/36028797018963968), (9240553093803/36028797018963968)), (13243/2251799813685248), by norm_num⟩
  | 3 => ⟨((186767891899579/1125899906842624), (11536225552389/9007199254740992)), (66351/2251799813685248), by norm_num⟩
  | 2 => ⟨((1118832011754867/2251799813685248), (359829054167/70368744177664)), (133111/1125899906842624), by norm_num⟩
  | 1 => ⟨((557635162201783/562949953421312), (538048920193/35184372088832)), (401379/1125899906842624), by norm_num⟩
  | 0 => ⟨((552265329995449/562949953421312), (8554569623633/281474976710656)), (202741/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552265329995449/562949953421312), (8554569623633/281474976710656)), (773395539403819949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((270631758842299/281474976710656), (16784412850387/281474976710656)), (1640439/1125899906842624), by norm_num⟩
  | 2 => ⟨((1036821577988349/1125899906842624), (129102635663557/1125899906842624)), (1675065/562949953421312), by norm_num⟩
  | 3 => ⟨((939987193901513/1125899906842624), (29722091106331/140737488355328)), (6938447/1125899906842624), by norm_num⟩
  | 4 => ⟨((734557438800399/1125899906842624), (198514165219345/562949953421312)), (14516127/1125899906842624), by norm_num⟩
  | 5 => ⟨((169616825352245/562949953421312), (518056910327123/1125899906842624)), (58357739/2251799813685248), by norm_num⟩
  | 6 => ⟨((-544643415052053/4503599627370496), (1248724408945339/4503599627370496)), (177740631/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-987635957/33554432)), (3/67108864), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-573304919/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-520592397856871/2251799813685248), (-211490949788921/2251799813685248)), (196801943/4503599627370496), by norm_num⟩
  | 1 => ⟨((199761663/536870912), (324613145/2147483648)), (153/2147483648), by norm_num⟩
  | 2 => ⟨((-160751997/536870912), (-522444703/4294967296)), (249/4294967296), by norm_num⟩
  | 3 => ⟨((172480239/1073741824), (280280771/4294967296)), (269/8589934592), by norm_num⟩
  | 4 => ⟨((-1110384943/17179869184), (-451094499/17179869184)), (109/8589934592), by norm_num⟩
  | 5 => ⟨((357419125/17179869184), (580806871/68719476736)), (283/68719476736), by norm_num⟩
  | 6 => ⟨((-383495927/68719476736), (-155795433/68719476736)), (153/137438953472), by norm_num⟩
  | 7 => ⟨((1410772307/1099511627776), (71640879/137438953472)), (283/1099511627776), by norm_num⟩
  | 8 => ⟨((-1135275219/4398046511104), (-461206187/4398046511104)), (115/2199023255552), by norm_num⟩
  | 9 => ⟨((812068879/17592186044416), (41237929/2199023255552)), (167/17592186044416), by norm_num⟩
  | 10 => ⟨((-1045579553/140737488355328), (-424767273/140737488355328)), (217/140737488355328), by norm_num⟩
  | 11 => ⟨((1223851181/1125899906842624), (497190221/1125899906842624)), (1/4398046511104), by norm_num⟩
  | 12 => ⟨((-328285415/2251799813685248), (-33341533/562949953421312)), (277/9007199254740992), by norm_num⟩
  | 13 => ⟨((1300566137/72057594037927936), (528355715/72057594037927936)), (69/18014398509481984), by norm_num⟩
  | 14 => ⟨((-598051557/288230376151711744), (-242958777/288230376151711744)), (1/2251799813685248), by norm_num⟩
  | 15 => ⟨((513347653/2305843009213693952), (208547769/2305843009213693952)), (221/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-826201175/36893488147419103232), (-167822343/18446744073709551616)), (179/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-3589619312143/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779818282580429/633825300114114700748351602688), (-4252940716617/633825300114114700748351602688)), (46309/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890921857185817/39614081257132168796771975168), (-4783943835703/39614081257132168796771975168)), (52111/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890769815556137/2475880078570760549798248448), (-1270554335453/618970019642690137449562112)), (6923/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772435091841683/154742504910672534362390528), (-5081403837897/154742504910672534362390528)), (55401/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550719020879605/9671406556917033397649408), (-4762951695185/9671406556917033397649408)), (51957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629903773222725/302231454903657293676544), (-4166718268579/604462909807314587353088)), (45481/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889445760639871/75557863725914323419136), (-6769296184013/75557863725914323419136)), (147883/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324694511556805/1180591620717411303424), (-2537776815097/2361183241434822606848)), (55487/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623148428634165/590295810358705651712), (-6976580922139/590295810358705651712)), (9543/36893488147419103232), by norm_num⟩
  | 8 => ⟨((912797943107971/36893488147419103232), (-8717267748027/73786976294838206464)), (5969/2305843009213693952), by norm_num⟩
  | 7 => ⟨((28516213118309/144115188075855872), (-2450542555457/2305843009213693952)), (215089/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596279047098269/1152921504606846976), (-9796224201663/1152921504606846976)), (215345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598289662555925/72057594037927936), (-535312843823/9007199254740992)), (47179/36028797018963968), by norm_num⟩
  | 4 => ⟨((93413707438873/2251799813685248), (-12834123422335/36028797018963968)), (141825/18014398509481984), by norm_num⟩
  | 3 => ⟨((373239316331593/2251799813685248), (-8009611537521/4503599627370496)), (177787/4503599627370496), by norm_num⟩
  | 2 => ⟨((279408005690559/562949953421312), (-15984060957669/2251799813685248)), (357093/2251799813685248), by norm_num⟩
  | 1 => ⟨((139179404986059/140737488355328), (-23888133399843/1125899906842624)), (539443/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100721266612991/1125899906842624), (-23712062499953/562949953421312)), (1094143/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100721266612991/1125899906842624), (-23712062499953/562949953421312)), (4173824314597701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1074108143887731/1125899906842624), (-46363573369765/562949953421312)), (2231523/1125899906842624), by norm_num⟩
  | 2 => ⟨((508530986664143/562949953421312), (-88461667744257/562949953421312)), (2312657/562949953421312), by norm_num⟩
  | 3 => ⟨((445471744359181/562949953421312), (-159820598284251/562949953421312)), (9810033/1125899906842624), by norm_num⟩
  | 4 => ⟨((1228545808277741/2251799813685248), (-1011749769506497/2251799813685248)), (42191587/2251799813685248), by norm_num⟩
  | 5 => ⟨((215688447964427/2251799813685248), (-34499651423247/70368744177664)), (41976035/1125899906842624), by norm_num⟩
  | 6 => ⟨((-520592397856871/2251799813685248), (-211490949788921/2251799813685248)), (196801943/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-573304919/16777216)), (1/16777216), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1276500957/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((904169199597609/4503599627370496), (-161742907300469/2251799813685248)), (39880189/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1545003629/4294967296), (552757999/4294967296)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((1384137441/4294967296), (-247602345/2147483648)), (65/4294967296), by norm_num⟩
  | 3 => ⟨((-103335057/536870912), (73940641/1073741824)), (5/536870912), by norm_num⟩
  | 4 => ⟨((1481212535/17179869184), (-529935375/17179869184)), (37/8589934592), by norm_num⟩
  | 5 => ⟨((-530795317/17179869184), (379806691/34359738368)), (55/34359738368), by norm_num⟩
  | 6 => ⟨((634038357/68719476736), (-226840745/68719476736)), (67/137438953472), by norm_num⟩
  | 7 => ⟨((-1298336263/549755813888), (464507489/549755813888)), (35/274877906944), by norm_num⟩
  | 8 => ⟨((1163153147/2199023255552), (-208071423/1099511627776)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((-463131259/4398046511104), (331390171/8796093022208)), (13/2199023255552), by norm_num⟩
  | 10 => ⟨((663855855/35184372088832), (-237508591/35184372088832)), (77/70368744177664), by norm_num⟩
  | 11 => ⟨((-432534551/140737488355328), (309496921/281474976710656)), (13/70368744177664), by norm_num⟩
  | 12 => ⟨((129166313/281474976710656), (-184848013/1125899906842624)), (1/35184372088832), by norm_num⟩
  | 13 => ⟨((-1139372133/18014398509481984), (50954335/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 14 => ⟨((583280231/72057594037927936), (-417361885/144115188075855872)), (19/36028797018963968), by norm_num⟩
  | 15 => ⟨((-1114771069/1152921504606846976), (398833125/1152921504606846976)), (37/576460752303423488), by norm_num⟩
  | 16 => ⟨((499350405/4611686018427387904), (-178653257/4611686018427387904)), (17/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-447552881385/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779585133342315/633825300114114700748351602688), (-530118177727/633825300114114700748351602688)), (23063/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945330077736087/19807040628566084398385987584), (-149075382073/9903520314283042199192993792)), (25947/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945246250953725/1237940039285380274899124224), (-633470484115/2475880078570760549798248448)), (55139/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886079307660977/77371252455336267181195264), (-39584883575/9671406556917033397649408)), (27571/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775230356611341/4835703278458516698824704), (-593653912785/9671406556917033397649408)), (25849/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259582415910901/604462909807314587353088), (-129831966019/151115727451828646838272)), (22619/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889081588886709/75557863725914323419136), (-843684139943/75557863725914323419136)), (73515/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649253186862705/2361183241434822606848), (-39535467937/295147905179352825856)), (55141/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622777243799969/590295810358705651712), (-869462539719/590295810358705651712)), (75825/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114070965597805/4611686018427387904), (-1086351759729/73786976294838206464)), (47395/36893488147419103232), by norm_num⟩
  | 7 => ⟨((114032782323723/576460752303423488), (-305372753079/2305843009213693952)), (106651/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595772003710943/1152921504606846976), (-610336572487/576460752303423488)), (106667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299035622836091/36028797018963968), (-533584814241/72057594037927936)), (11669/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493977702563567/36028797018963968), (-799458756455/18014398509481984)), (140063/36028797018963968), by norm_num⟩
  | 3 => ⟨((373044762542197/2251799813685248), (-1995436347819/9007199254740992)), (175143/9007199254740992), by norm_num⟩
  | 2 => ⟨((558444703476989/1125899906842624), (-3981257379943/4503599627370496)), (87619/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112409934158607/1125899906842624), (-2973952392751/1125899906842624)), (32887/140737488355328), by norm_num⟩
  | 0 => ⟨((549511423645979/562949953421312), (-2950056425709/562949953421312)), (527157/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549511423645979/562949953421312), (-2950056425709/562949953421312)), (2010944370750045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1072756468135039/1125899906842624), (-23037070296927/2251799813685248)), (2069343/2251799813685248), by norm_num⟩
  | 2 => ⟨((1022003604654739/1125899906842624), (-21949700872801/1125899906842624)), (1992839/1125899906842624), by norm_num⟩
  | 3 => ⟨((927266777636215/1125899906842624), (-39848432843385/1125899906842624)), (923897/281474976710656), by norm_num⟩
  | 4 => ⟨((381133249097843/562949953421312), (-131273224882515/2251799813685248)), (12697611/2251799813685248), by norm_num⟩
  | 5 => ⟨((1024499683983659/2251799813685248), (-88875734716653/1125899906842624)), (583555/70368744177664), by norm_num⟩
  | 6 => ⟨((904169199597609/4503599627370496), (-161742907300469/2251799813685248)), (39880189/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1276500957/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1386322333/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-747696221753787/4503599627370496), (384444255207731/4503599627370496)), (37418837/2251799813685248), by norm_num⟩
  | 1 => ⟨((1387548129/4294967296), (-713438013/4294967296)), (141/4294967296), by norm_num⟩
  | 2 => ⟨((-1350021993/4294967296), (694143135/4294967296)), (139/4294967296), by norm_num⟩
  | 3 => ⟨((875673833/4294967296), (-112561681/1073741824)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((-212997825/2147483648), (438069835/8589934592)), (91/8589934592), by norm_num⟩
  | 5 => ⟨((663159407/17179869184), (-340977815/17179869184)), (9/2147483648), by norm_num⟩
  | 6 => ⟨((-107537385/8589934592), (442341461/68719476736)), (95/68719476736), by norm_num⟩
  | 7 => ⟨((478304203/137438953472), (-491860993/274877906944)), (27/68719476736), by norm_num⟩
  | 8 => ⟨((-930737003/1099511627776), (478558649/1099511627776)), (53/549755813888), by norm_num⟩
  | 9 => ⟨((804946925/4398046511104), (-103470237/1099511627776)), (47/2199023255552), by norm_num⟩
  | 10 => ⟨((-1253083513/35184372088832), (322150055/17592186044416)), (37/8796093022208), by norm_num⟩
  | 11 => ⟨((443343259/70368744177664), (-28494321/8796093022208)), (107/140737488355328), by norm_num⟩
  | 12 => ⟨((-1150274863/1125899906842624), (295719405/562949953421312)), (35/281474976710656), by norm_num⟩
  | 13 => ⟨((344358697/2251799813685248), (-177059505/2251799813685248)), (85/4503599627370496), by norm_num⟩
  | 14 => ⟨((-765818381/36028797018963968), (393762157/36028797018963968)), (3/1125899906842624), by norm_num⟩
  | 15 => ⟨((776153/281474976710656), (-102163437/72057594037927936)), (101/288230376151711744), by norm_num⟩
  | 16 => ⟨((-377581/1125899906842624), (198800869/1152921504606846976)), (99/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (3473638079211/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889685560619131/316912650057057350374175801344), (4113558555431/633825300114114700748351602688)), (46303/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890418912456743/39614081257132168796771975168), (1156761536369/9903520314283042199192993792)), (6513/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945117783335025/1237940039285380274899124224), (4915392073529/2475880078570760549798248448)), (55375/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771900989141099/154742504910672534362390528), (4914442007365/154742504910672534362390528)), (1731/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((775109227471663/4835703278458516698824704), (4606279980239/9671406556917033397649408)), (12987/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629684853311563/302231454903657293676544), (1007371407483/151115727451828646838272)), (45473/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888734562306905/75557863725914323419136), (6546021716395/75557863725914323419136)), (36963/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324561225622327/1180591620717411303424), (1226965128413/1180591620717411303424)), (55475/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622415770492989/590295810358705651712), (6745617770935/590295810358705651712)), (76325/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824680685468897/73786976294838206464), (8427986906653/73786976294838206464)), (95479/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456002223544583/2305843009213693952), (2368984321983/2305843009213693952)), (107513/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797625685726139/576460752303423488), (9469003163015/1152921504606846976)), (26909/288230376151711744), by norm_num⟩
  | 5 => ⟨((597840656493499/72057594037927936), (8277578057615/144115188075855872)), (94321/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493274710453019/36028797018963968), (6200385320987/18014398509481984)), (141761/36028797018963968), by norm_num⟩
  | 3 => ⟨((745640362381727/4503599627370496), (15473676286545/9007199254740992)), (177691/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115961818977249/2251799813685248), (15432759452931/2251799813685248)), (89213/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110945798755013/1125899906842624), (11523447879379/562949953421312)), (269481/1125899906842624), by norm_num⟩
  | 0 => ⟨((547902987681571/562949953421312), (22842557887327/562949953421312)), (546353/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547902987681571/562949953421312), (22842557887327/562949953421312)), (2084171299460982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064662674322235/1125899906842624), (44464008342813/562949953421312)), (553919/562949953421312), by norm_num⟩
  | 2 => ⟨((62483264004117/70368744177664), (168182516920529/1125899906842624)), (1135085/562949953421312), by norm_num⟩
  | 3 => ⟨((862580372318763/1125899906842624), (298672165559489/1125899906842624)), (4709771/1125899906842624), by norm_num⟩
  | 4 => ⟨((290807305449539/562949953421312), (915281176253143/2251799813685248)), (19430621/2251799813685248), by norm_num⟩
  | 5 => ⟨((228866965753219/2251799813685248), (945627407826283/2251799813685248)), (35870639/2251799813685248), by norm_num⟩
  | 6 => ⟨((-747696221753787/4503599627370496), (384444255207731/4503599627370496)), (37418837/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1386322333/33554432)), (1/33554432), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-92590871/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1477345678787767/9007199254740992), (-125635561981695/4503599627370496)), (53875715/4503599627370496), by norm_num⟩
  | 1 => ⟨((-91554343/268435456), (124574569/2147483648)), (109/4294967296), by norm_num⟩
  | 2 => ⟨((1523055233/4294967296), (-129522767/2147483648)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((-1055701441/4294967296), (89778341/2147483648)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((274408679/2147483648), (-46672203/2147483648)), (11/1073741824), by norm_num⟩
  | 5 => ⟨((-1825973781/34359738368), (310566777/34359738368)), (149/34359738368), by norm_num⟩
  | 6 => ⟨((632834289/34359738368), (-107634243/34359738368)), (105/68719476736), by norm_num⟩
  | 7 => ⟨((-1503933611/274877906944), (63948319/68719476736)), (127/274877906944), by norm_num⟩
  | 8 => ⟨((1563671013/1099511627776), (-132976791/549755813888)), (135/1099511627776), by norm_num⟩
  | 9 => ⟨((-180642359/549755813888), (245793301/4398046511104)), (127/4398046511104), by norm_num⟩
  | 10 => ⟨((601016361/8796093022208), (-3194455/274877906944)), (27/4398046511104), by norm_num⟩
  | 11 => ⟨((-908929737/70368744177664), (309186673/140737488355328)), (83/70368744177664), by norm_num⟩
  | 12 => ⟨((1260044169/562949953421312), (-214311871/562949953421312)), (117/562949953421312), by norm_num⟩
  | 13 => ⟨((-1612423501/4503599627370496), (274245543/4503599627370496)), (19/562949953421312), by norm_num⟩
  | 14 => ⟨((957982975/18014398509481984), (-81468225/9007199254740992)), (23/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1062437117/144115188075855872), (180702305/144115188075855872)), (13/18014398509481984), by norm_num⟩
  | 16 => ⟨((552318969/576460752303423488), (-46969985/288230376151711744)), (55/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-109725917647/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222400310946733/79228162514264337593543950336), (-64957580551/158456325028528675187087900672)), (46113/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945114874453479/19807040628566084398385987584), (-292263080409/39614081257132168796771975168)), (25939/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472508820309549/618970019642690137449562112), (-310472715627/2475880078570760549798248448)), (110243/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771701491716691/154742504910672534362390528), (-77602206883/38685626227668133590597632)), (110245/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96877016434057/604462909807314587353088), (-145470206637/4835703278458516698824704)), (103357/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629603812494073/302231454903657293676544), (-63626254991/151115727451828646838272)), (11305/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888472746826335/75557863725914323419136), (-413443498717/75557863725914323419136)), (18371/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649024955576461/2361183241434822606848), (-38746425563/590295810358705651712)), (55115/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405537470554189/147573952589676412928), (-106507508143/147573952589676412928)), (37893/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228043957380621/9223372036854775808), (-266133356583/36893488147419103232)), (94737/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911821659120337/4611686018427387904), (-299213950267/4611686018427387904)), (213171/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594891510977041/1152921504606846976), (-597963064713/1152921504606846976)), (213187/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195372853940909/144115188075855872), (-522695227529/144115188075855872)), (186557/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492824832082881/36028797018963968), (-97874893423/4503599627370496)), (4373/562949953421312), by norm_num⟩
  | 3 => ⟨((1490740732746787/9007199254740992), (-61057824915/562949953421312)), (21869/562949953421312), by norm_num⟩
  | 2 => ⟨((557727618617439/1125899906842624), (-1948390088651/4503599627370496)), (21875/140737488355328), by norm_num⟩
  | 1 => ⟨((277567254947547/281474976710656), (-2908972429113/2251799813685248)), (1050487/2251799813685248), by norm_num⟩
  | 0 => ⟨((547391102783777/562949953421312), (-5763721843885/2251799813685248)), (2102951/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547391102783777/562949953421312), (-5763721843885/2251799813685248)), (8022121438033293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1064517161091225/1125899906842624), (-11208847383639/2251799813685248)), (4100425/2251799813685248), by norm_num⟩
  | 2 => ⟨((2012906067059823/2251799813685248), (-2649438534327/281474976710656)), (1948643/562949953421312), by norm_num⟩
  | 3 => ⟨((1799157083419811/2251799813685248), (-37893747873233/2251799813685248)), (14082027/2251799813685248), by norm_num⟩
  | 4 => ⟨((718432041566919/1125899906842624), (-60553166839351/2251799813685248)), (22976643/2251799813685248), by norm_num⟩
  | 5 => ⟨((1830457303407381/4503599627370496), (-38638723576889/1125899906842624)), (61116663/4503599627370496), by norm_num⟩
  | 6 => ⟨((1477345678787767/9007199254740992), (-125635561981695/4503599627370496)), (53875715/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-92590871/2097152)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile018Terms0
