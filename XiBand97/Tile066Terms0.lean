/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile066Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨66,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (81741/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (81741/2560))
  have he : value ((69/80), (81741/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-2567700857/4294967296), (-380229050267/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-613089763777827/1125899906842624), (174165150460929/2251799813685248)), (397651/2251799813685248), by norm_num⟩
  | 1 => ⟨((415001407415/1099511627776), (-58946329587/1099511627776)), (137/1099511627776), by norm_num⟩
  | 2 => ⟨((-143828527739/1099511627776), (20429241079/1099511627776)), (97/2199023255552), by norm_num⟩
  | 3 => ⟨((265851569297/8796093022208), (-37761255613/8796093022208)), (91/8796093022208), by norm_num⟩
  | 4 => ⟨((-368548531411/70368744177664), (52348215725/70368744177664)), (1/549755813888), by norm_num⟩
  | 5 => ⟨((408733400715/562949953421312), (-58056029019/562949953421312)), (9/35184372088832), by norm_num⟩
  | 6 => ⟨((-47218734051/562949953421312), (13413790943/1125899906842624)), (135/4503599627370496), by norm_num⟩
  | 7 => ⟨((74810359719/9007199254740992), (-42503914847/36028797018963968)), (27/9007199254740992), by norm_num⟩
  | 8 => ⟨((-414836719327/576460752303423488), (29461468739/288230376151711744)), (19/72057594037927936), by norm_num⟩
  | 9 => ⟨((255593691017/4611686018427387904), (-36304238207/4611686018427387904)), (95/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-70865618519/18446744073709551616), (40262688569/73786976294838206464)), (107/73786976294838206464), by norm_num⟩
  | 11 => ⟨((142895428873/590295810358705651712), (-40593409547/1180591620717411303424)), (55/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-264126836369/18889465931478580854784), (18758138251/9444732965739290427392)), (13/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((112663859655/151115727451828646838272), (-16002646943/151115727451828646838272)), (45/151115727451828646838272), by norm_num⟩
  | 14 => ⟨((-356994910495/9671406556917033397649408), (50707152503/9671406556917033397649408)), (145/9671406556917033397649408), by norm_num⟩
  | 15 => ⟨((65986670849/38685626227668133590597632), (-18745343889/77371252455336267181195264)), (109/154742504910672534362390528), by norm_num⟩
  | 16 => ⟨((-91476949707/1237940039285380274899124224), (51973129061/4951760157141521099596496896)), (153/4951760157141521099596496896), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (1954241566513/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890518485688207/316912650057057350374175801344), (579594994995/79228162514264337593543950336)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118268289318755/2475880078570760549798248448), (163001254959/1237940039285380274899124224)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946112988793537/1237940039285380274899124224), (5541700332109/2475880078570760549798248448)), (109/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886945467563445/77371252455336267181195264), (346332181389/9671406556917033397649408)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((388020883786167/2417851639229258349412352), (5194572928953/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261001157446781/604462909807314587353088), (1136210303631/151115727451828646838272)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118211546411031/4722366482869645213696), (923074673547/9444732965739290427392)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300231725880223/4722366482869645213696), (5537774003609/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625146332699751/590295810358705651712), (951667840563/73786976294838206464)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((914045953480989/36893488147419103232), (4757515738765/36893488147419103232)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28560059249355/144115188075855872), (10702142423289/9223372036854775808)), (211/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199885357250311/144115188075855872), (1337412780885/144115188075855872)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199030021655061/144115188075855872), (9358687138401/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498290078294495/36028797018963968), (7015804124193/18014398509481984)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((748768221658519/4503599627370496), (17528231004499/9007199254740992)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((280549312874135/562949953421312), (17511232180499/2251799813685248)), (175/562949953421312), by norm_num⟩
  | 1 => ⟨((1120248061606681/1125899906842624), (6556018078191/281474976710656)), (529/562949953421312), by norm_num⟩
  | 0 => ⟨((34818935690629/35184372088832), (6534421556545/140737488355328)), (1073/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((34818935690629/35184372088832), (6534421556545/140737488355328)), (4093172313499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((550103148298487/562949953421312), (103464846666975/1125899906842624)), (139/35184372088832), by norm_num⟩
  | 2 => ⟨((33299721884811/35184372088832), (202207452168051/1125899906842624)), (1189/140737488355328), by norm_num⟩
  | 3 => ⟨((486098512267221/562949953421312), (191376213940439/562949953421312)), (10711/562949953421312), by norm_num⟩
  | 4 => ⟨((177339839139127/281474976710656), (330500757001249/562949953421312)), (51561/1125899906842624), by norm_num⟩
  | 5 => ⟨((58857536818263/1125899906842624), (1665823421091125/2251799813685248)), (125513/1125899906842624), by norm_num⟩
  | 6 => ⟨((-613089763777827/1125899906842624), (174165150460929/2251799813685248)), (397651/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-380229050267/17179869184)), (1/8589934592), by norm_num⟩, -4, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-8139419143/8589934592), (-301324393179/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-378528792245673/1125899906842624), (217363396199513/1125899906842624)), (603355/2251799813685248), by norm_num⟩
  | 1 => ⟨((101527437201/274877906944), (-116600633873/549755813888)), (41/137438953472), by norm_num⟩
  | 2 => ⟨((-55769645073/274877906944), (128098889239/1099511627776)), (91/549755813888), by norm_num⟩
  | 3 => ⟨((163384579765/2199023255552), (-46910337961/1099511627776)), (269/4398046511104), by norm_num⟩
  | 4 => ⟨((-179496307109/8796093022208), (103072547499/8796093022208)), (75/4398046511104), by norm_num⟩
  | 5 => ⟨((315514958017/70368744177664), (-181178827691/70368744177664)), (133/35184372088832), by norm_num⟩
  | 6 => ⟨((-231085740091/281474976710656), (132696857699/281474976710656)), (197/281474976710656), by norm_num⟩
  | 7 => ⟨((290141295771/2251799813685248), (-166608455469/2251799813685248)), (125/1125899906842624), by norm_num⟩
  | 8 => ⟨((-39844099123/2251799813685248), (91519048287/9007199254740992)), (277/18014398509481984), by norm_num⟩
  | 9 => ⟨((155638104631/72057594037927936), (-178744801947/144115188075855872)), (273/144115188075855872), by norm_num⟩
  | 10 => ⟨((-68394373733/288230376151711744), (39274247191/288230376151711744)), (121/576460752303423488), by norm_num⟩
  | 11 => ⟨((218585889335/9223372036854775808), (-125519041723/9223372036854775808)), (195/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-80047048051/36893488147419103232), (45965587233/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 13 => ⟨((54117335791/295147905179352825856), (-62151826449/590295810358705651712)), (197/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-271789577737/18889465931478580854784), (156070309257/18889465931478580854784)), (125/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((318497461369/302231454903657293676544), (-45722869239/75557863725914323419136)), (37/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-174952612485/2417851639229258349412352), (50231706019/1208925819614629174706176)), (41/604462909807314587353088), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349765/2535301200456458802993406410752), (213329983061/633825300114114700748351602688)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780499422049635/633825300114114700748351602688), (126467273647/19807040628566084398385987584)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945844051180321/19807040628566084398385987584), (2276206730635/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891583921056637/2475880078570760549798248448), (4836468842691/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773249163452455/154742504910672534362390528), (4835939401733/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96967636055587/604462909807314587353088), (2266565266905/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630237635848327/302231454903657293676544), (3965926422009/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945265372955041/37778931862957161709568), (6443574898259/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299591725169489/4722366482869645213696), (4831757281917/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624267139137779/590295810358705651712), (3321082191617/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826994126364239/73786976294838206464), (8300451689419/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((111487454515/562949953421312), (4667453807505/4611686018427387904)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597851603860667/1152921504606846976), (9331029587159/1152921504606846976)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((598977509233681/72057594037927936), (8160284871041/144115188075855872)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((748341131888275/18014398509481984), (12231687199223/36028797018963968)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495534887340355/9007199254740992), (7637147850949/4503599627370496)), (1389/9007199254740992), by norm_num⟩
  | 2 => ⟨((560104011041347/1125899906842624), (15251289668771/2251799813685248)), (697/1125899906842624), by norm_num⟩
  | 1 => ⟨((1117295062462197/1125899906842624), (22819293704265/1125899906842624)), (2105/1125899906842624), by norm_num⟩
  | 0 => ⟨((1108423491101173/1125899906842624), (22703637316925/562949953421312)), (2133/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108423491101173/1125899906842624), (22703637316925/562949953421312)), (8136751415061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((544693541397851/562949953421312), (44702454956395/562949953421312)), (8745/1125899906842624), by norm_num⟩
  | 2 => ⟨((523479472323281/562949953421312), (173011034827487/1125899906842624)), (18313/1125899906842624), by norm_num⟩
  | 3 => ⟨((118370892377247/140737488355328), (80440299059601/281474976710656)), (39687/1125899906842624), by norm_num⟩
  | 4 => ⟨((176129443246769/281474976710656), (541251096295673/1125899906842624)), (22361/281474976710656), by norm_num⟩
  | 5 => ⟨((45162216902517/281474976710656), (338681098267771/562949953421312)), (395867/2251799813685248), by norm_num⟩
  | 6 => ⟨((-378528792245673/1125899906842624), (217363396199513/1125899906842624)), (603355/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8139419143/8589934592), (-301324393179/8589934592)), (1/4294967296), by norm_num⟩, -6, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-2567700857/2147483648), (-380229050267/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((163556139094643/562949953421312), (-189677377723333/2251799813685248)), (104559/1125899906842624), by norm_num⟩
  | 1 => ⟨((-221422806009/549755813888), (64196454875/549755813888)), (73/549755813888), by norm_num⟩
  | 2 => ⟨((153478593697/549755813888), (-88995183397/1099511627776)), (103/1099511627776), by norm_num⟩
  | 3 => ⟨((-70922169665/549755813888), (20562253485/549755813888)), (97/2199023255552), by norm_num⟩
  | 4 => ⟨((98319003885/2199023255552), (-114021344233/8796093022208)), (137/8796093022208), by norm_num⟩
  | 5 => ⟨((-218078529083/17592186044416), (63226858623/17592186044416)), (77/17592186044416), by norm_num⟩
  | 6 => ⟨((100773678383/35184372088832), (-116868050107/140737488355328)), (145/140737488355328), by norm_num⟩
  | 7 => ⟨((-159659408105/281474976710656), (92579153633/562949953421312)), (117/562949953421312), by norm_num⟩
  | 8 => ⟨((55333734289/562949953421312), (-64170979319/2251799813685248)), (83/2251799813685248), by norm_num⟩
  | 9 => ⟨((-272742555821/18014398509481984), (4942214821/1125899906842624)), (13/2251799813685248), by norm_num⟩
  | 10 => ⟨((151240586869/72057594037927936), (-21924366521/36028797018963968)), (117/144115188075855872), by norm_num⟩
  | 11 => ⟨((-19060361159/72057594037927936), (44208910079/576460752303423488)), (15/144115188075855872), by norm_num⟩
  | 12 => ⟨((281848226087/9223372036854775808), (-81715417005/9223372036854775808)), (113/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-120222955851/36893488147419103232), (17427941817/18446744073709551616)), (49/36893488147419103232), by norm_num⟩
  | 14 => ⟨((95236803299/295147905179352825856), (-110446891277/1180591620717411303424)), (79/590295810358705651712), by norm_num⟩
  | 15 => ⟨((-281655985887/9444732965739290427392), (2551865043/295147905179352825856)), (119/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((390458105011/151115727451828646838272), (-56602177911/75557863725914323419136)), (167/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (-367584117833/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780124917843259/633825300114114700748351602688), (-435647716941/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891267342013603/39614081257132168796771975168), (-61256438215/4951760157141521099596496896)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472784387748961/618970019642690137449562112), (-260308097993/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((443200891747927/38685626227668133590597632), (-520544739643/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1551065251925511/9671406556917033397649408), (-487934784685/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157513910476315/75557863725914323419136), (-213433521605/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889940805273225/75557863725914323419136), (-346758338849/37778931862957161709568)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299150616355895/4722366482869645213696), (-520013056775/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623662801808769/590295810358705651712), (-714815780451/590295810358705651712)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913120991909185/36893488147419103232), (-893216573477/73786976294838206464)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825768800236905/9223372036854775808), (-1004451984579/9223372036854775808)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99813473573291/72057594037927936), (-1003931419039/1152921504606846976)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197229820345929/144115188075855872), (-219463678247/36028797018963968)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495607101804309/36028797018963968), (-164451550683/4503599627370496)), (1095/36028797018963968), by norm_num⟩
  | 3 => ⟨((373553253042349/2251799813685248), (-1642470603169/9007199254740992)), (1369/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237838388376471/4503599627370496), (-409851815103/562949953421312)), (1369/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115444198399753/1125899906842624), (-4902933120561/2251799813685248)), (4109/2251799813685248), by norm_num⟩
  | 0 => ⟨((2210099661913647/2251799813685248), (-9744879629115/2251799813685248)), (4115/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2210099661913647/2251799813685248), (-9744879629115/2251799813685248)), (15697483543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2169129566148267/2251799813685248), (-9564418223505/1125899906842624)), (16227/2251799813685248), by norm_num⟩
  | 2 => ⟨((2089331890766545/2251799813685248), (-18426560145823/1125899906842624)), (31539/2251799813685248), by norm_num⟩
  | 3 => ⟨((1937982928489957/2251799813685248), (-34194158393493/1125899906842624)), (7445/281474976710656), by norm_num⟩
  | 4 => ⟨((1665823421091141/2251799813685248), (-58857536818265/1125899906842624)), (53069/1125899906842624), by norm_num⟩
  | 5 => ⟨((1226179527555677/2251799813685248), (-21770643807617/281474976710656)), (84067/1125899906842624), by norm_num⟩
  | 6 => ⟨((163556139094643/562949953421312), (-189677377723333/2251799813685248)), (104559/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-380229050267/8589934592)), (1/4294967296), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-5962016759/4294967296), (-220716128577/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((485584322573759/4503599627370496), (-1013502509695761/4503599627370496)), (590261/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2981253885/17179869184), (199117353937/549755813888)), (59/274877906944), by norm_num⟩
  | 2 => ⟨((153540576931/1099511627776), (-160233509225/549755813888)), (3/17179869184), by norm_num⟩
  | 3 => ⟨((-41185670935/549755813888), (343847846119/2199023255552)), (13/137438953472), by norm_num⟩
  | 4 => ⟨((16571445063/549755813888), (-138350439913/2199023255552)), (169/4398046511104), by norm_num⟩
  | 5 => ⟨((-42673139117/4398046511104), (356266309117/17592186044416)), (55/4398046511104), by norm_num⟩
  | 6 => ⟨((91573023917/35184372088832), (-191129501605/35184372088832)), (15/4398046511104), by norm_num⟩
  | 7 => ⟨((-84217769399/140737488355328), (351555504077/281474976710656)), (223/281474976710656), by norm_num⟩
  | 8 => ⟨((135543270971/1125899906842624), (-282903378293/1125899906842624)), (181/1125899906842624), by norm_num⟩
  | 9 => ⟨((-96954879589/4503599627370496), (50590602509/1125899906842624)), (131/4503599627370496), by norm_num⟩
  | 10 => ⟨((124834287205/36028797018963968), (-260551787811/36028797018963968)), (171/36028797018963968), by norm_num⟩
  | 11 => ⟨((-73059285309/144115188075855872), (152487972893/144115188075855872)), (101/144115188075855872), by norm_num⟩
  | 12 => ⟨((156779178175/2305843009213693952), (-20451660397/144115188075855872)), (219/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-155277755837/18446744073709551616), (324092825749/18446744073709551616)), (219/18446744073709551616), by norm_num⟩
  | 14 => ⟨((71402830629/73786976294838206464), (-18628831461/9223372036854775808)), (203/147573952589676412928), by norm_num⟩
  | 15 => ⟨((-122579650847/1180591620717411303424), (63961488251/295147905179352825856)), (11/73786976294838206464), by norm_num⟩
  | 16 => ⟨((98642168683/9444732965739290427392), (-102942044127/4722366482869645213696)), (143/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754455/5070602400912917605986812821504), (-1464130055463/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779826335583667/633825300114114700748351602688), (-216835609359/79228162514264337593543950336)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945465693688441/19807040628566084398385987584), (-975639347031/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890780534994747/2475880078570760549798248448), (-2072939779655/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772446478817151/154742504910672534362390528), (-2072609271753/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775365202561729/4835703278458516698824704), (-1942720086029/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259818216271951/604462909807314587353088), (-1699529034729/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944732213516265/37778931862957161709568), (-2761076619991/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298793207230797/4722366482869645213696), (-258778975099/590295810358705651712)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623171160619765/590295810358705651712), (-1422816766699/295147905179352825856)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912813563614219/36893488147419103232), (-222227474093/4611686018427387904)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825076667639161/9223372036854775808), (-3998167071927/9223372036854775808)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199540365222731/144115188075855872), (-1997879430033/576460752303423488)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196623159938113/144115188075855872), (-436697662167/18014398509481984)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494695940310793/36028797018963968), (-1308740091755/9007199254740992)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1493072017999831/9007199254740992), (-6534238812641/9007199254740992)), (43/281474976710656), by norm_num⟩
  | 2 => ⟨((2235550300044373/4503599627370496), (-6520063568357/2251799813685248)), (689/1125899906842624), by norm_num⟩
  | 1 => ⟨((2227441108311177/2251799813685248), (-19489434974727/2251799813685248)), (4145/2251799813685248), by norm_num⟩
  | 0 => ⟨((1101572511624435/1125899906842624), (-19348284653537/1125899906842624)), (4169/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101572511624435/1125899906842624), (-19348284653537/1125899906842624)), (15903477195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2154876530098327/2251799813685248), (-75720899848695/2251799813685248)), (16603/2251799813685248), by norm_num⟩
  | 2 => ⟨((1029789410477091/1125899906842624), (-36230838312141/562949953421312)), (16447/1125899906842624), by norm_num⟩
  | 3 => ⟨((1874439333263127/2251799813685248), (-265104444185841/2251799813685248)), (64407/2251799813685248), by norm_num⟩
  | 4 => ⟨((1529106817946527/2251799813685248), (-27584723261409/140737488355328)), (122393/2251799813685248), by norm_num⟩
  | 5 => ⟨((951848786276509/2251799813685248), (-599413687186095/2251799813685248)), (53551/562949953421312), by norm_num⟩
  | 6 => ⟨((485584322573759/4503599627370496), (-1013502509695761/4503599627370496)), (590261/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5962016759/4294967296), (-220716128577/4294967296)), (1/4294967296), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-13274820857/8589934592), (-491438918313/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((94654756703535/562949953421312), (-295277642816577/2251799813685248)), (196063/2251799813685248), by norm_num⟩
  | 1 => ⟨((-41405897615/137438953472), (129166629045/549755813888)), (87/549755813888), by norm_num⟩
  | 2 => ⟨((296757636535/1099511627776), (-57858882675/274877906944)), (79/549755813888), by norm_num⟩
  | 3 => ⟨((-177239435109/1099511627776), (2159775019/17179869184)), (3/34359738368), by norm_num⟩
  | 4 => ⟨((158785218089/2199023255552), (-61916757467/1099511627776)), (11/274877906944), by norm_num⟩
  | 5 => ⟨((-56900983617/2199023255552), (177503898393/8796093022208)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((271874336545/35184372088832), (-212029527181/35184372088832)), (155/35184372088832), by norm_num⟩
  | 7 => ⟨((-69590488135/35184372088832), (108544546595/70368744177664)), (5/4398046511104), by norm_num⟩
  | 8 => ⟨((31172354021/70368744177664), (-194485719195/562949953421312)), (145/562949953421312), by norm_num⟩
  | 9 => ⟨((-99294863103/1125899906842624), (77438139777/1125899906842624)), (59/1125899906842624), by norm_num⟩
  | 10 => ⟨((284660017937/18014398509481984), (-27750104045/2251799813685248)), (171/18014398509481984), by norm_num⟩
  | 11 => ⟨((-46367480241/18014398509481984), (144644397657/72057594037927936)), (113/72057594037927936), by norm_num⟩
  | 12 => ⟨((110772495715/288230376151711744), (-172778646115/576460752303423488)), (137/576460752303423488), by norm_num⟩
  | 13 => ⟨((-122140103463/2305843009213693952), (95254700079/2305843009213693952)), (153/4611686018427387904), by norm_num⟩
  | 14 => ⟨((250109356517/36893488147419103232), (-195055440977/36893488147419103232)), (159/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-59751441051/73786976294838206464), (93197982239/147573952589676412928)), (77/147573952589676412928), by norm_num⟩
  | 16 => ⟨((214120420607/2361183241434822606848), (-83494183595/1180591620717411303424)), (35/590295810358705651712), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775111/10141204801825835211973625643008), (-862787521959/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779584725435035/633825300114114700748351602688), (-1021955992089/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945329836464507/19807040628566084398385987584), (-1149543263489/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945245979578187/1237940039285380274899124224), (-610598559907/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772158038785253/154742504910672534362390528), (-1220980499795/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550460136839295/9671406556917033397649408), (-1144439110893/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259581875714335/604462909807314587353088), (-500577085929/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889080643868347/75557863725914323419136), (-1626444307333/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((649252803101585/2361183241434822606848), (-609728016703/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811388046525233/295147905179352825856), (-838069664757/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456283467037859/18446744073709551616), (-523563871901/18446744073709551616)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456130635428185/2305843009213693952), (-294346862083/1152921504606846976)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595769783097053/1152921504606846976), (-2353197712907/1152921504606846976)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598070136480773/72057594037927936), (-2057275006643/144115188075855872)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((373493456352139/9007199254740992), (-192648117003/2251799813685248)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((373043311113377/2251799813685248), (-3846770246041/9007199254740992)), (343/2251799813685248), by norm_num⟩
  | 2 => ⟨((279220541827869/562949953421312), (-3837497132141/2251799813685248)), (1373/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224791014527205/2251799813685248), (-11466230859059/2251799813685248)), (2063/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098979827751397/1125899906842624), (-11374024250533/1125899906842624)), (8279/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098979827751397/1125899906842624), (-11374024250533/1125899906842624)), (31581887252043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((268147125254545/281474976710656), (-44408292906763/2251799813685248)), (8165/1125899906842624), by norm_num⟩
  | 2 => ⟨((510681749508947/562949953421312), (-84611116906859/2251799813685248)), (31759/2251799813685248), by norm_num⟩
  | 3 => ⟨((57808959666451/70368744177664), (-153510460200937/2251799813685248)), (7501/281474976710656), by norm_num⟩
  | 4 => ⟨((754622003984789/1125899906842624), (-126111103812353/1125899906842624)), (53389/1125899906842624), by norm_num⟩
  | 5 => ⟨((983302965084307/2251799813685248), (-338098309823961/2251799813685248)), (167055/2251799813685248), by norm_num⟩
  | 6 => ⟨((94654756703535/562949953421312), (-295277642816577/2251799813685248)), (196063/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13274820857/8589934592), (-491438918313/8589934592)), (1/4294967296), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-7208447639/4294967296), (-33357434243/536870912)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((643689804684985/4503599627370496), (540842355184257/4503599627370496)), (22009/281474976710656), by norm_num⟩
  | 1 => ⟨((-152900698703/549755813888), (-128470535643/549755813888)), (43/274877906944), by norm_num⟩
  | 2 => ⟨((74382755351/274877906944), (124996059581/549755813888)), (169/1099511627776), by norm_num⟩
  | 3 => ⟨((-6030923273/34359738368), (-162154067287/1099511627776)), (111/1099511627776), by norm_num⟩
  | 4 => ⟨((93885078441/1099511627776), (78884311311/1099511627776)), (55/1099511627776), by norm_num⟩
  | 5 => ⟨((-292307083173/8796093022208), (-122801425585/4398046511104)), (173/8796093022208), by norm_num⟩
  | 6 => ⟨((47400276649/4398046511104), (159307026909/17592186044416)), (57/8796093022208), by norm_num⟩
  | 7 => ⟨((-105413347885/35184372088832), (-177141234559/70368744177664)), (129/70368744177664), by norm_num⟩
  | 8 => ⟨((205124903495/281474976710656), (5385951971/8796093022208)), (127/281474976710656), by norm_num⟩
  | 9 => ⟨((-44350514615/281474976710656), (-149057117905/1125899906842624)), (111/1125899906842624), by norm_num⟩
  | 10 => ⟨((17260423301/562949953421312), (7251293963/281474976710656)), (175/9007199254740992), by norm_num⟩
  | 11 => ⟨((-24427078457/4503599627370496), (-164193355827/36028797018963968)), (125/36028797018963968), by norm_num⟩
  | 12 => ⟨((126754399683/144115188075855872), (213003678341/288230376151711744)), (41/72057594037927936), by norm_num⟩
  | 13 => ⟨((-151786260173/1152921504606846976), (-127534159837/1152921504606846976)), (25/288230376151711744), by norm_num⟩
  | 14 => ⟨((84389264045/4611686018427387904), (70905718851/4611686018427387904)), (113/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-175161520401/73786976294838206464), (-147174568467/73786976294838206464)), (119/73786976294838206464), by norm_num⟩
  | 16 => ⟨((21303036267/73786976294838206464), (143194243231/590295810358705651712)), (117/590295810358705651712), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532093557/10141204801825835211973625643008), (227562995011/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889689773006897/316912650057057350374175801344), (269485099965/158456325028528675187087900672)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890428875453259/39614081257132168796771975168), (606251686293/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472561693131847/618970019642690137449562112), (644032114119/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771912892300103/154742504910672534362390528), (321954028477/38685626227668133590597632)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387557588663811/2417851639229258349412352), (1207064049107/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259380858941141/604462909807314587353088), (263979389265/151115727451828646838272)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888754071541035/75557863725914323419136), (428843036653/18889465931478580854784)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298260746878831/4722366482869645213696), (1286097114217/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1622439525069787/590295810358705651712), (883840912321/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824713328505769/73786976294838206464), (2208550219401/73786976294838206464)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912024834362799/4611686018427387904), (155198326501/576460752303423488)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797648601309037/576460752303423488), (2481367224711/1152921504606846976)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597863546964521/72057594037927936), (1084583122105/72057594037927936)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493354714170409/36028797018963968), (1624846693757/18014398509481984)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491400504658829/9007199254740992), (4055028157933/9007199254740992)), (1373/9007199254740992), by norm_num⟩
  | 2 => ⟨((558055574657949/1125899906842624), (4044414042139/2251799813685248)), (2747/4503599627370496), by norm_num⟩
  | 1 => ⟨((138905409686225/140737488355328), (6040151287033/1125899906842624)), (4127/2251799813685248), by norm_num⟩
  | 0 => ⟨((1096692513438865/1125899906842624), (23949631375663/2251799813685248)), (2071/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096692513438865/1125899906842624), (23949631375663/2251799813685248)), (7900240184593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1068115438604609/1125899906842624), (46656689941411/2251799813685248)), (4079/562949953421312), by norm_num⟩
  | 2 => ⟨((2025626561608441/2251799813685248), (88524264968387/2251799813685248)), (15817/1125899906842624), by norm_num⟩
  | 3 => ⟨((1818690274648845/2251799813685248), (159265580694193/2251799813685248)), (59401/2251799813685248), by norm_num⟩
  | 4 => ⟨((1457620153425957/2251799813685248), (257265109388909/2251799813685248)), (104355/2251799813685248), by norm_num⟩
  | 5 => ⟨((914144837677987/2251799813685248), (166531148079677/1125899906842624)), (79473/1125899906842624), by norm_num⟩
  | 6 => ⟨((643689804684985/4503599627370496), (540842355184257/4503599627370496)), (22009/281474976710656), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7208447639/4294967296), (-33357434243/536870912)), (1/4294967296), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-7703102571/4294967296), (-285171787701/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-1366305412568647/9007199254740992), (615546077817501/9007199254740992)), (1037539/4503599627370496), by norm_num⟩
  | 1 => ⟨((173410170503/549755813888), (-78124516909/549755813888)), (265/549755813888), by norm_num⟩
  | 2 => ⟨((-180298156147/549755813888), (40613841471/274877906944)), (277/549755813888), by norm_num⟩
  | 3 => ⟨((249946317187/1099511627776), (-112605478829/1099511627776)), (193/549755813888), by norm_num⟩
  | 4 => ⟨((-259874377575/2199023255552), (117078255249/2199023255552)), (101/549755813888), by norm_num⟩
  | 5 => ⟨((216157430539/4398046511104), (-97382955037/4398046511104)), (169/2199023255552), by norm_num⟩
  | 6 => ⟨((-299657827071/17592186044416), (135001441437/17592186044416)), (471/17592186044416), by norm_num⟩
  | 7 => ⟨((356069105087/70368744177664), (-80207887289/35184372088832)), (563/70368744177664), by norm_num⟩
  | 8 => ⟨((-185106222207/140737488355328), (166787612799/281474976710656)), (147/70368744177664), by norm_num⟩
  | 9 => ⟨((342148949405/1125899906842624), (-9634030297/70368744177664)), (273/562949953421312), by norm_num⟩
  | 10 => ⟨((-142295747767/2251799813685248), (64106889003/2251799813685248)), (457/4503599627370496), by norm_num⟩
  | 11 => ⟨((26899608101/2251799813685248), (-96950202255/18014398509481984)), (87/4503599627370496), by norm_num⟩
  | 12 => ⟨((-149163100107/72057594037927936), (16800189837/18014398509481984)), (485/144115188075855872), by norm_num⟩
  | 13 => ⟨((190877505753/576460752303423488), (-85993877305/576460752303423488)), (39/72057594037927936), by norm_num⟩
  | 14 => ⟨((-226810637049/4611686018427387904), (102182423313/4611686018427387904)), (373/4611686018427387904), by norm_num⟩
  | 15 => ⟨((251541045747/36893488147419103232), (-28330983449/9223372036854775808)), (13/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-130766224991/147573952589676412928), (117825247801/295147905179352825856)), (435/295147905179352825856), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233537/10141204801825835211973625643008), (3540899014965/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1779193124025601/633825300114114700748351602688), (2096206966613/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890218678893243/39614081257132168796771975168), (1178924520447/9903520314283042199192993792)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890022830441145/2475880078570760549798248448), (2504754840895/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221461033297813/19342813113834066795298816), (5008475177097/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775009520851215/4835703278458516698824704), (4694346390781/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259195234419841/604462909807314587353088), (2053227043299/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888451072022755/75557863725914323419136), (6670927431183/75557863725914323419136)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298032308520541/4722366482869645213696), (5001392847137/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622123492518329/590295810358705651712), (6873986065175/590295810358705651712)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912157698178777/36893488147419103232), (8588089512033/73786976294838206464)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823598024588199/9223372036854775808), (1206945147015/1152921504606846976)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594840603315171/1152921504606846976), (1206001649199/144115188075855872)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597661002931645/72057594037927936), (8433522030095/144115188075855872)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((373183995477217/9007199254740992), (12633308957329/36028797018963968)), (2217/36028797018963968), by norm_num⟩
  | 3 => ⟨((186325965643957/1125899906842624), (15761942730185/9007199254740992)), (2779/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115289445574683/2251799813685248), (15717425080511/2251799813685248)), (1395/1125899906842624), by norm_num⟩
  | 1 => ⟨((554969418819651/562949953421312), (23464923209659/1125899906842624)), (2107/562949953421312), by norm_num⟩
  | 0 => ⟨((546899324305199/562949953421312), (23242736666171/562949953421312)), (8545/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546899324305199/562949953421312), (23242736666171/562949953421312)), (32596592429732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1060693385986689/1125899906842624), (45160096028001/562949953421312)), (17309/1125899906842624), by norm_num⟩
  | 2 => ⟨((496008888176857/562949953421312), (170178591813739/1125899906842624)), (35391/1125899906842624), by norm_num⟩
  | 3 => ⟨((848333417282685/1125899906842624), (299884895998431/1125899906842624)), (73065/1125899906842624), by norm_num⟩
  | 4 => ⟨((559320266573707/1125899906842624), (14122168912823/35184372088832)), (149027/1125899906842624), by norm_num⟩
  | 5 => ⟨((385885279579139/4503599627370496), (224497832758717/562949953421312)), (1070793/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1366305412568647/9007199254740992), (615546077817501/9007199254740992)), (1037539/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7703102571/4294967296), (-285171787701/4294967296)), (1/2147483648), by norm_num⟩, -11, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile066Terms0
