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
namespace Reinmann.XiBand97.Tile066Terms1
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-8139419143/4294967296), (-301324393179/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((682385352146699/9007199254740992), (-584622511054665/4503599627370496)), (172369/1125899906842624), by norm_num⟩
  | 1 => ⟨((-183026595087/1099511627776), (313610095155/1099511627776)), (373/1099511627776), by norm_num⟩
  | 2 => ⟨((50268816629/274877906944), (-86133976097/274877906944)), (413/1099511627776), by norm_num⟩
  | 3 => ⟨((-73634586247/549755813888), (252340918965/1099511627776)), (305/1099511627776), by norm_num⟩
  | 4 => ⟨((40447930661/549755813888), (-277224834509/2199023255552)), (337/2199023255552), by norm_num⟩
  | 5 => ⟨((-142197099761/4398046511104), (60912521983/1099511627776)), (299/4398046511104), by norm_num⟩
  | 6 => ⟨((104146320807/8796093022208), (-178451320491/8796093022208)), (221/8796093022208), by norm_num⟩
  | 7 => ⟨((-65380815919/17592186044416), (224055786995/35184372088832)), (35/4398046511104), by norm_num⟩
  | 8 => ⟨((143656335623/140737488355328), (-61537610235/35184372088832)), (155/70368744177664), by norm_num⟩
  | 9 => ⟨((-35071692369/140737488355328), (120188399679/281474976710656)), (305/562949953421312), by norm_num⟩
  | 10 => ⟨((123296615107/2251799813685248), (-52816181137/562949953421312)), (135/1125899906842624), by norm_num⟩
  | 11 => ⟨((-49256427821/4503599627370496), (168798561855/9007199254740992)), (217/9007199254740992), by norm_num⟩
  | 12 => ⟨((144303245067/72057594037927936), (-247258899151/72057594037927936)), (5/1125899906842624), by norm_num⟩
  | 13 => ⟨((-97558965123/288230376151711744), (334328203187/576460752303423488)), (109/144115188075855872), by norm_num⟩
  | 14 => ⟨((122490831947/2305843009213693952), (-209884041411/2305843009213693952)), (69/576460752303423488), by norm_num⟩
  | 15 => ⟨((-35885315527/4611686018427387904), (245953266229/18446744073709551616)), (163/9223372036854775808), by norm_num⟩
  | 16 => ⟨((157696194483/147573952589676412928), (-270207280717/147573952589676412928)), (361/147573952589676412928), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581507179692737/10141204801825835211973625643008), (-678995462967/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779044476486653/633825300114114700748351602688), (-1607587785053/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945025969135837/19807040628566084398385987584), (-904117325873/19807040628566084398385987584)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944923146818439/1237940039285380274899124224), (-1920877805665/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((110719527025571/9671406556917033397649408), (-960229987717/77371252455336267181195264)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774927471856553/4835703278458516698824704), (-1799987398153/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259052394593391/604462909807314587353088), (-393636318711/151115727451828646838272)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118013772184087/4722366482869645213696), (-639451103403/18889465931478580854784)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((648930246349931/2361183241434822606848), (-59925808941/147573952589676412928)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810944614858577/295147905179352825856), (-1317777023893/295147905179352825856)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824025540675799/73786976294838206464), (-51447986693/1152921504606846976)), (743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823276019524345/9223372036854775808), (-3701820824455/9223372036854775808)), (209/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594523693905047/1152921504606846976), (-1849390130581/576460752303423488)), (209/144115188075855872), by norm_num⟩
  | 5 => ⟨((149381304042503/18014398509481984), (-808253782349/36028797018963968)), (183/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492340040067771/36028797018963968), (-4842695075969/36028797018963968)), (2197/36028797018963968), by norm_num⟩
  | 3 => ⟨((745066360869531/4503599627370496), (-6041437551075/9007199254740992)), (1375/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114844211372743/2251799813685248), (-12047149284739/4503599627370496)), (5507/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218690003749145/2251799813685248), (-17981647216975/2251799813685248)), (8283/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092904599833337/1125899906842624), (-4451051433221/281474976710656)), (16655/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092904599833337/1125899906842624), (-4451051433221/281474976710656)), (63533791548918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2121189401185375/2251799813685248), (-4320610167829/140737488355328)), (16431/1125899906842624), by norm_num⟩
  | 2 => ⟨((1996032473355779/2251799813685248), (-130240103070671/2251799813685248)), (31965/1125899906842624), by norm_num⟩
  | 3 => ⟨((1761783230521865/2251799813685248), (-115446974230277/1125899906842624)), (120733/2251799813685248), by norm_num⟩
  | 4 => ⟨((169340549133887/281474976710656), (-45162216902515/281474976710656)), (213681/2251799813685248), by norm_num⟩
  | 5 => ⟨((378528792245683/1125899906842624), (-217363396199505/1125899906842624)), (20355/140737488355328), by norm_num⟩
  | 6 => ⟨((682385352146699/9007199254740992), (-584622511054665/4503599627370496)), (172369/1125899906842624), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8139419143/4294967296), (-301324393179/4294967296)), (1/2147483648), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-315773391143/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-93013760777971/2251799813685248), (294721557169057/2251799813685248)), (208877/1125899906842624), by norm_num⟩
  | 1 => ⟨((26144055055/274877906944), (-165679068389/549755813888)), (59/137438953472), by norm_num⟩
  | 2 => ⟨((-3762431965/34359738368), (381490153093/1099511627776)), (273/549755813888), by norm_num⟩
  | 3 => ⟨((721943313/8589934592), (-73201128303/274877906944)), (421/1099511627776), by norm_num⟩
  | 4 => ⟨((-3324671821/68719476736), (337103653641/2199023255552)), (487/2199023255552), by norm_num⟩
  | 5 => ⟨((97988349109/4398046511104), (-310483939067/4398046511104)), (451/4398046511104), by norm_num⟩
  | 6 => ⟨((-75208837315/8796093022208), (238305229903/8796093022208)), (87/2199023255552), by norm_num⟩
  | 7 => ⟨((12369624833/4398046511104), (-19597073927/2199023255552)), (115/8796093022208), by norm_num⟩
  | 8 => ⟨((-113928454985/140737488355328), (360991442325/140737488355328)), (533/140737488355328), by norm_num⟩
  | 9 => ⟨((58295547137/281474976710656), (-369428228353/562949953421312)), (137/140737488355328), by norm_num⟩
  | 10 => ⟨((-26846091565/562949953421312), (170127986307/1125899906842624)), (507/2251799813685248), by norm_num⟩
  | 11 => ⟨((89913323989/9007199254740992), (-142448787335/4503599627370496)), (427/9007199254740992), by norm_num⟩
  | 12 => ⟨((-69011026493/36028797018963968), (13666685593/2251799813685248)), (165/18014398509481984), by norm_num⟩
  | 13 => ⟨((97786929757/288230376151711744), (-154922862853/144115188075855872)), (235/144115188075855872), by norm_num⟩
  | 14 => ⟨((-128664415285/2305843009213693952), (407683513793/2305843009213693952)), (621/2305843009213693952), by norm_num⟩
  | 15 => ⟨((79002870569/9223372036854775808), (-250326928405/9223372036854775808)), (383/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-45477708019/36893488147419103232), (72049881715/18446744073709551616)), (443/73786976294838206464), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (2444353077791/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((444725315159865/158456325028528675187087900672), (1446593980317/316912650057057350374175801344)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889890672045507/39614081257132168796771975168), (1627131623687/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889674753813059/2475880078570760549798248448), (3456953422789/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771340674005615/154742504910672534362390528), (864041160993/38685626227668133590597632)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549693688126225/9671406556917033397649408), (3239316455879/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629455532024161/302231454903657293676544), (88548881345/18889465931478580854784)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943995129180441/37778931862957161709568), (4602971579413/75557863725914323419136)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297687540494587/4722366482869645213696), (3450855144519/4722366482869645213696)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810825402008919/295147905179352825856), (1185673656443/147573952589676412928)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823726585157375/73786976294838206464), (370313930829/4611686018427387904)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911469213449073/4611686018427387904), (6661053132797/9223372036854775808)), (419/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594184519689599/1152921504606846976), (3327654768111/576460752303423488)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((298687969931951/36028797018963968), (2908469507529/72057594037927936)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((93243041942051/2251799813685248), (8712506654655/36028797018963968)), (2207/36028797018963968), by norm_num⟩
  | 3 => ⟨((744781169215047/4503599627370496), (5434040785829/4503599627370496)), (691/2251799813685248), by norm_num⟩
  | 2 => ⟨((2228529232005005/4503599627370496), (21668613961731/4503599627370496)), (5543/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216905478680695/2251799813685248), (8083604763671/562949953421312)), (4177/1125899906842624), by norm_num⟩
  | 0 => ⟨((545514778634887/562949953421312), (63997055834947/2251799813685248)), (8435/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545514778634887/562949953421312), (63997055834947/2251799813685248)), (32176975730514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((264082442368839/281474976710656), (124029994264723/2251799813685248)), (33655/2251799813685248), by norm_num⟩
  | 2 => ⟨((1975285218965673/2251799813685248), (232732189519575/2251799813685248)), (16715/562949953421312), by norm_num⟩
  | 3 => ⟨((1708672059053425/2251799813685248), (408306680852929/2251799813685248)), (131121/2251799813685248), by norm_num⟩
  | 4 => ⟨((1222509142700161/2251799813685248), (154912131366701/562949953421312)), (123271/1125899906842624), by norm_num⟩
  | 5 => ⟨((123297406603695/562949953421312), (168204558646821/562949953421312)), (50423/281474976710656), by norm_num⟩
  | 6 => ⟨((-93013760777971/2251799813685248), (294721557169057/2251799813685248)), (208877/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-315773391143/4294967296)), (1/2147483648), by norm_num⟩, -12, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-2220696383/1073741824), (-328844099705/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((447639315742233/9007199254740992), (-261740912793295/2251799813685248)), (308119/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4094666287/34359738368), (153229320675/549755813888)), (363/1099511627776), by norm_num⟩
  | 2 => ⟨((157097294933/1099511627776), (-367427863701/1099511627776)), (219/549755813888), by norm_num⟩
  | 3 => ⟨((-15695952537/137438953472), (36710564061/137438953472)), (353/1099511627776), by norm_num⟩
  | 4 => ⟨((75274500781/1099511627776), (-352112352095/2199023255552)), (213/1099511627776), by norm_num⟩
  | 5 => ⟨((-36100073917/1099511627776), (337731417833/4398046511104)), (411/4398046511104), by norm_num⟩
  | 6 => ⟨((115418928791/8796093022208), (-269948190099/8796093022208)), (165/4398046511104), by norm_num⟩
  | 7 => ⟨((-158150002137/35184372088832), (23118124605/2199023255552)), (455/35184372088832), by norm_num⟩
  | 8 => ⟨((94806785629/70368744177664), (-221739366825/70368744177664)), (275/70368744177664), by norm_num⟩
  | 9 => ⟨((-25259638121/70368744177664), (59078642167/70368744177664)), (295/281474976710656), by norm_num⟩
  | 10 => ⟨((96911946949/1125899906842624), (-226663034841/1125899906842624)), (285/1125899906842624), by norm_num⟩
  | 11 => ⟨((-84503527079/4503599627370496), (197641534459/4503599627370496)), (251/4503599627370496), by norm_num⟩
  | 12 => ⟨((67543536039/18014398509481984), (-315949134125/36028797018963968)), (101/9007199254740992), by norm_num⟩
  | 13 => ⟨((-99669123555/144115188075855872), (116555836179/72057594037927936)), (75/36028797018963968), by norm_num⟩
  | 14 => ⟨((4267787861/36028797018963968), (-39926955513/144115188075855872)), (207/576460752303423488), by norm_num⟩
  | 15 => ⟨((-87327644477/4611686018427387904), (204246736815/4611686018427387904)), (267/4611686018427387904), by norm_num⟩
  | 16 => ⟨((52350636469/18446744073709551616), (-244881142347/36893488147419103232)), (161/18446744073709551616), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (-189979348949/1267650600228229401496703205376)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222347159154655/79228162514264337593543950336), (-1798664559115/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472437841903007/9903520314283042199192993792), (-2023130551653/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472381744046819/618970019642690137449562112), (-1074561303677/1237940039285380274899124224)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771193158703769/154742504910672534362390528), (-2148612465057/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774777835547507/4835703278458516698824704), (-2013782313207/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258790577536013/604462909807314587353088), (-440379455963/151115727451828646838272)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58993593418421/2361183241434822606848), (-2861451142487/75557863725914323419136)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((648770772402887/2361183241434822606848), (-2145200317233/4722366482869645213696)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((405362700079257/147573952589676412928), (-1474104029329/295147905179352825856)), (297/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227934711234489/9223372036854775808), (-3683097708469/73786976294838206464)), (743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911329971543303/4611686018427387904), (-517564202707/1152921504606846976)), (209/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199238492144111/144115188075855872), (-4136802421289/1152921504606846976)), (1673/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597256002445017/72057594037927936), (-3615531037221/144115188075855872)), (1465/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491533118462045/36028797018963968), (-5414964431511/36028797018963968)), (2199/36028797018963968), by norm_num⟩
  | 3 => ⟨((372281332329389/2251799813685248), (-3377073441831/4503599627370496)), (2751/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113838708996869/2251799813685248), (-13464707923687/4503599627370496)), (5513/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215682951414381/2251799813685248), (-20088412152345/2251799813685248)), (4147/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089916470358585/1125899906842624), (-19872055090547/1125899906842624)), (1043/140737488355328), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089916470358585/1125899906842624), (-19872055090547/1125899906842624)), (3978729784917787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((527366156870721/562949953421312), (-76947799751751/2251799813685248)), (32899/2251799813685248), by norm_num⟩
  | 2 => ⟨((1973496943958815/2251799813685248), (-18020991558893/281474976710656)), (63889/2251799813685248), by norm_num⟩
  | 3 => ⟨((430089940890641/562949953421312), (-126350030060191/1125899906842624)), (15021/281474976710656), by norm_num⟩
  | 4 => ⟨((642992413912901/1125899906842624), (-96530564803953/562949953421312)), (210587/2251799813685248), by norm_num⟩
  | 5 => ⟨((41762886991321/140737488355328), (-882045311522993/4503599627370496)), (625499/4503599627370496), by norm_num⟩
  | 6 => ⟨((447639315742233/9007199254740992), (-261740912793295/2251799813685248)), (308119/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-328844099705/4294967296)), (1/2147483648), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-9205111285/4294967296), (-340776721723/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-366664764689711/4503599627370496), (760290746563913/9007199254740992)), (1502905/9007199254740992), by norm_num⟩
  | 1 => ⟨((222443289067/1099511627776), (-230621524891/1099511627776)), (229/549755813888), by norm_num⟩
  | 2 => ⟨((-138187702051/549755813888), (35817060049/137438953472)), (143/274877906944), by norm_num⟩
  | 3 => ⟨((114461179915/549755813888), (-59334700461/274877906944)), (119/274877906944), by norm_num⟩
  | 4 => ⟨((-35553168389/274877906944), (147441191739/1099511627776)), (149/549755813888), by norm_num⟩
  | 5 => ⟨((141354087281/2199023255552), (-73275519561/1099511627776)), (149/1099511627776), by norm_num⟩
  | 6 => ⟨((-234167807639/8796093022208), (121388550549/4398046511104)), (31/549755813888), by norm_num⟩
  | 7 => ⟨((166252897819/17592186044416), (-172365266553/17592186044416)), (177/8796093022208), by norm_num⟩
  | 8 => ⟨((-51640366417/17592186044416), (214155798525/70368744177664)), (221/35184372088832), by norm_num⟩
  | 9 => ⟨((14257943323/17592186044416), (-59128574205/70368744177664)), (245/140737488355328), by norm_num⟩
  | 10 => ⟨((-56687453081/281474976710656), (235086379575/1125899906842624)), (489/1125899906842624), by norm_num⟩
  | 11 => ⟨((100044765/2199023255552), (-212424621047/4503599627370496)), (111/1125899906842624), by norm_num⟩
  | 12 => ⟨((-84856115823/9007199254740992), (175951784473/18014398509481984)), (185/9007199254740992), by norm_num⟩
  | 13 => ⟨((129759708605/72057594037927936), (-269060774941/144115188075855872)), (569/144115188075855872), by norm_num⟩
  | 14 => ⟨((-92125932225/288230376151711744), (47756493489/144115188075855872)), (203/288230376151711744), by norm_num⟩
  | 15 => ⟨((244185964377/4611686018427387904), (-31645447531/576460752303423488)), (135/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-75847415833/9223372036854775808), (78635983005/9223372036854775808)), (337/18446744073709551616), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075657/5070602400912917605986812821504), (3045695611143/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778656365596175/633825300114114700748351602688), (1802007128245/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236201884645189/4951760157141521099596496896), (4053743355575/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472345453423247/618970019642690137449562112), (538269889897/309485009821345068724781056)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885523799214353/77371252455336267181195264), (2152549095977/77371252455336267181195264)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193677348248601/1208925819614629174706176), (4034902544565/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629335190525089/302231454903657293676544), (3529412968701/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887598879518227/75557863725914323419136), (5733183940123/75557863725914323419136)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297393771344703/4722366482869645213696), (134313761711/147573952589676412928)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621246490153679/590295810358705651712), (2953402102065/295147905179352825856)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823220621988453/73786976294838206464), (3689502525419/36893488147419103232)), (1491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822368435192745/9223372036854775808), (8295195765777/9223372036854775808)), (1679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398403387925037/288230376151711744), (2071867229533/288230376151711744)), (1681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194251188044665/144115188075855872), (7242848511089/144115188075855872)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491135453217129/36028797018963968), (10846913965593/36028797018963968)), (2213/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488617020863153/9007199254740992), (6764148916131/4503599627370496)), (693/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113313646130713/2251799813685248), (3370711871127/562949953421312)), (1391/1125899906842624), by norm_num⟩
  | 1 => ⟨((553506147656587/562949953421312), (20110878576411/1125899906842624)), (2099/562949953421312), by norm_num⟩
  | 0 => ⟨((1088093558085877/1125899906842624), (39769587098167/1125899906842624)), (531/70368744177664), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088093558085877/1125899906842624), (39769587098167/1125899906842624)), (2025604516482331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((525075969854971/562949953421312), (76868345518567/1125899906842624)), (17023/1125899906842624), by norm_num⟩
  | 2 => ⟨((1948504209419241/2251799813685248), (286787277121253/2251799813685248)), (68161/2251799813685248), by norm_num⟩
  | 3 => ⟨((824767301522895/1125899906842624), (124079905612061/562949953421312)), (33831/562949953421312), by norm_num⟩
  | 4 => ⟨((1098957031605903/2251799813685248), (727148467126959/2251799813685248)), (64479/562949953421312), by norm_num⟩
  | 5 => ⟨((603039097831523/4503599627370496), (1419495491764567/4503599627370496)), (836633/4503599627370496), by norm_num⟩
  | 6 => ⟨((-366664764689711/4503599627370496), (760290746563913/9007199254740992)), (1502905/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9205111285/4294967296), (-340776721723/4294967296)), (1/2147483648), by norm_num⟩, -13, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-9501622235/4294967296), (-87938417475/1073741824)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((240650765080637/2251799813685248), (-13303554749661/562949953421312)), (582219/9007199254740992), by norm_num⟩
  | 1 => ⟨((-75348757967/274877906944), (16661593851/274877906944)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((193265748333/549755813888), (-85472288885/1099511627776)), (119/549755813888), by norm_num⟩
  | 3 => ⟨((-330477904671/1099511627776), (9134670519/137438953472)), (103/549755813888), by norm_num⟩
  | 4 => ⟨((105957386155/549755813888), (-93719869113/2199023255552)), (267/2199023255552), by norm_num⟩
  | 5 => ⟨((-217420263629/2199023255552), (96154687225/4398046511104)), (69/1099511627776), by norm_num⟩
  | 6 => ⟨((371781310329/8796093022208), (-82210634405/8796093022208)), (119/4398046511104), by norm_num⟩
  | 7 => ⟨((-272457209441/17592186044416), (7530932639/2199023255552)), (11/1099511627776), by norm_num⟩
  | 8 => ⟨((174709736073/35184372088832), (-38632921667/35184372088832)), (57/17592186044416), by norm_num⟩
  | 9 => ⟨((-24895645849/17592186044416), (88081322317/281474976710656)), (131/140737488355328), by norm_num⟩
  | 10 => ⟨((408678853273/1125899906842624), (-5648103277/70368744177664)), (271/1125899906842624), by norm_num⟩
  | 11 => ⟨((-190589193111/2251799813685248), (84288575251/4503599627370496)), (255/4503599627370496), by norm_num⟩
  | 12 => ⟨((162950542803/9007199254740992), (-72065308977/18014398509481984)), (55/4503599627370496), by norm_num⟩
  | 13 => ⟨((-257206086191/72057594037927936), (28437518147/36028797018963968)), (175/72057594037927936), by norm_num⟩
  | 14 => ⟨((47122898965/72057594037927936), (-83360907313/576460752303423488)), (259/576460752303423488), by norm_num⟩
  | 15 => ⟨((-64462853025/576460752303423488), (7127216855/288230376151711744)), (179/2305843009213693952), by norm_num⟩
  | 16 => ⟨((330687906893/18446744073709551616), (-73123801171/18446744073709551616)), (231/18446744073709551616), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039965283/10141204801825835211973625643008), (-70870012263/2535301200456458802993406410752)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((222319606563229/79228162514264337593543950336), (-335407687011/633825300114114700748351602688)), (721/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472375883806983/9903520314283042199192993792), (-2947351953/309485009821345068724781056)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889263835037247/2475880078570760549798248448), (-400749440441/2475880078570760549798248448)), (431/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770930220765811/154742504910672534362390528), (-100161938421/38685626227668133590597632)), (431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193663672821953/1208925819614629174706176), (-93874815829/2417851639229258349412352)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157321911343641/75557863725914323419136), (-82113472655/151115727451828646838272)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887445552461697/75557863725914323419136), (-266767612669/37778931862957161709568)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297279820422613/4722366482869645213696), (-399974452449/4722366482869645213696)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621091502906841/590295810358705651712), (-549677464501/590295810358705651712)), (1185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227878678454395/9223372036854775808), (-343333002163/36893488147419103232)), (1481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822156828442493/9223372036854775808), (-24122104115/288230376151711744)), (1667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593406295783147/1152921504606846976), (-385584060775/576460752303423488)), (1667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194074723108891/144115188075855872), (-336970724009/72057594037927936)), (1459/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490880497096241/36028797018963968), (-1009253235027/36028797018963968)), (547/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488315312988335/9007199254740992), (-19666699221/140737488355328)), (2735/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226074599002879/4503599627370496), (-627166365773/1125899906842624)), (171/140737488355328), by norm_num⟩
  | 1 => ⟨((1106660760847491/1125899906842624), (-58459259715/35184372088832)), (2053/562949953421312), by norm_num⟩
  | 0 => ⟨((2175279869764351/2251799813685248), (-1849202153213/562949953421312)), (4111/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175279869764351/2251799813685248), (-1849202153213/562949953421312)), (15682222606468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2101335904846893/2251799813685248), (-14290905237889/2251799813685248)), (3985/281474976710656), by norm_num⟩
  | 2 => ⟨((980417603774473/1125899906842624), (-416749860859/35184372088832)), (59905/2251799813685248), by norm_num⟩
  | 3 => ⟨((1707151449561261/2251799813685248), (-23225589982117/1125899906842624)), (105749/2251799813685248), by norm_num⟩
  | 4 => ⟨((1293280309341969/2251799813685248), (-35215918718811/1125899906842624)), (82353/1125899906842624), by norm_num⟩
  | 5 => ⟨((185142269827001/562949953421312), (-80902492268865/2251799813685248)), (398991/4503599627370496), by norm_num⟩
  | 6 => ⟨((240650765080637/2251799813685248), (-13303554749661/562949953421312)), (582219/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9501622235/4294967296), (-87938417475/1073741824)), (1/2147483648), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-361916736511/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-196170890820349/2251799813685248), (-244720462484409/4503599627370496)), (654581/4503599627370496), by norm_num⟩
  | 1 => ⟨((252786243787/1099511627776), (78836832303/549755813888)), (53/137438953472), by norm_num⟩
  | 2 => ⟨((-166779347373/549755813888), (-208054920133/1099511627776)), (281/549755813888), by norm_num⟩
  | 3 => ⟨((293426839409/1099511627776), (45755738495/274877906944)), (31/68719476736), by norm_num⟩
  | 4 => ⟨((-48398140703/274877906944), (-120752017047/1099511627776)), (329/1099511627776), by norm_num⟩
  | 5 => ⟨((204360748739/2199023255552), (63734299131/1099511627776)), (349/2199023255552), by norm_num⟩
  | 6 => ⟨((-44943310987/1099511627776), (-56066156423/2199023255552)), (309/4398046511104), by norm_num⟩
  | 7 => ⟨((135551970603/8796093022208), (84549600601/8796093022208)), (117/4398046511104), by norm_num⟩
  | 8 => ⟨((-89432355391/17592186044416), (-111565621591/35184372088832)), (155/17592186044416), by norm_num⟩
  | 9 => ⟨((209792989333/140737488355328), (130856920619/140737488355328)), (365/140737488355328), by norm_num⟩
  | 10 => ⟨((-221462290481/562949953421312), (-34533891549/140737488355328)), (97/140737488355328), by norm_num⟩
  | 11 => ⟨((106263941987/1125899906842624), (33140698041/562949953421312)), (375/2251799813685248), by norm_num⟩
  | 12 => ⟨((-93478878325/4503599627370496), (-116613602765/9007199254740992)), (83/2251799813685248), by norm_num⟩
  | 13 => ⟨((303625992625/72057594037927936), (189384604991/72057594037927936)), (541/72057594037927936), by norm_num⟩
  | 14 => ⟨((-28617371475/36028797018963968), (-71399547131/144115188075855872)), (205/144115188075855872), by norm_num⟩
  | 15 => ⟨((322230971501/2305843009213693952), (25123666425/288230376151711744)), (145/576460752303423488), by norm_num⟩
  | 16 => ⟨((-6643640681/288230376151711744), (-132605592051/9223372036854775808)), (385/9223372036854775808), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-3365815270891/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((222306239097175/79228162514264337593543950336), (-1990971152263/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944691389418159/19807040628566084398385987584), (-4478778345163/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944567469635345/1237940039285380274899124224), (-1189398758095/618970019642690137449562112)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770800659497077/154742504910672534362390528), (-4756349884927/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549187212296035/9671406556917033397649408), (-4457755313407/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314616921433377/151115727451828646838272), (-3899213493727/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471817342932701/18889465931478580854784), (-1583435762705/18889465931478580854784)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324286632206143/1180591620717411303424), (-2374069452593/2361183241434822606848)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620906350642045/590295810358705651712), (-1631292140363/147573952589676412928)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455698794196491/18446744073709551616), (-8151179133613/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821889438200465/9223372036854775808), (-572676109553/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | 6 => ⟨((99570880788975/72057594037927936), (-9153749365185/1152921504606846976)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((596915572017051/72057594037927936), (-3999667872059/72057594037927936)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((745252179433987/18014398509481984), (-5989315595119/18014398509481984)), (2215/36028797018963968), by norm_num⟩
  | 3 => ⟨((743913183747493/4503599627370496), (-14937676590001/9007199254740992)), (347/1125899906842624), by norm_num⟩
  | 2 => ⟨((556260171418941/1125899906842624), (-14884336760663/2251799813685248)), (2787/2251799813685248), by norm_num⟩
  | 1 => ⟨((552907906990927/562949953421312), (-22193431575227/1125899906842624)), (263/70368744177664), by norm_num⟩
  | 0 => ⟨((1085675077490727/1125899906842624), (-43856227478289/1125899906842624)), (533/70368744177664), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085675077490727/1125899906842624), (-43856227478289/1125899906842624)), (2033233911013581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((261294764757529/281474976710656), (-10572345924485/140737488355328)), (2139/140737488355328), by norm_num⟩
  | 2 => ⟨((240972952157053/281474976710656), (-39257466842081/281474976710656)), (17171/562949953421312), by norm_num⟩
  | 3 => ⟨((12551474297335/17592186044416), (-537738042063659/2251799813685248)), (68381/1125899906842624), by norm_num⟩
  | 4 => ⟨((1017836962005613/2251799813685248), (-767318535242937/2251799813685248)), (130235/1125899906842624), by norm_num⟩
  | 5 => ⟨((99301532929241/1125899906842624), (-693671934828071/2251799813685248)), (412985/2251799813685248), by norm_num⟩
  | 6 => ⟨((-196170890820349/2251799813685248), (-244720462484409/4503599627370496)), (654581/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-361916736511/4294967296)), (1/2147483648), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-5015863165/2147483648), (-185689162583/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((64820505148699/9007199254740992), (1737945391120953/18014398509481984)), (2149105/18014398509481984), by norm_num⟩
  | 1 => ⟨((-21427878663/1099511627776), (-287258506221/1099511627776)), (357/1099511627776), by norm_num⟩
  | 2 => ⟨((29013885561/1099511627776), (194477613885/549755813888)), (485/1099511627776), by norm_num⟩
  | 3 => ⟨((-6547588219/274877906944), (-175551713797/549755813888)), (439/1099511627776), by norm_num⟩
  | 4 => ⟨((17731197593/1099511627776), (118850713463/549755813888)), (597/2199023255552), by norm_num⟩
  | 5 => ⟨((-19206789283/2199023255552), (-64370739699/549755813888)), (325/2199023255552), by norm_num⟩
  | 6 => ⟨((4334412465/1099511627776), (464851185565/8796093022208)), (589/8796093022208), by norm_num⟩
  | 7 => ⟨((-26829272109/17592186044416), (-359668670443/17592186044416)), (229/8796093022208), by norm_num⟩
  | 8 => ⟨((36327507865/70368744177664), (487000407661/70368744177664)), (623/70368744177664), by norm_num⟩
  | 9 => ⟨((-10930746109/70368744177664), (-146535727989/70368744177664)), (377/140737488355328), by norm_num⟩
  | 10 => ⟨((23680807359/562949953421312), (317460886119/562949953421312)), (205/281474976710656), by norm_num⟩
  | 11 => ⟨((-11659784569/1125899906842624), (-312618187817/2251799813685248)), (203/1125899906842624), by norm_num⟩
  | 12 => ⟨((21050187965/9007199254740992), (282195248795/9007199254740992)), (23/562949953421312), by norm_num⟩
  | 13 => ⟨((-8769994731/18014398509481984), (-470276246307/72057594037927936)), (615/72057594037927936), by norm_num⟩
  | 14 => ⟨((13571191997/144115188075855872), (363866195253/288230376151711744)), (239/144115188075855872), by norm_num⟩
  | 15 => ⟨((-9800391791/576460752303423488), (-32845597441/144115188075855872)), (347/1152921504606846976), by norm_num⟩
  | 16 => ⟨((414686765/144115188075855872), (177895053511/4611686018427387904)), (59/1152921504606846976), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265802739/10141204801825835211973625643008), (1949149673665/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778363859258819/633825300114114700748351602688), (2305723409683/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944643152462457/19807040628566084398385987584), (1296704678675/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889032875931829/2475880078570760549798248448), (2754840729877/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770699090963713/154742504910672534362390528), (2754102184889/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((193636564646765/1208925819614629174706176), (1290593168295/4835703278458516698824704)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258385352483237/604462909807314587353088), (564438463835/151115727451828646838272)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943568281848321/37778931862957161709568), (3667380239239/75557863725914323419136)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648523891258575/2361183241434822606848), (1374624852253/2361183241434822606848)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810385984966693/295147905179352825856), (472266316469/73786976294838206464)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822629291336625/73786976294838206464), (4719533344281/73786976294838206464)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821705686939481/9223372036854775808), (5305174591009/9223372036854775808)), (837/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199119240248125/144115188075855872), (1324950921011/288230376151711744)), (1675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298419378425879/36028797018963968), (2315646150217/72057594037927936)), (1467/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490281928304887/36028797018963968), (6934882458087/36028797018963968)), (2203/36028797018963968), by norm_num⟩
  | 3 => ⟨((743781151853385/4503599627370496), (1080942589581/1125899906842624)), (1379/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224554274910719/4503599627370496), (17232036691269/4503599627370496)), (5527/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105502791630369/1125899906842624), (12845470215437/1125899906842624)), (8323/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085254021682555/1125899906842624), (25378199403481/1125899906842624)), (16773/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085254021682555/1125899906842624), (25378199403481/1125899906842624)), (63983925826262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2091006902868025/2251799813685248), (97848104607897/2251799813685248)), (8273/562949953421312), by norm_num⟩
  | 2 => ⟨((1937443812612459/2251799813685248), (45430562016261/562949953421312)), (64335/2251799813685248), by norm_num⟩
  | 3 => ⟨((1652307424921279/2251799813685248), (156353439141397/1125899906842624)), (30273/562949953421312), by norm_num⟩
  | 4 => ⟨((1168991230360125/2251799813685248), (229455519833717/1125899906842624)), (211341/2251799813685248), by norm_num⟩
  | 5 => ⟨((1026681987719365/4503599627370496), (119118710647887/562949953421312)), (611143/4503599627370496), by norm_num⟩
  | 6 => ⟨((64820505148699/9007199254740992), (1737945391120953/18014398509481984)), (2149105/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5015863165/2147483648), (-185689162583/2147483648)), (1/2147483648), by norm_num⟩, -14, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile066Terms1
