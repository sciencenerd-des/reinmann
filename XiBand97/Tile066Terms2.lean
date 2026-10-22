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
namespace Reinmann.XiBand97.Tile066Terms2
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
  | 0 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-2567700857/1073741824), (-380229050267/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((10881081106937/140737488355328), (-440861918690777/9007199254740992)), (638839/9007199254740992), by norm_num⟩
  | 1 => ⟨((-235693459085/1099511627776), (37302514155/274877906944)), (109/549755813888), by norm_num⟩
  | 2 => ⟨((163370256641/549755813888), (-206849060115/1099511627776)), (305/1099511627776), by norm_num⟩
  | 3 => ⟨((-301972354075/1099511627776), (11948070235/68719476736)), (71/274877906944), by norm_num⟩
  | 4 => ⟨((104655642917/549755813888), (-16563542393/137438953472)), (199/1099511627776), by norm_num⟩
  | 5 => ⟨((-29016705527/274877906944), (146956450685/2199023255552)), (223/2199023255552), by norm_num⟩
  | 6 => ⟨((214537041335/4398046511104), (-135816599277/4398046511104)), (13/274877906944), by norm_num⟩
  | 7 => ⟨((-169949423231/8796093022208), (53794795921/4398046511104)), (83/4398046511104), by norm_num⟩
  | 8 => ⟨((235599927101/35184372088832), (-74575422243/17592186044416)), (29/4398046511104), by norm_num⟩
  | 9 => ⟨((-290320755929/140737488355328), (183792866371/140737488355328)), (9/4398046511104), by norm_num⟩
  | 10 => ⟨((20123501343/35184372088832), (-203832811411/562949953421312)), (161/281474976710656), by norm_num⟩
  | 11 => ⟨((-324620758549/2251799813685248), (205507110597/2251799813685248)), (327/2251799813685248), by norm_num⟩
  | 12 => ⟨((300013284719/9007199254740992), (-47482224765/2251799813685248)), (305/9007199254740992), by norm_num⟩
  | 13 => ⟨((-127971299959/18014398509481984), (162029145711/36028797018963968)), (131/18014398509481984), by norm_num⟩
  | 14 => ⟨((202749590307/144115188075855872), (-128354337735/144115188075855872)), (209/144115188075855872), by norm_num⟩
  | 15 => ⟨((-37476081835/144115188075855872), (189799354269/1152921504606846976)), (39/144115188075855872), by norm_num⟩
  | 16 => ⟨((207811523699/4611686018427387904), (-32889721821/1152921504606846976)), (109/2305843009213693952), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (-735168235667/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778280532356127/633825300114114700748351602688), (-869578587911/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889192717959421/39614081257132168796771975168), (-244518277609/9903520314283042199192993792)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888933643790161/2475880078570760549798248448), (-519474637873/1237940039285380274899124224)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770600088124305/154742504910672534362390528), (-259666080405/38685626227668133590597632)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548999945482499/9671406556917033397649408), (-973445146369/9671406556917033397649408)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629152297769767/302231454903657293676544), (-425730985075/302231454903657293676544)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471751447358701/18889465931478580854784), (-691529355937/37778931862957161709568)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648475050115415/2361183241434822606848), (-1036798177461/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405159575868773/147573952589676412928), (-356198053377/147573952589676412928)), (1187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455615794253473/18446744073709551616), (-1779783196439/73786976294838206464)), (1483/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227690017285427/1152921504606846976), (-2000597754785/9223372036854775808)), (1669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592770032667499/1152921504606846976), (-999263448675/576460752303423488)), (1669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298379618259975/36028797018963968), (-873192081227/72057594037927936)), (1461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490047081640313/36028797018963968), (-653732398417/9007199254740992)), (137/2251799813685248), by norm_num⟩
  | 3 => ⟨((1487275221550701/9007199254740992), (-3260546293837/9007199254740992)), (2741/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223999443767903/4503599627370496), (-1624202280725/1125899906842624)), (5487/4503599627370496), by norm_num⟩
  | 1 => ⟨((552555334227061/562949953421312), (-9684727156307/2251799813685248)), (4121/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084564783074133/1125899906842624), (-19128836447011/2251799813685248)), (8267/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084564783074133/1125899906842624), (-19128836447011/2251799813685248)), (31536106589889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2089331890766543/2251799813685248), (-575830004557/35184372088832)), (4017/281474976710656), by norm_num⟩
  | 2 => ⟨((1937982928489953/2251799813685248), (-34194158393495/1125899906842624)), (3793/140737488355328), by norm_num⟩
  | 3 => ⟨((1665823421091133/2251799813685248), (-117715073636537/2251799813685248)), (27037/562949953421312), by norm_num⟩
  | 4 => ⟨((1226179527555665/2251799813685248), (-87082575230473/1125899906842624)), (85659/1125899906842624), by norm_num⟩
  | 5 => ⟨((1308449112757115/4503599627370496), (-94838688861671/1125899906842624)), (106539/1125899906842624), by norm_num⟩
  | 6 => ⟨((10881081106937/140737488355328), (-440861918690777/9007199254740992)), (638839/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-380229050267/4294967296)), (1/2147483648), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-388543028533/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-626729065274469/9007199254740992), (-936109032683565/18014398509481984)), (1115885/9007199254740992), by norm_num⟩
  | 1 => ⟨((3386797239/17179869184), (161877234063/1099511627776)), (97/274877906944), by norm_num⟩
  | 2 => ⟨((-307056612197/1099511627776), (-229316369823/1099511627776)), (69/137438953472), by norm_num⟩
  | 3 => ⟨((18124101897/68719476736), (13535462479/68719476736)), (131/274877906944), by norm_num⟩
  | 4 => ⟨((-102698894687/549755813888), (-76697705827/549755813888)), (373/1099511627776), by norm_num⟩
  | 5 => ⟨((116387151539/1099511627776), (86920385443/1099511627776)), (425/2199023255552), by norm_num⟩
  | 6 => ⟨((-219833087211/4398046511104), (-20521999659/549755813888)), (403/4398046511104), by norm_num⟩
  | 7 => ⟨((88976290879/4398046511104), (33224687589/2199023255552)), (41/1099511627776), by norm_num⟩
  | 8 => ⟨((-252088814623/35184372088832), (-188265256459/35184372088832)), (467/35184372088832), by norm_num⟩
  | 9 => ⟨((158715865217/70368744177664), (59266181869/35184372088832)), (37/8796093022208), by norm_num⟩
  | 10 => ⟨((-89935181449/140737488355328), (-67165494929/140737488355328)), (337/281474976710656), by norm_num⟩
  | 11 => ⟨((23164141471/140737488355328), (69197882361/562949953421312)), (349/1125899906842624), by norm_num⟩
  | 12 => ⟨((-87505272959/2251799813685248), (-65350787895/2251799813685248)), (331/4503599627370496), by norm_num⟩
  | 13 => ⟨((152566835091/18014398509481984), (28485034509/4503599627370496)), (579/36028797018963968), by norm_num⟩
  | 14 => ⟨((-247002510309/144115188075855872), (-184466696861/144115188075855872)), (471/144115188075855872), by norm_num⟩
  | 15 => ⟨((93308107763/288230376151711744), (139368935221/576460752303423488)), (179/288230376151711744), by norm_num⟩
  | 16 => ⟨((-264361776023/4611686018427387904), (-49357740877/1152921504606846976)), (255/2305843009213693952), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-3256697319729/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27784256639307/9903520314283042199192993792), (-120368271079/19807040628566084398385987584)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889093198502077/39614081257132168796771975168), (-4332322521881/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888827374581269/2475880078570760549798248448), (-4601943604739/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885246611757731/77371252455336267181195264), (-4600651170419/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548899127785233/9671406556917033397649408), (-4311737597447/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629107874237401/302231454903657293676544), (-3771397901235/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886860229904163/75557863725914323419136), (-191435905075/2361183241434822606848)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40526246767945/147573952589676412928), (-2296105738499/2361183241434822606848)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620485095357585/590295810358705651712), (-6310635640469/590295810358705651712)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911134576767029/36893488147419103232), (-3941407239017/36893488147419103232)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910649206103485/4611686018427387904), (-4430317737533/4611686018427387904)), (105/576460752303423488), by norm_num⟩
  | 6 => ⟨((796272001879779/576460752303423488), (-8851228390055/1152921504606846976)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193315869754435/144115188075855872), (-7734250713671/144115188075855872)), (737/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489733552411533/36028797018963968), (-11580249924339/36028797018963968)), (1107/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486866538622031/9007199254740992), (-14438391399193/9007199254740992)), (2775/9007199254740992), by norm_num⟩
  | 2 => ⟨((555783011879253/1125899906842624), (-898944337425/140737488355328)), (2785/2251799813685248), by norm_num⟩
  | 1 => ⟨((2208796156429811/2251799813685248), (-42873614840325/2251799813685248)), (1051/281474976710656), by norm_num⟩
  | 0 => ⟨((2165788773214329/2251799813685248), (-5290534796581/140737488355328)), (8517/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2165788773214329/2251799813685248), (-5290534796581/140737488355328)), (32489780906295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079880992776747/2251799813685248), (-162830543597677/2251799813685248)), (133/8796093022208), by norm_num⟩
  | 2 => ⟨((1909313222275021/2251799813685248), (-37599718080407/281474976710656)), (67823/2251799813685248), by norm_num⟩
  | 3 => ⟨((197342014816679/281474976710656), (-510096064123887/2251799813685248)), (8321/140737488355328), by norm_num⟩
  | 4 => ⟨((247825064617327/562949953421312), (-715256370002249/2251799813685248)), (123501/1125899906842624), by norm_num⟩
  | 5 => ⟨((209203555640035/2251799813685248), (-629748541718421/2251799813685248)), (93597/562949953421312), by norm_num⟩
  | 6 => ⟨((-626729065274469/9007199254740992), (-936109032683565/18014398509481984)), (1115885/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-388543028533/4294967296)), (1/2147483648), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-198190827873/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-562292624385917/18014398509481984), (1378943231931203/18014398509481984)), (2058305/18014398509481984), by norm_num⟩
  | 1 => ⟨((99196455151/1099511627776), (-243265293781/1099511627776)), (365/1099511627776), by norm_num⟩
  | 2 => ⟨((-71678658113/549755813888), (175781783705/549755813888)), (265/549755813888), by norm_num⟩
  | 3 => ⟨((34529661509/274877906944), (-169358234391/549755813888)), (513/1099511627776), by norm_num⟩
  | 4 => ⟨((-99803558435/1099511627776), (244754128825/1099511627776)), (373/1099511627776), by norm_num⟩
  | 5 => ⟨((115387754655/2199023255552), (-141486084317/1099511627776)), (433/2199023255552), by norm_num⟩
  | 6 => ⟨((-111171169087/4398046511104), (272631588163/4398046511104)), (419/4398046511104), by norm_num⟩
  | 7 => ⟨((22951857673/2199023255552), (-225144755067/8796093022208)), (87/2199023255552), by norm_num⟩
  | 8 => ⟨((-66339401209/17592186044416), (162688010371/17592186044416)), (505/35184372088832), by norm_num⟩
  | 9 => ⟨((85220236307/70368744177664), (-13061911959/4398046511104)), (163/35184372088832), by norm_num⟩
  | 10 => ⟨((-98527265689/281474976710656), (241624201155/281474976710656)), (379/281474976710656), by norm_num⟩
  | 11 => ⟨((103556518593/1125899906842624), (-126978866735/562949953421312)), (25/70368744177664), by norm_num⟩
  | 12 => ⟨((-6235767431/281474976710656), (122338710087/2251799813685248)), (97/1125899906842624), by norm_num⟩
  | 13 => ⟨((88731992967/18014398509481984), (-108801339241/9007199254740992)), (347/18014398509481984), by norm_num⟩
  | 14 => ⟨((-36638349499/36028797018963968), (44925188309/18014398509481984)), (575/144115188075855872), by norm_num⟩
  | 15 => ⟨((56479173679/288230376151711744), (-138507195207/288230376151711744)), (445/576460752303423488), by norm_num⟩
  | 16 => ⟨((-81622904255/2305843009213693952), (100084321323/1152921504606846976)), (81/576460752303423488), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (318811525877/1267650600228229401496703205376)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((222264943828279/79228162514264337593543950336), (3016291061397/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944505702004515/19807040628566084398385987584), (1696293658201/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888740716367987/2475880078570760549798248448), (3603706789657/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221300855568649/19342813113834066795298816), (1801337617815/77371252455336267181195264)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548818443997975/9671406556917033397649408), (1688206170099/4835703278458516698824704)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157268180802815/75557863725914323419136), (2953265478881/604462909807314587353088)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886746544066789/75557863725914323419136), (4797003475883/75557863725914323419136)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648377558663259/2361183241434822606848), (1797978545369/2361183241434822606848)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620369311305739/590295810358705651712), (617690597067/73786976294838206464)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911062801487945/36893488147419103232), (771566780419/9223372036854775808)), (745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821138537030133/9223372036854775808), (3469047067085/4611686018427387904)), (1677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796193074328621/576460752303423488), (6930591872265/1152921504606846976)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((298295003432677/36028797018963968), (6055836569941/144115188075855872)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((372383572323533/9007199254740992), (9066914019103/36028797018963968)), (69/1125899906842624), by norm_num⟩
  | 3 => ⟨((185828167636519/1125899906842624), (11304220071399/9007199254740992)), (2765/9007199254740992), by norm_num⟩
  | 2 => ⟨((138917073491345/281474976710656), (22520368618187/4503599627370496)), (5547/4503599627370496), by norm_num⟩
  | 1 => ⟨((552041559051299/562949953421312), (16780529297127/1125899906842624)), (8361/2251799813685248), by norm_num⟩
  | 0 => ⟨((135297497735199/140737488355328), (66248239228849/2251799813685248)), (8447/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((135297497735199/140737488355328), (66248239228849/2251799813685248)), (32222752097701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079135473347841/2251799813685248), (63687515684493/1125899906842624)), (33477/2251799813685248), by norm_num⟩
  | 2 => ⟨((1912505672903953/2251799813685248), (235216243050165/2251799813685248)), (8201/281474976710656), by norm_num⟩
  | 3 => ⟨((99985333010121/140737488355328), (399549193013189/2251799813685248)), (3911/70368744177664), by norm_num⟩
  | 4 => ⟨((532820353960423/1125899906842624), (141927568781415/562949953421312)), (222239/2251799813685248), by norm_num⟩
  | 5 => ⟨((722351211641471/4503599627370496), (1074651797734643/4503599627370496)), (80601/562949953421312), by norm_num⟩
  | 6 => ⟨((-562292624385917/18014398509481984), (1378943231931203/18014398509481984)), (2058305/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-198190827873/2147483648)), (1/2147483648), by norm_num⟩, -15, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-10907407117/4294967296), (-201898180505/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((1383376365957259/18014398509481984), (20391434803837/1125899906842624)), (853985/18014398509481984), by norm_num⟩
  | 1 => ⟨((-248612505785/1099511627776), (-58634116677/1099511627776)), (155/1099511627776), by norm_num⟩
  | 2 => ⟨((366012176371/1099511627776), (43161144663/549755813888)), (115/549755813888), by norm_num⟩
  | 3 => ⟨((-359233506319/1099511627776), (-42361785577/549755813888)), (57/274877906944), by norm_num⟩
  | 4 => ⟨((264435284657/1099511627776), (15591461585/274877906944)), (169/1099511627776), by norm_num⟩
  | 5 => ⟨((-311445423845/2199023255552), (-73452971573/2199023255552)), (201/2199023255552), by norm_num⟩
  | 6 => ⟨((152838674309/2199023255552), (72092597545/4398046511104)), (199/4398046511104), by norm_num⟩
  | 7 => ⟨((-128578328617/4398046511104), (-1895287985/274877906944)), (169/8796093022208), by norm_num⟩
  | 8 => ⟨((11830970083/1099511627776), (89288957117/35184372088832)), (251/35184372088832), by norm_num⟩
  | 9 => ⟨((-247719605147/70368744177664), (-58423530165/70368744177664)), (83/35184372088832), by norm_num⟩
  | 10 => ⟨((36469763065/35184372088832), (68809807807/281474976710656)), (99/140737488355328), by norm_num⟩
  | 11 => ⟨((-312386885613/1125899906842624), (-36837505501/562949953421312)), (107/562949953421312), by norm_num⟩
  | 12 => ⟨((306601374193/4503599627370496), (9038815591/562949953421312)), (53/1125899906842624), by norm_num⟩
  | 13 => ⟨((-138887544191/9007199254740992), (-65511977727/18014398509481984)), (97/9007199254740992), by norm_num⟩
  | 14 => ⟨((58420842691/18014398509481984), (27556574403/36028797018963968)), (165/72057594037927936), by norm_num⟩
  | 15 => ⟨((-11467773761/18014398509481984), (-43273947629/288230376151711744)), (261/576460752303423488), by norm_num⟩
  | 16 => ⟨((270129280529/2305843009213693952), (63708749091/2305843009213693952)), (97/1152921504606846976), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682407867/10141204801825835211973625643008), (301701751383/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222256565426801/79228162514264337593543950336), (178387177269/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944468140688647/19807040628566084398385987584), (401283170735/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888661273242717/2475880078570760549798248448), (426252978077/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55322744453077/4835703278458516698824704), (426128848937/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387186201971313/2417851639229258349412352), (399363959697/9671406556917033397649408)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629040730755065/302231454903657293676544), (349311685991/604462909807314587353088)), (707/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471660851331879/18889465931478580854784), (567384526579/75557863725914323419136)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648339247314885/2361183241434822606848), (106330606023/1180591620717411303424)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620265142068891/590295810358705651712), (584467608955/590295810358705651712)), (1185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821997169290267/73786976294838206464), (730058824421/73786976294838206464)), (741/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820996489477683/9223372036854775808), (102574250845/1152921504606846976)), (1667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592247145221733/1152921504606846976), (204923066321/288230376151711744)), (1667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149132725211205/18014398509481984), (358108803877/72057594037927936)), (1459/144115188075855872), by norm_num⟩
  | 4 => ⟨((186170472692143/4503599627370496), (1072303495089/36028797018963968)), (547/9007199254740992), by norm_num⟩
  | 3 => ⟨((371606018971113/2251799813685248), (1336846749237/9007199254740992)), (171/562949953421312), by norm_num⟩
  | 2 => ⟨((2222306060295503/4503599627370496), (332890688925/562949953421312)), (5473/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207703424845861/2251799813685248), (496046569583/281474976710656)), (4107/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082090879164451/1125899906842624), (979013183627/281474976710656)), (16449/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1082090879164451/1125899906842624), (979013183627/281474976710656)), (62747963912200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079945700653729/2251799813685248), (7527356420557/1125899906842624)), (31733/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921106595265877/2251799813685248), (27811517754063/2251799813685248)), (59047/2251799813685248), by norm_num⟩
  | 3 => ⟨((1638634592395445/2251799813685248), (11863596811975/562949953421312)), (51105/1125899906842624), by norm_num⟩
  | 4 => ⟨((1191434243941597/2251799813685248), (4316569352255/140737488355328)), (153065/2251799813685248), by norm_num⟩
  | 5 => ⟨((1256546483101709/4503599627370496), (73085126112821/2251799813685248)), (42841/562949953421312), by norm_num⟩
  | 6 => ⟨((1383376365957259/18014398509481984), (20391434803837/1125899906842624)), (853985/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10907407117/4294967296), (-201898180505/2147483648)), (1/2147483648), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-11097418473/4294967296), (-410830653711/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((222830979583199/18014398509481984), (-1341438232988123/18014398509481984)), (1632727/18014398509481984), by norm_num⟩
  | 1 => ⟨((-20371763827/549755813888), (30659407101/137438953472)), (75/274877906944), by norm_num⟩
  | 2 => ⟨((30514175183/549755813888), (-183694750681/549755813888)), (451/1099511627776), by norm_num⟩
  | 3 => ⟨((-60941532931/1099511627776), (366866862065/1099511627776)), (113/274877906944), by norm_num⟩
  | 4 => ⟨((22820564625/549755813888), (-274758724697/1099511627776)), (85/274877906944), by norm_num⟩
  | 5 => ⟨((-27345720779/1099511627776), (164620715803/1099511627776)), (205/1099511627776), by norm_num⟩
  | 6 => ⟨((27306819427/2199023255552), (-164386530409/2199023255552)), (411/4398046511104), by norm_num⟩
  | 7 => ⟨((-46745097283/8796093022208), (140702295567/4398046511104)), (353/8796093022208), by norm_num⟩
  | 8 => ⟨((70017898281/35184372088832), (-210753203897/17592186044416)), (531/35184372088832), by norm_num⟩
  | 9 => ⟨((-2913262189/4398046511104), (280604522075/70368744177664)), (355/70368744177664), by norm_num⟩
  | 10 => ⟨((27927531395/140737488355328), (-168123204577/140737488355328)), (427/281474976710656), by norm_num⟩
  | 11 => ⟨((-30423057135/562949953421312), (366292443553/1125899906842624)), (467/1125899906842624), by norm_num⟩
  | 12 => ⟨((3797472255/281474976710656), (-45721420613/562949953421312)), (117/1125899906842624), by norm_num⟩
  | 13 => ⟨((-56005957869/18014398509481984), (168577397321/9007199254740992)), (433/18014398509481984), by norm_num⟩
  | 14 => ⟨((47936815857/72057594037927936), (-288578714141/72057594037927936)), (93/18014398509481984), by norm_num⟩
  | 15 => ⟨((-76589795389/576460752303423488), (461069102621/576460752303423488)), (149/144115188075855872), by norm_num⟩
  | 16 => ⟨((14340157617/576460752303423488), (-345309897765/2305843009213693952)), (7/36028797018963968), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054261013/10141204801825835211973625643008), (-228964271681/1267650600228229401496703205376)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777981931200231/633825300114114700748351602688), (-541479198933/158456325028528675187087900672)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944428373831509/19807040628566084398385987584), (-2436110191177/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236072076318097/309485009821345068724781056), (-2587684874665/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770242982124741/154742504910672534362390528), (-323364714993/19342813113834066795298816)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774332540707003/4835703278458516698824704), (-2424420551025/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258011512406689/604462909807314587353088), (-530138374383/151115727451828646838272)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886529385089101/75557863725914323419136), (-430546621127/9444732965739290427392)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296592671005211/4722366482869645213696), (-645486191051/1180591620717411303424)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405036658518807/147573952589676412928), (-3548006036923/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821848284782229/73786976294838206464), (-4431757799521/73786976294838206464)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820827965848517/9223372036854775808), (-4981262815779/9223372036854775808)), (837/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592077338931197/1152921504606846976), (-4975687464849/1152921504606846976)), (1675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596455891178995/72057594037927936), (-1086865466297/36028797018963968)), (1467/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489135885279115/36028797018963968), (-6508682450955/36028797018963968)), (1101/18014398509481984), by norm_num⟩
  | 3 => ⟨((185766776397767/1125899906842624), (-8114002615935/9007199254740992)), (689/2251799813685248), by norm_num⟩
  | 2 => ⟨((277713930093995/562949953421312), (-8081312112971/2251799813685248)), (5523/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103387297159511/1125899906842624), (-12040539329659/1125899906842624)), (8315/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162178426354315/2251799813685248), (-1484821402063/70368744177664)), (16751/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162178426354315/2251799813685248), (-1484821402063/70368744177664)), (63900002486418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2075121381451025/2251799813685248), (-45623221503345/1125899906842624)), (8219/562949953421312), by norm_num⟩
  | 2 => ⟨((1908607864817319/2251799813685248), (-168174314354039/2251799813685248)), (31629/1125899906842624), by norm_num⟩
  | 3 => ⟨((401290265642959/562949953421312), (-17817903765559/140737488355328)), (29171/562949953421312), by norm_num⟩
  | 4 => ⟨((277030370530115/562949953421312), (-50804880908699/281474976710656)), (195899/2251799813685248), by norm_num⟩
  | 5 => ⟨((943903195597279/4503599627370496), (-800042413565919/4503599627370496)), (65881/562949953421312), by norm_num⟩
  | 6 => ⟨((222830979583199/18014398509481984), (-1341438232988123/18014398509481984)), (1632727/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-11097418473/4294967296), (-410830653711/4294967296)), (1/2147483648), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-5639078605/2147483648), (-208760835267/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-1283291537139279/18014398509481984), (-230250668037187/18014398509481984)), (218009/2251799813685248), by norm_num⟩
  | 1 => ⟨((238464958433/1099511627776), (21392923741/549755813888)), (163/549755813888), by norm_num⟩
  | 2 => ⟨((-45375744785/137438953472), (-32565618169/549755813888)), (249/549755813888), by norm_num⟩
  | 3 => ⟨((184196630835/549755813888), (66097836809/1099511627776)), (127/274877906944), by norm_num⟩
  | 4 => ⟨((-280395387765/1099511627776), (-50309086813/1099511627776)), (389/1099511627776), by norm_num⟩
  | 5 => ⟨((170734009897/1099511627776), (61266857449/2199023255552)), (119/549755813888), by norm_num⟩
  | 6 => ⟨((-86633920669/1099511627776), (-62176107397/4398046511104)), (485/4398046511104), by norm_num⟩
  | 7 => ⟨((150719380197/4398046511104), (13521182433/2199023255552)), (53/1099511627776), by norm_num⟩
  | 8 => ⟨((-229434267405/17592186044416), (-20582771651/8796093022208)), (81/4398046511104), by norm_num⟩
  | 9 => ⟨((38806543061/8796093022208), (55701964553/70368744177664)), (55/8796093022208), by norm_num⟩
  | 10 => ⟨((-378071651455/281474976710656), (-67834352363/281474976710656)), (269/140737488355328), by norm_num⟩
  | 11 => ⟨((418562773063/1125899906842624), (75099348297/1125899906842624)), (299/562949953421312), by norm_num⟩
  | 12 => ⟨((-424774584729/4503599627370496), (-38106941825/2251799813685248)), (609/4503599627370496), by norm_num⟩
  | 13 => ⟨((397918693595/18014398509481984), (71395347335/18014398509481984)), (143/4503599627370496), by norm_num⟩
  | 14 => ⟨((-346134968869/72057594037927936), (-31052105273/36028797018963968)), (499/72057594037927936), by norm_num⟩
  | 15 => ⟨((140508757227/144115188075855872), (12605177499/72057594037927936)), (407/288230376151711744), by norm_num⟩
  | 16 => ⟨((-427782064075/2305843009213693952), (-38376745727/1152921504606846976)), (311/1152921504606846976), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790277619193693/5070602400912917605986812821504), (-1930509337509/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((888954227765113/316912650057057350374175801344), (-1141289405833/158456325028528675187087900672)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236096703692979/4951760157141521099596496896), (-2567304258537/19807040628566084398385987584)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((29507620053699/38685626227668133590597632), (-5454057414541/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442538341224637/38685626227668133590597632), (-2726205268609/77371252455336267181195264)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548580332618863/9671406556917033397649408), (-2554942740259/4835703278458516698824704)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257936625245863/604462909807314587353088), (-4469400856607/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((58950197576983/2361183241434822606848), (-453718631741/4722366482869645213696)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296499175864569/4722366482869645213696), (-42513719209/36893488147419103232)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620016133934153/590295810358705651712), (-3738878344377/295147905179352825856)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910841123926451/36893488147419103232), (-4670106114527/36893488147419103232)), (747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820637178322811/9223372036854775808), (-5249070737967/4611686018427387904)), (1683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397970391984185/288230376151711744), (-10486152695531/1152921504606846976)), (1685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192734892134721/144115188075855872), (-9161906991485/144115188075855872)), (1477/144115188075855872), by norm_num⟩
  | 4 => ⟨((744429704084681/18014398509481984), (-13715934172707/36028797018963968)), (555/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485769205226353/9007199254740992), (-17097857282721/9007199254740992)), (2783/9007199254740992), by norm_num⟩
  | 2 => ⟨((555230888342201/1125899906842624), (-17027387986295/2251799813685248)), (2795/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102724653384825/1125899906842624), (-25365334003883/1125899906842624)), (33/8796093022208), by norm_num⟩
  | 0 => ⟨((1079480692850629/1125899906842624), (-50030231871845/1125899906842624)), (4289/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079480692850629/1125899906842624), (-50030231871845/1125899906842624)), (16361238719749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1032752143480419/1125899906842624), (-23983779124713/281474976710656)), (4303/281474976710656), by norm_num⟩
  | 2 => ⟨((939136273890419/1125899906842624), (-175996456873465/1125899906842624)), (69019/2251799813685248), by norm_num⟩
  | 3 => ⟨((1511683557184481/2251799813685248), (-587209060846525/2251799813685248)), (136719/2251799813685248), by norm_num⟩
  | 4 => ⟨((861698577346489/2251799813685248), (-197103285229135/562949953421312)), (31859/281474976710656), by norm_num⟩
  | 5 => ⟨((26851666985701/1125899906842624), (-37712859606801/140737488355328)), (747079/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1283291537139279/18014398509481984), (-230250668037187/18014398509481984)), (218009/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5639078605/2147483648), (-208760835267/2147483648)), (1/2147483648), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile066Terms2
