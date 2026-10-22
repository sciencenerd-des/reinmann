/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile064Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨64,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (16205/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (16205/512))
  have he : value ((69/80), (16205/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2862621597/1073741824), (-820680179/8388608)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1131425723101315/18014398509481984), (537261501948137/18014398509481984)), (1762733/4503599627370496), by norm_num⟩
  | 1 => ⟨((13341083309/68719476736), (-25340242173/274877906944)), (335/274877906944), by norm_num⟩
  | 2 => ⟨((-20618927441/68719476736), (4895485271/34359738368)), (65/34359738368), by norm_num⟩
  | 3 => ⟨((21244660021/68719476736), (-40352407473/274877906944)), (269/137438953472), by norm_num⟩
  | 4 => ⟨((-4104259127/17179869184), (31182751149/274877906944)), (209/137438953472), by norm_num⟩
  | 5 => ⟨((81193210887/549755813888), (-19277441523/274877906944)), (519/549755813888), by norm_num⟩
  | 6 => ⟨((-5228576287/68719476736), (4965615845/137438953472)), (537/1099511627776), by norm_num⟩
  | 7 => ⟨((73882291537/2199023255552), (-35083267163/2199023255552)), (119/549755813888), by norm_num⟩
  | 8 => ⟨((-57093324923/4398046511104), (27110967051/4398046511104)), (369/4398046511104), by norm_num⟩
  | 9 => ⟨((78434618285/17592186044416), (-37244955603/17592186044416)), (509/17592186044416), by norm_num⟩
  | 10 => ⟨((-24244473493/17592186044416), (23025147789/35184372088832)), (317/35184372088832), by norm_num⟩
  | 11 => ⟨((54502324965/140737488355328), (-50548089/274877906944)), (179/70368744177664), by norm_num⟩
  | 12 => ⟨((-56156333425/562949953421312), (26666033329/562949953421312)), (371/562949953421312), by norm_num⟩
  | 13 => ⟨((53409726351/2251799813685248), (-3170224657/281474976710656)), (355/2251799813685248), by norm_num⟩
  | 14 => ⟨((-11792266541/2251799813685248), (11199198859/4503599627370496)), (315/9007199254740992), by norm_num⟩
  | 15 => ⟨((38880422933/36028797018963968), (-36925012391/72057594037927936)), (521/72057594037927936), by norm_num⟩
  | 16 => ⟨((-60090518945/288230376151711744), (28534195223/288230376151711744)), (101/72057594037927936), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (3514789898529/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777848575032863/633825300114114700748351602688), (2077755609057/316912650057057350374175801344)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118044149114745/2475880078570760549798248448), (4673853328447/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888416397339045/2475880078570760549798248448), (2482308357759/1237940039285380274899124224)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885041129517391/77371252455336267181195264), (1240773893803/38685626227668133590597632)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548513862234693/9671406556917033397649408), (4651286327563/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314469663717655/151115727451828646838272), (4068260253821/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943156239400413/37778931862957161709568), (1651973825365/18889465931478580854784)), (2311/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648214553108471/2361183241434822606848), (1238318340183/1180591620717411303424)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619920296349515/590295810358705651712), (3403224820779/295147905179352825856)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821563212084247/73786976294838206464), (4250806817181/36893488147419103232)), (5969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910252154014949/4611686018427387904), (4777727166389/4611686018427387904)), (6721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591750001249677/1152921504606846976), (9544386428045/1152921504606846976)), (6729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298155308574819/36028797018963968), (8338898216805/144115188075855872)), (5897/144115188075855872), by norm_num⟩
  | 4 => ⟨((186086479825743/4503599627370496), (12483496223125/36028797018963968)), (8863/36028797018963968), by norm_num⟩
  | 3 => ⟨((742782414244451/4503599627370496), (15560945456963/9007199254740992)), (11109/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220529976226727/4503599627370496), (15495937440709/2251799813685248)), (22311/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204896604922915/2251799813685248), (23081838389593/1125899906842624)), (8425/562949953421312), by norm_num⟩
  | 0 => ⟨((1079002490429071/1125899906842624), (22759059678509/562949953421312)), (17085/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079002490429071/1125899906842624), (22759059678509/562949953421312)), (65174104930686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2064436577531015/2251799813685248), (87244281391943/1125899906842624)), (136513/2251799813685248), by norm_num⟩
  | 2 => ⟨((939571115156209/1125899906842624), (319940137824545/2251799813685248)), (135733/1125899906842624), by norm_num⟩
  | 3 => ⟨((761349612233251/1125899906842624), (533984433699855/2251799813685248)), (265111/1125899906842624), by norm_num⟩
  | 4 => ⟨((451521831647457/1125899906842624), (722175815212681/2251799813685248)), (484279/1125899906842624), by norm_num⟩
  | 5 => ⟨((130540000915057/2251799813685248), (1158462292694385/4503599627370496)), (1398099/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1131425723101315/18014398509481984), (537261501948137/18014398509481984)), (1762733/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-820680179/8388608)), (1/536870912), by norm_num⟩, -16, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1451894239/536870912), (-6659857943/67108864)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((332478466404385/18014398509481984), (289658849822291/4503599627370496)), (5554437/18014398509481984), by norm_num⟩
  | 1 => ⟨((-7953524081/137438953472), (-55433572279/274877906944)), (267/274877906944), by norm_num⟩
  | 2 => ⟨((1558639297/17179869184), (86905822625/274877906944)), (421/274877906944), by norm_num⟩
  | 3 => ⟨((-3258069667/34359738368), (-90830901391/274877906944)), (221/137438953472), by norm_num⟩
  | 4 => ⟨((2553914649/34359738368), (71199941485/274877906944)), (87/68719476736), by norm_num⟩
  | 5 => ⟨((-800778461/17179869184), (-89298801881/549755813888)), (439/549755813888), by norm_num⟩
  | 6 => ⟨((26782253149/1099511627776), (93331958929/1099511627776)), (461/1099511627776), by norm_num⟩
  | 7 => ⟨((-23993028525/2199023255552), (-5225746739/137438953472)), (415/2199023255552), by norm_num⟩
  | 8 => ⟨((18807500541/4398046511104), (8192649337/549755813888)), (327/4398046511104), by norm_num⟩
  | 9 => ⟨((-26209248517/17592186044416), (-22833781875/4398046511104)), (229/8796093022208), by norm_num⟩
  | 10 => ⟨((8217894713/17592186044416), (28638076399/17592186044416)), (289/35184372088832), by norm_num⟩
  | 11 => ⟨((-9369876851/70368744177664), (-65305107567/140737488355328)), (331/140737488355328), by norm_num⟩
  | 12 => ⟨((4896532445/140737488355328), (68254595683/562949953421312)), (87/140737488355328), by norm_num⟩
  | 13 => ⟨((-2362007563/281474976710656), (-16462453075/562949953421312)), (337/2251799813685248), by norm_num⟩
  | 14 => ⟨((16928139547/9007199254740992), (29495957941/4503599627370496)), (303/9007199254740992), by norm_num⟩
  | 15 => ⟨((-28308311273/72057594037927936), (-12331254069/9007199254740992)), (509/72057594037927936), by norm_num⟩
  | 16 => ⟨((22190136565/288230376151711744), (77329151617/288230376151711744)), (401/288230376151711744), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (1682125181753/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777796671475967/633825300114114700748351602688), (994319367307/316912650057057350374175801344)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944324200204287/19807040628566084398385987584), (2236695791231/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888355330363017/2475880078570760549798248448), (1187916910109/1237940039285380274899124224)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885010900879169/77371252455336267181195264), (1187548387007/77371252455336267181195264)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193557228853109/1208925819614629174706176), (2225870413339/9671406556917033397649408)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628915137044965/302231454903657293676544), (1946854136155/604462909807314587353088)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471558767840019/18889465931478580854784), (1581085772495/37778931862957161709568)), (2303/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324093027327271/1180591620717411303424), (2370346250725/4722366482869645213696)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619843643622793/590295810358705651712), (3257143521481/590295810358705651712)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455367492287323/18446744073709551616), (127134621405/2305843009213693952)), (5943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910201470488967/4611686018427387904), (4572558089291/9223372036854775808)), (209/288230376151711744), by norm_num⟩
  | 6 => ⟨((1591653038389565/1152921504606846976), (4567203439165/1152921504606846976)), (1673/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192541332960855/144115188075855872), (1995143429517/72057594037927936)), (1465/36028797018963968), by norm_num⟩
  | 4 => ⟨((744290917554107/18014398509481984), (186669298151/1125899906842624)), (8799/36028797018963968), by norm_num⟩
  | 3 => ⟨((742722241542139/4503599627370496), (7445793542171/9007199254740992)), (2753/2251799813685248), by norm_num⟩
  | 2 => ⟨((555085114863395/1125899906842624), (7414413643259/2251799813685248)), (22069/4503599627370496), by norm_num⟩
  | 1 => ⟨((551184802140509/562949953421312), (22086953624583/2251799813685248)), (519/35184372088832), by norm_num⟩
  | 0 => ⟨((2158191395459473/2251799813685248), (21776209399897/1125899906842624)), (16721/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158191395459473/2251799813685248), (21776209399897/1125899906842624)), (63785555125999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((516907992659465/562949953421312), (83483846951149/2251799813685248)), (130795/2251799813685248), by norm_num⟩
  | 2 => ⟨((1895431550958743/2251799813685248), (153311915152473/2251799813685248)), (124947/1125899906842624), by norm_num⟩
  | 3 => ⟨((792511883017021/1125899906842624), (64524439373305/562949953421312)), (454721/2251799813685248), by norm_num⟩
  | 4 => ⟨((1086102712863783/2251799813685248), (181672934290431/1125899906842624)), (744389/2251799813685248), by norm_num⟩
  | 5 => ⟨((465227360047077/2251799813685248), (701005357892231/4503599627370496)), (29947/70368744177664), by norm_num⟩
  | 6 => ⟨((332478466404385/18014398509481984), (289658849822291/4503599627370496)), (5554437/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-6659857943/67108864)), (1/536870912), by norm_num⟩, -16, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-735800759/268435456), (-54002043921/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((580074810162377/9007199254740992), (-32332126357691/9007199254740992)), (2386747/18014398509481984), by norm_num⟩
  | 1 => ⟨((-56259429087/274877906944), (6271559937/549755813888)), (117/274877906944), by norm_num⟩
  | 2 => ⟨((89397747051/274877906944), (-2491419385/137438953472)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((-11837952185/34359738368), (5278576613/274877906944)), (201/274877906944), by norm_num⟩
  | 4 => ⟨((37621649285/137438953472), (-1048475039/68719476736)), (161/274877906944), by norm_num⟩
  | 5 => ⟨((-95650901291/549755813888), (2665688091/274877906944)), (103/274877906944), by norm_num⟩
  | 6 => ⟨((12665988051/137438953472), (-5647800165/1099511627776)), (55/274877906944), by norm_num⟩
  | 7 => ⟨((-23001823909/549755813888), (2564144707/1099511627776)), (101/1099511627776), by norm_num⟩
  | 8 => ⟨((73101034579/4398046511104), (-2037247477/2199023255552)), (81/2199023255552), by norm_num⟩
  | 9 => ⟨((-103252899087/17592186044416), (2877547621/8796093022208)), (231/17592186044416), by norm_num⟩
  | 10 => ⟨((65628654287/35184372088832), (-228625031/2199023255552)), (149/35184372088832), by norm_num⟩
  | 11 => ⟨((-37922072025/70368744177664), (1056847499/35184372088832)), (87/70368744177664), by norm_num⟩
  | 12 => ⟨((20086397709/140737488355328), (-2239145495/281474976710656)), (93/281474976710656), by norm_num⟩
  | 13 => ⟨((-19641739439/562949953421312), (4379153795/2251799813685248)), (183/2251799813685248), by norm_num⟩
  | 14 => ⟨((35670003005/4503599627370496), (-1988169499/4503599627370496)), (21/1125899906842624), by norm_num⟩
  | 15 => ⟨((-30229650581/18014398509481984), (6739743671/72057594037927936)), (287/72057594037927936), by norm_num⟩
  | 16 => ⟨((96071456819/288230376151711744), (-5354817047/288230376151711744)), (115/144115188075855872), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-36264866707/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222217782725127/79228162514264337593543950336), (-85740759249/633825300114114700748351602688)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888587319961707/39614081257132168796771975168), (-96435644357/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944145303136383/1237940039285380274899124224), (-51217121175/1237940039285380274899124224)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769957273065589/154742504910672534362390528), (-25600512815/38685626227668133590597632)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193549692827825/1208925819614629174706176), (-95967734341/9671406556917033397649408)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257777729176909/604462909807314587353088), (-20984398737/151115727451828646838272)), (1413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886150074107331/75557863725914323419136), (-136334552395/75557863725914323419136)), (287/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296308700682897/4722366482869645213696), (-102194914031/4722366482869645213696)), (861/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619757007417969/590295810358705651712), (-140427070453/590295810358705651712)), (37/4611686018427387904), by norm_num⟩
  | 8 => ⟨((455340624651227/18446744073709551616), (-175397545627/73786976294838206464)), (185/2305843009213693952), by norm_num⟩
  | 7 => ⟨((910141584264361/4611686018427387904), (-98567509333/4611686018427387904)), (1665/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591534677738693/1152921504606846976), (-98450633037/576460752303423488)), (1665/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192439351419071/144115188075855872), (-172026010505/144115188075855872)), (1457/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488432020260619/36028797018963968), (-32189344447/4503599627370496)), (4371/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485262716323823/9007199254740992), (-10030565239/281474976710656)), (683/562949953421312), by norm_num⟩
  | 2 => ⟨((554998334146769/1125899906842624), (-319609239445/2251799813685248)), (10929/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204259220719939/2251799813685248), (-952012697097/2251799813685248)), (32793/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078696117932061/1125899906842624), (-469234978659/562949953421312)), (32807/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078696117932061/1125899906842624), (-469234978659/562949953421312)), (125148777488326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2066941167761339/2251799813685248), (-899124241509/562949953421312)), (125837/2251799813685248), by norm_num⟩
  | 2 => ⟨((948626256701819/1125899906842624), (-206327944697/70368744177664)), (28927/281474976710656), by norm_num⟩
  | 3 => ⟨((99906846870067/140737488355328), (-5562927351289/1125899906842624)), (391317/2251799813685248), by norm_num⟩
  | 4 => ⟨((567348167678451/1125899906842624), (-15796062229883/2251799813685248)), (559445/2251799813685248), by norm_num⟩
  | 5 => ⟨((1143339874234795/4503599627370496), (-31838947345829/4503599627370496)), (1143331/4503599627370496), by norm_num⟩
  | 6 => ⟨((580074810162377/9007199254740992), (-32332126357691/9007199254740992)), (2386747/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-54002043921/536870912)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-745252095/268435456), (-109391396717/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((248174262060647/18014398509481984), (-1093953879162513/18014398509481984)), (1322269/4503599627370496), by norm_num⟩
  | 1 => ⟨((-6094681797/137438953472), (3358174987/17179869184)), (261/274877906944), by norm_num⟩
  | 2 => ⟨((19618023897/274877906944), (-86476386251/274877906944)), (211/137438953472), by norm_num⟩
  | 3 => ⟨((-10524663809/137438953472), (46392791521/137438953472)), (227/137438953472), by norm_num⟩
  | 4 => ⟨((8469396475/137438953472), (-37333158769/137438953472)), (367/274877906944), by norm_num⟩
  | 5 => ⟨((-5452387113/137438953472), (48068320891/274877906944)), (475/549755813888), by norm_num⟩
  | 6 => ⟨((23400742755/1099511627776), (-25787659343/274877906944)), (1/2147483648), by norm_num⟩
  | 7 => ⟨((-10760583591/1099511627776), (94865455131/2199023255552)), (473/2199023255552), by norm_num⟩
  | 8 => ⟨((17318491191/4398046511104), (-38170015017/2199023255552)), (383/4398046511104), by norm_num⟩
  | 9 => ⟨((-24776032275/17592186044416), (109212923177/17592186044416)), (275/8796093022208), by norm_num⟩
  | 10 => ⟨((15950194265/35184372088832), (-17577141909/8796093022208)), (89/8796093022208), by norm_num⟩
  | 11 => ⟨((-4667426793/35184372088832), (82296199507/140737488355328)), (419/140737488355328), by norm_num⟩
  | 12 => ⟨((20031823025/562949953421312), (-88300415691/562949953421312)), (113/140737488355328), by norm_num⟩
  | 13 => ⟨((-19839984881/2251799813685248), (43727395907/1125899906842624)), (449/2251799813685248), by norm_num⟩
  | 14 => ⟨((4561603407/2251799813685248), (-80430318611/9007199254740992)), (415/9007199254740992), by norm_num⟩
  | 15 => ⟨((-7831058629/18014398509481984), (69038722177/36028797018963968)), (179/18014398509481984), by norm_num⟩
  | 16 => ⟨((3150900663/36028797018963968), (-55556768449/144115188075855872)), (289/144115188075855872), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-1755545764955/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888842869649419/316912650057057350374175801344), (-518797821189/158456325028528675187087900672)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888523621193169/39614081257132168796771975168), (-1167015455385/19807040628566084398385987584)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236027846950859/309485009821345068724781056), (-1239602841699/1237940039285380274899124224)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769889273062257/154742504910672534362390528), (-2478416133419/154742504910672534362390528)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774166806430355/4835703278458516698824704), (-1161338278229/4835703278458516698824704)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628860805529639/302231454903657293676544), (-1015751893813/302231454903657293676544)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943029272924661/37778931862957161709568), (-824905703937/18889465931478580854784)), (4607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296239760599875/4722366482869645213696), (-2473343411639/4722366482869645213696)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1619661737959585/590295810358705651712), (-3398616397491/590295810358705651712)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821242697784957/73786976294838206464), (-4244926876051/73786976294838206464)), (743/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820147412920283/9223372036854775808), (-4770949429005/9223372036854775808)), (3345/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397849425151871/288230376151711744), (-4765214048135/1152921504606846976)), (3347/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192318126449459/144115188075855872), (-1040779644051/36028797018963968)), (2931/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488247453405381/36028797018963968), (-6231811873293/36028797018963968)), (8801/36028797018963968), by norm_num⟩
  | 3 => ⟨((371256813748343/2251799813685248), (-7767297521985/9007199254740992)), (11017/9007199254740992), by norm_num⟩
  | 2 => ⟨((554877062516691/1125899906842624), (-15467385358259/4503599627370496)), (22079/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203496510273193/2251799813685248), (-11516862523967/1125899906842624)), (8309/562949953421312), by norm_num⟩
  | 0 => ⟨((2155728454207383/2251799813685248), (-45402051666145/2251799813685248)), (66943/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155728454207383/2251799813685248), (-45402051666145/2251799813685248)), (255367287642668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062840485976317/2251799813685248), (-86930013992605/2251799813685248)), (130875/2251799813685248), by norm_num⟩
  | 2 => ⟨((943190868352207/1125899906842624), (-79635299381679/1125899906842624)), (249891/2251799813685248), by norm_num⟩
  | 3 => ⟨((1568997790775805/2251799813685248), (-266848897379979/2251799813685248)), (454029/2251799813685248), by norm_num⟩
  | 4 => ⟨((1061615565867789/2251799813685248), (-185933637579859/1125899906842624)), (370161/1125899906842624), by norm_num⟩
  | 5 => ⟨((439089804230829/2251799813685248), (-701270308927343/4503599627370496)), (471285/1125899906842624), by norm_num⟩
  | 6 => ⟨((248174262060647/18014398509481984), (-1093953879162513/18014398509481984)), (1322269/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-109391396717/1073741824)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-3017330773/1073741824), (-110724287087/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-461537201967713/9007199254740992), (-569159264793773/18014398509481984)), (3094441/9007199254740992), by norm_num⟩
  | 1 => ⟨((45890281979/274877906944), (7073882409/68719476736)), (309/274877906944), by norm_num⟩
  | 2 => ⟨((-37378742211/137438953472), (-23047391787/137438953472)), (505/274877906944), by norm_num⟩
  | 3 => ⟨((81189033729/274877906944), (50060418261/274877906944)), (275/137438953472), by norm_num⟩
  | 4 => ⟨((-66130427429/274877906944), (-40775418857/274877906944)), (225/137438953472), by norm_num⟩
  | 5 => ⟨((43091863333/274877906944), (26570050203/274877906944)), (295/274877906944), by norm_num⟩
  | 6 => ⟨((-46799150247/549755813888), (-28855929527/549755813888)), (161/274877906944), by norm_num⟩
  | 7 => ⟨((43564614115/1099511627776), (26861544027/1099511627776)), (301/1099511627776), by norm_num⟩
  | 8 => ⟨((-35484429607/2199023255552), (-5469843975/549755813888)), (123/1099511627776), by norm_num⟩
  | 9 => ⟨((25691488279/4398046511104), (31682275055/8796093022208)), (179/4398046511104), by norm_num⟩
  | 10 => ⟨((-66964279215/35184372088832), (-41289564269/35184372088832)), (469/35184372088832), by norm_num⟩
  | 11 => ⟨((9917094831/17592186044416), (6114790291/17592186044416)), (279/70368744177664), by norm_num⟩
  | 12 => ⟨((-673142757/4398046511104), (-3320429513/35184372088832)), (19/17592186044416), by norm_num⟩
  | 13 => ⟨((43188462005/1125899906842624), (832175377/35184372088832)), (153/562949953421312), by norm_num⟩
  | 14 => ⟨((-40203479583/4503599627370496), (-24789099107/4503599627370496)), (143/2251799813685248), by norm_num⟩
  | 15 => ⟨((34929818039/18014398509481984), (43074814923/36028797018963968)), (499/36028797018963968), by norm_num⟩
  | 16 => ⟨((-56902359613/144115188075855872), (-4385684543/18014398509481984)), (51/18014398509481984), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (-3372543898119/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777627436452569/633825300114114700748351602688), (-3986385696441/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472114426851319/9903520314283042199192993792), (-2241790828561/19807040628566084398385987584)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888152304737237/2475880078570760549798248448), (-4762438495323/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769818310648389/154742504910672534362390528), (-2380450534421/77371252455336267181195264)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548266563793911/9671406556917033397649408), (-4461711742717/9671406556917033397649408)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157207802730245/75557863725914323419136), (-1951182667291/302231454903657293676544)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117872586691749/4722366482869645213696), (-6338284052175/75557863725914323419136)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((10126297174623/36893488147419103232), (-4751037083539/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619558985546503/590295810358705651712), (-3264164914139/295147905179352825856)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455278046099611/18446744073709551616), (-4076948504083/36893488147419103232)), (5967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819997741027543/9223372036854775808), (-2291045517533/2305843009213693952)), (6719/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795622241040785/576460752303423488), (-9153001650737/1152921504606846976)), (3363/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192180082333467/144115188075855872), (-7996311752039/144115188075855872)), (2947/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488032461500843/36028797018963968), (-1496171428757/4503599627370496)), (4429/18014398509481984), by norm_num⟩
  | 3 => ⟨((742372356300717/4503599627370496), (-14917870578125/9007199254740992)), (5551/4503599627370496), by norm_num⟩
  | 2 => ⟨((554725506748217/1125899906842624), (-14852254204949/2251799813685248)), (5573/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202485268585035/2251799813685248), (-44229724331829/2251799813685248)), (33663/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076651972416987/1125899906842624), (-87157550937445/2251799813685248)), (68229/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076651972416987/1125899906842624), (-87157550937445/2251799813685248)), (260272988326262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((513935720664287/562949953421312), (-166690393271257/2251799813685248)), (33943/562949953421312), by norm_num⟩
  | 2 => ⟨((1864416670998723/2251799813685248), (-304354399083013/2251799813685248)), (67001/562949953421312), by norm_num⟩
  | 3 => ⟨((1502539391954007/2251799813685248), (-125997749021371/562949953421312)), (516245/2251799813685248), by norm_num⟩
  | 4 => ⟨((889785001340417/2251799813685248), (-168146901915151/562949953421312)), (460015/1125899906842624), by norm_num⟩
  | 5 => ⟨((18837334949215/281474976710656), (-1063075610445875/4503599627370496)), (2553389/4503599627370496), by norm_num⟩
  | 6 => ⟨((-461537201967713/9007199254740992), (-569159264793773/18014398509481984)), (3094441/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-110724287087/1073741824)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-3052282179/1073741824), (-112006867533/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-420365928742413/9007199254740992), (157133878041885/4503599627370496)), (6027369/18014398509481984), by norm_num⟩
  | 1 => ⟨((42280808263/274877906944), (-1975584519/17179869184)), (305/274877906944), by norm_num⟩
  | 2 => ⟨((-69675323299/274877906944), (52089634317/274877906944)), (505/274877906944), by norm_num⟩
  | 3 => ⟨((38273083197/137438953472), (-57226312373/274877906944)), (557/274877906944), by norm_num⟩
  | 4 => ⟨((-7883864911/34359738368), (23576073753/137438953472)), (461/274877906944), by norm_num⟩
  | 5 => ⟨((41574292193/274877906944), (-7770289303/68719476736)), (153/137438953472), by norm_num⟩
  | 6 => ⟨((-5709253537/68719476736), (34146141259/549755813888)), (169/274877906944), by norm_num⟩
  | 7 => ⟨((43009756079/1099511627776), (-8038579371/274877906944)), (5/17179869184), by norm_num⟩
  | 8 => ⟨((-35438284921/2199023255552), (52987692483/4398046511104)), (529/4398046511104), by norm_num⟩
  | 9 => ⟨((51910580405/8796093022208), (-38808620073/8796093022208)), (389/8796093022208), by norm_num⟩
  | 10 => ⟨((-34217760927/17592186044416), (25581376151/17592186044416)), (515/35184372088832), by norm_num⟩
  | 11 => ⟨((41009511977/70368744177664), (-30658924583/70368744177664)), (311/70368744177664), by norm_num⟩
  | 12 => ⟨((-22526776905/140737488355328), (4210283913/35184372088832)), (43/35184372088832), by norm_num⟩
  | 13 => ⟨((45688973413/1125899906842624), (-17078657153/562949953421312)), (175/562949953421312), by norm_num⟩
  | 14 => ⟨((-43023829413/4503599627370496), (32164838781/4503599627370496)), (331/4503599627370496), by norm_num⟩
  | 15 => ⟨((37813206159/18014398509481984), (-56538699437/36028797018963968)), (73/4503599627370496), by norm_num⟩
  | 16 => ⟨((-62313079441/144115188075855872), (23292791245/72057594037927936)), (483/144115188075855872), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (1628020959609/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444394474464517/158456325028528675187087900672), (3848472009863/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888402022322445/39614081257132168796771975168), (4328457025571/39614081257132168796771975168)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118005824941857/154742504910672534362390528), (1149412700357/618970019642690137449562112)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769759272128281/154742504910672534362390528), (574518707501/19342813113834066795298816)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548211286479581/9671406556917033397649408), (538411982591/1208925819614629174706176)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257614125438639/604462909807314587353088), (941822503499/151115727451828646838272)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885883038890683/75557863725914323419136), (6118859012709/75557863725914323419136)), (4619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20251678029729/73786976294838206464), (1146632910495/1180591620717411303424)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809739269417615/295147905179352825856), (6302237819245/590295810358705651712)), (4769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113813244360001/4611686018427387904), (7871436541591/73786976294838206464)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909942660817035/4611686018427387904), (1105828335223/1152921504606846976)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591132548783723/1152921504606846976), (8835712263301/1152921504606846976)), (1681/288230376151711744), by norm_num⟩
  | 5 => ⟨((596041343178283/72057594037927936), (7718983069427/144115188075855872)), (1473/36028797018963968), by norm_num⟩
  | 4 => ⟨((743943727929783/18014398509481984), (11553978164409/36028797018963968)), (8853/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484565353392369/9007199254740992), (14399680122967/9007199254740992)), (1387/1125899906842624), by norm_num⟩
  | 2 => ⟨((2218548975256281/4503599627370496), (7167821751417/1125899906842624)), (22277/4503599627370496), by norm_num⟩
  | 1 => ⟨((550492440989613/562949953421312), (42687812096445/2251799813685248)), (1051/70368744177664), by norm_num⟩
  | 0 => ⟨((538082166756823/562949953421312), (84105529933543/2251799813685248)), (68137/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538082166756823/562949953421312), (84105529933543/2251799813685248)), (259922036177825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2054110193380011/2251799813685248), (160780493924305/2251799813685248)), (135345/2251799813685248), by norm_num⟩
  | 2 => ⟨((232787029614885/281474976710656), (73332640286103/562949953421312)), (133127/1125899906842624), by norm_num⟩
  | 3 => ⟨((187744511933689/281474976710656), (121295951103795/562949953421312)), (254883/1125899906842624), by norm_num⟩
  | 4 => ⟨((112158548484855/281474976710656), (40452351050239/140737488355328)), (899705/2251799813685248), by norm_num⟩
  | 5 => ⟨((342991437279493/4503599627370496), (1031611867937183/4503599627370496)), (1234213/2251799813685248), by norm_num⟩
  | 6 => ⟨((-420365928742413/9007199254740992), (157133878041885/4503599627370496)), (6027369/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-112006867533/1073741824)), (1/536870912), by norm_num⟩, -17, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile064Terms3
