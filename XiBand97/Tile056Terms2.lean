/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile056Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨56,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78161/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78161/2560))
  have he : value ((69/80), (78161/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-320962607/134217728), (-22723512985/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1624282369860183/18014398509481984), (-281025504050651/18014398509481984)), (35087761/18014398509481984), by norm_num⟩
  | 1 => ⟨((2147420397/8589934592), (2972290585/68719476736)), (373/68719476736), by norm_num⟩
  | 2 => ⟨((-23815654299/68719476736), (-2060234839/34359738368)), (519/68719476736), by norm_num⟩
  | 3 => ⟨((11005169087/34359738368), (3808122587/68719476736)), (241/34359738368), by norm_num⟩
  | 4 => ⟨((-15256403849/68719476736), (-1319794717/34359738368)), (21/4294967296), by norm_num⟩
  | 5 => ⟨((8459946651/68719476736), (1463699179/68719476736)), (375/137438953472), by norm_num⟩
  | 6 => ⟨((-1954662723/34359738368), (-1352745279/137438953472)), (87/68719476736), by norm_num⟩
  | 7 => ⟨((24774746613/1099511627776), (4286407205/1099511627776)), (277/549755813888), by norm_num⟩
  | 8 => ⟨((-4293136441/549755813888), (-2971111069/2199023255552)), (193/1099511627776), by norm_num⟩
  | 9 => ⟨((21161069653/8796093022208), (3661186241/8796093022208)), (239/4398046511104), by norm_num⟩
  | 10 => ⟨((-23468377229/35184372088832), (-4060385473/35184372088832)), (133/8796093022208), by norm_num⟩
  | 11 => ⟨((23661148377/140737488355328), (4093737807/140737488355328)), (539/140737488355328), by norm_num⟩
  | 12 => ⟨((-10933772191/281474976710656), (-945854273/140737488355328)), (125/140737488355328), by norm_num⟩
  | 13 => ⟨((9327647221/1125899906842624), (403456137/281474976710656)), (429/2251799813685248), by norm_num⟩
  | 14 => ⟨((-14778131137/9007199254740992), (-2556840995/9007199254740992)), (171/4503599627370496), by norm_num⟩
  | 15 => ⟨((5463157297/18014398509481984), (3780836537/72057594037927936)), (127/18014398509481984), by norm_num⟩
  | 16 => ⟨((-7573544155/144115188075855872), (-1310338093/144115188075855872)), (177/144115188075855872), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-3869112836105/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778269714575499/633825300114114700748351602688), (-4576500334571/633825300114114700748351602688)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889179947633469/39614081257132168796771975168), (-5147464177643/39614081257132168796771975168)), (6517/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944459640825239/1237940039285380274899124224), (-1366960855133/618970019642690137449562112)), (3463/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442646208485885/38685626227668133590597632), (-2733169566395/77371252455336267181195264)), (13857/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774492348795595/4835703278458516698824704), (-5123094919793/9671406556917033397649408)), (3249/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258290307321587/604462909807314587353088), (-4481110361477/604462909807314587353088)), (711/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943490399204165/37778931862957161709568), (-3639404675473/37778931862957161709568)), (289/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((324232451884087/1180591620717411303424), (-1364121772257/1180591620717411303424)), (1735/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810303943161175/295147905179352825856), (-1874603415823/147573952589676412928)), (9549/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911210694488499/36893488147419103232), (-9366635216829/73786976294838206464)), (23893/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910733978260953/4611686018427387904), (-5264346620167/4611686018427387904)), (26907/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99544462586941/72057594037927936), (-10517734545765/1152921504606846976)), (13471/576460752303423488), by norm_num⟩
  | 5 => ⟨((298364983294601/36028797018963968), (-1148837100897/18014398509481984)), (23613/144115188075855872), by norm_num⟩
  | 4 => ⟨((744972421157197/18014398509481984), (-6880711212373/18014398509481984)), (17749/18014398509481984), by norm_num⟩
  | 3 => ⟨((185890284099441/1125899906842624), (-17158731102897/9007199254740992)), (11127/2251799813685248), by norm_num⟩
  | 2 => ⟨((555904626216371/1125899906842624), (-17094246790829/2251799813685248)), (44713/2251799813685248), by norm_num⟩
  | 1 => ⟨((276182968342119/281474976710656), (-25480461513161/1125899906842624)), (67585/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083439077304825/1125899906842624), (-12579776885201/281474976710656)), (137237/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083439077304825/1125899906842624), (-12579776885201/281474976710656)), (523517612937545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((32510333915143/35184372088832), (-96842866960875/1125899906842624)), (276391/1125899906842624), by norm_num⟩
  | 2 => ⟨((952934969923079/1125899906842624), (-178965475595181/1125899906842624)), (279159/562949953421312), by norm_num⟩
  | 3 => ⟨((1556188805280261/2251799813685248), (-302944265413109/1125899906842624)), (2245175/2251799813685248), by norm_num⟩
  | 4 => ⟨((912435765118171/2251799813685248), (-418721479231483/1125899906842624)), (2155717/1125899906842624), by norm_num⟩
  | 5 => ⟨((58277079512149/2251799813685248), (-1357337187620511/4503599627370496)), (6700851/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1624282369860183/18014398509481984), (-281025504050651/18014398509481984)), (35087761/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-22723512985/268435456)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-23220378737/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((84979194840001/9007199254740992), (1555175730227381/18014398509481984)), (7642123/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1836884985/68719476736), (-16808107877/68719476736)), (83/17179869184), by norm_num⟩
  | 2 => ⟨((1301071763/34359738368), (23810477763/68719476736)), (59/8589934592), by norm_num⟩
  | 3 => ⟨((-153592245/4294967296), (-22486721109/68719476736)), (7/1073741824), by norm_num⟩
  | 4 => ⟨((217579799/8589934592), (7963709789/34359738368)), (319/68719476736), by norm_num⟩
  | 5 => ⟨((-61644999/4294967296), (-9025155537/68719476736)), (363/137438953472), by norm_num⟩
  | 6 => ⟨((232871245/34359738368), (17046794067/274877906944)), (345/274877906944), by norm_num⟩
  | 7 => ⟨((-3016109343/1099511627776), (-862450079/34359738368)), (561/1099511627776), by norm_num⟩
  | 8 => ⟨((2136320309/2199023255552), (4887010145/549755813888)), (25/137438953472), by norm_num⟩
  | 9 => ⟨((-2690067203/8796093022208), (-3076876079/1099511627776)), (505/8796093022208), by norm_num⟩
  | 10 => ⟨((1524306859/17592186044416), (27895828369/35184372088832)), (575/35184372088832), by norm_num⟩
  | 11 => ⟨((-3140862933/140737488355328), (-14369969669/70368744177664)), (595/140737488355328), by norm_num⟩
  | 12 => ⟨((2966244925/562949953421312), (27142126547/562949953421312)), (141/140737488355328), by norm_num⟩
  | 13 => ⟨((-2585847601/2251799813685248), (-5915341163/562949953421312)), (247/1125899906842624), by norm_num⟩
  | 14 => ⟨((2093216551/9007199254740992), (9576813439/4503599627370496)), (201/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1581474417/36028797018963968), (-28942032671/72057594037927936)), (305/36028797018963968), by norm_num⟩
  | 16 => ⟨((2240327211/288230376151711744), (5124934573/72057594037927936)), (217/144115188075855872), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (1904343547853/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778197657457369/633825300114114700748351602688), (281539876619/79228162514264337593543950336)), (11553/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944549687342487/19807040628566084398385987584), (633329870769/9903520314283042199192993792)), (12999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888834320582685/2475880078570760549798248448), (1345490447697/1237940039285380274899124224)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110656287554913/9671406556917033397649408), (2690226244359/154742504910672534362390528)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387226625510217/2417851639229258349412352), (630321387887/2417851639229258349412352)), (12955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629111329269497/302231454903657293676544), (2205323602271/604462909807314587353088)), (11339/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117929519744901/4722366482869645213696), (447768641409/9444732965739290427392)), (18429/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296849710278141/4722366482869645213696), (2685298472409/4722366482869645213696)), (6913/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810249902549897/295147905179352825856), (461269043275/73786976294838206464)), (19017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455572340467189/18446744073709551616), (1152373230337/18446744073709551616)), (23781/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821323646303909/9223372036854775808), (5181286317825/9223372036854775808)), (26767/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796286177979421/576460752303423488), (5175799830083/1152921504606846976)), (837/36028797018963968), by norm_num⟩
  | 5 => ⟨((1193344176802279/144115188075855872), (2261329735371/72057594037927936)), (733/4503599627370496), by norm_num⟩
  | 4 => ⟨((1489782988287209/36028797018963968), (6771675722723/36028797018963968)), (35221/36028797018963968), by norm_num⟩
  | 3 => ⟨((743470244925461/4503599627370496), (8443084884229/9007199254740992)), (22047/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223316218033459/4503599627370496), (4205448881759/1125899906842624)), (88389/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209162380750653/2251799813685248), (6268074833819/562949953421312)), (133091/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083438452123211/1125899906842624), (193383844085/8796093022208)), (134111/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083438452123211/1125899906842624), (193383844085/8796093022208)), (511592869285201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521017079254985/562949953421312), (1488725535389/35184372088832)), (66001/281474976710656), by norm_num⟩
  | 2 => ⟨((1924799328798679/2251799813685248), (176362716561173/2251799813685248)), (1022039/2251799813685248), by norm_num⟩
  | 3 => ⟨((1631472134433935/2251799813685248), (301503567412149/2251799813685248)), (1907337/2251799813685248), by norm_num⟩
  | 4 => ⟨((570831587392499/1125899906842624), (218445114737051/1125899906842624)), (3274569/2251799813685248), by norm_num⟩
  | 5 => ⟨((988117793854417/4503599627370496), (443006952378821/2251799813685248)), (9182135/4503599627370496), by norm_num⟩
  | 6 => ⟨((84979194840001/9007199254740992), (1555175730227381/18014398509481984)), (7642123/4503599627370496), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-23220378737/268435456)), (1/134217728), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-23688836229/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1429861436114343/18014398509481984), (-416117418333799/18014398509481984)), (14940947/18014398509481984), by norm_num⟩
  | 1 => ⟨((-15765499545/68719476736), (2294033115/34359738368)), (167/68719476736), by norm_num⟩
  | 2 => ⟨((22784077317/68719476736), (-6630608527/68719476736)), (243/68719476736), by norm_num⟩
  | 3 => ⟨((-2743935567/8589934592), (6388307875/68719476736)), (59/17179869184), by norm_num⟩
  | 4 => ⟨((15861987737/68719476736), (-2308073083/34359738368)), (43/17179869184), by norm_num⟩
  | 5 => ⟨((-2292352069/17179869184), (5336951403/137438953472)), (201/137438953472), by norm_num⟩
  | 6 => ⟨((4417166453/68719476736), (-642740567/34359738368)), (195/274877906944), by norm_num⟩
  | 7 => ⟨((-14591146475/549755813888), (4246306703/549755813888)), (163/549755813888), by norm_num⟩
  | 8 => ⟨((21086918843/2199023255552), (-6136702485/2199023255552)), (119/1099511627776), by norm_num⟩
  | 9 => ⟨((-6772114965/2199023255552), (1970816839/2199023255552)), (77/2199023255552), by norm_num⟩
  | 10 => ⟨((15659143869/17592186044416), (-4557114665/17592186044416)), (45/4398046511104), by norm_num⟩
  | 11 => ⟨((-4114613381/17592186044416), (2394864641/35184372088832)), (191/70368744177664), by norm_num⟩
  | 12 => ⟨((15857016415/281474976710656), (-4614699415/281474976710656)), (93/140737488355328), by norm_num⟩
  | 13 => ⟨((-7051180371/562949953421312), (1026015143/281474976710656)), (167/1125899906842624), by norm_num⟩
  | 14 => ⟨((11646018631/4503599627370496), (-3389217363/4503599627370496)), (139/4503599627370496), by norm_num⟩
  | 15 => ⟨((-17952705783/36028797018963968), (5224585679/36028797018963968)), (27/4503599627370496), by norm_num⟩
  | 16 => ⟨((25944996887/288230376151711744), (-7550497447/288230376151711744)), (315/288230376151711744), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-368896343679/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778124325383375/633825300114114700748351602688), (-436268239111/633825300114114700748351602688)), (11531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889017039160451/39614081257132168796771975168), (-122674009857/9903520314283042199192993792)), (12973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888747053885767/2475880078570760549798248448), (-521232027831/2475880078570760549798248448)), (1723/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770413575592151/154742504910672534362390528), (-260541510151/77371252455336267181195264)), (1723/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193603146518959/1208925819614629174706176), (-488357071079/9671406556917033397649408)), (3231/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258151750998169/604462909807314587353088), (-427154244323/604462909807314587353088)), (11309/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378785470217/37778931862957161709568), (-346914589465/37778931862957161709568)), (18377/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324191017728579/1180591620717411303424), (-520112618073/4722366482869645213696)), (1723/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620382731636795/590295810358705651712), (-89341726401/73786976294838206464)), (9477/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822144039611317/73786976294838206464), (-446393088061/36893488147419103232)), (11847/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821161558366637/9223372036854775808), (-501758732757/4611686018427387904)), (13329/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99525750879181/72057594037927936), (-501217440469/576460752303423488)), (13331/576460752303423488), by norm_num⟩
  | 5 => ⟨((596602918600611/72057594037927936), (-875914183927/144115188075855872)), (23333/144115188075855872), by norm_num⟩
  | 4 => ⟨((93098711634421/2251799813685248), (-1311442523489/36028797018963968)), (17503/18014398509481984), by norm_num⟩
  | 3 => ⟨((185836599788581/1125899906842624), (-817530822831/4503599627370496)), (43771/9007199254740992), by norm_num⟩
  | 2 => ⟨((277855145287989/562949953421312), (-1628716960905/2251799813685248)), (43791/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104250122921075/1125899906842624), (-303409385517/140737488355328)), (32869/562949953421312), by norm_num⟩
  | 0 => ⟨((1082876111076719/1125899906842624), (-9583431032433/2251799813685248)), (65843/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082876111076719/1125899906842624), (-9583431032433/2251799813685248)), (251171114208030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2082951964515889/2251799813685248), (-2304305308159/281474976710656)), (508859/2251799813685248), by norm_num⟩
  | 2 => ⟨((1926614005137315/2251799813685248), (-34104326605261/2251799813685248)), (949739/2251799813685248), by norm_num⟩
  | 3 => ⟨((1647872247411385/2251799813685248), (-29179269344525/1125899906842624)), (413485/562949953421312), by norm_num⟩
  | 4 => ⟨((1204404231791901/2251799813685248), (-85413823840569/2251799813685248)), (2506443/2251799813685248), by norm_num⟩
  | 5 => ⟨((320475653182755/1125899906842624), (-45684687538343/1125899906842624)), (2871353/2251799813685248), by norm_num⟩
  | 6 => ⟨((1429861436114343/18014398509481984), (-416117418333799/18014398509481984)), (14940947/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-23688836229/268435456)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-681712945/268435456), (-12065979501/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-126225395614141/4503599627370496), (-1328627892270731/18014398509481984)), (31327223/18014398509481984), by norm_num⟩
  | 1 => ⟨((2835563469/34359738368), (3730834727/17179869184)), (177/34359738368), by norm_num⟩
  | 2 => ⟨((-4174571803/34359738368), (-10985215195/34359738368)), (523/68719476736), by norm_num⟩
  | 3 => ⟨((8194514625/68719476736), (21563530543/68719476736)), (515/68719476736), by norm_num⟩
  | 4 => ⟨((-6032062069/68719476736), (-15873124965/68719476736)), (381/68719476736), by norm_num⟩
  | 5 => ⟨((444025967/8589934592), (18694979147/137438953472)), (451/137438953472), by norm_num⟩
  | 6 => ⟨((-435802455/17179869184), (-4587185443/68719476736)), (445/274877906944), by norm_num⟩
  | 7 => ⟨((2933014253/274877906944), (7718107213/274877906944)), (47/68719476736), by norm_num⟩
  | 8 => ⟨((-8636081493/2199023255552), (-22725495723/2199023255552)), (139/549755813888), by norm_num⟩
  | 9 => ⟨((5650758883/4398046511104), (7434870603/2199023255552)), (183/2199023255552), by norm_num⟩
  | 10 => ⟨((-6655325887/17592186044416), (-17513218247/17592186044416)), (433/17592186044416), by norm_num⟩
  | 11 => ⟨((3562945629/35184372088832), (9375745901/35184372088832)), (233/35184372088832), by norm_num⟩
  | 12 => ⟨((-6993917327/281474976710656), (-18404207793/281474976710656)), (459/281474976710656), by norm_num⟩
  | 13 => ⟨((6336357783/1125899906842624), (8336933355/562949953421312)), (209/562949953421312), by norm_num⟩
  | 14 => ⟨((-1332644203/1125899906842624), (-3506798791/1125899906842624)), (353/4503599627370496), by norm_num⟩
  | 15 => ⟨((8370964345/36028797018963968), (11013925389/18014398509481984)), (139/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1540487107/36028797018963968), (-8107457807/72057594037927936)), (411/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (-2519196811987/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889023916909825/316912650057057350374175801344), (-2979050709617/633825300114114700748351602688)), (11563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944465373687485/19807040628566084398385987584), (-837672144459/9903520314283042199192993792)), (6505/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888655049514791/2475880078570760549798248448), (-1779591917983/1237940039285380274899124224)), (6913/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442580303089553/38685626227668133590597632), (-1779073032091/77371252455336267181195264)), (13829/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548738200635297/9671406556917033397649408), (-833664912265/2417851639229258349412352)), (1621/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258075270282793/604462909807314587353088), (-1458362648195/302231454903657293676544)), (5675/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943316288407709/37778931862957161709568), (-2368806689123/37778931862957161709568)), (9225/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296669702212501/4722366482869645213696), (-1775701893105/2361183241434822606848)), (13843/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405062990874131/147573952589676412928), (-2440123302333/295147905179352825856)), (19043/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821979065077367/73786976294838206464), (-6095910566547/73786976294838206464)), (2977/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820973883675193/9223372036854775808), (-3425928485419/4611686018427387904)), (26811/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796110873647439/576460752303423488), (-6844310556003/1152921504606846976)), (13417/576460752303423488), by norm_num⟩
  | 5 => ⟨((149129555713653/18014398509481984), (-5980291097077/144115188075855872)), (23505/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489319502800593/36028797018963968), (-4476749021341/18014398509481984)), (8827/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486357845862847/9007199254740992), (-5581140485807/4503599627370496)), (44223/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222141141847991/4503599627370496), (-5558997713597/1125899906842624)), (44357/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103687775523531/1125899906842624), (-517707348265/35184372088832)), (66871/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163207905487671/2251799813685248), (-16346984609293/562949953421312)), (270179/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163207905487671/2251799813685248), (-16346984609293/562949953421312)), (1030651101119231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2076202703036897/2251799813685248), (-125630799408711/2251799813685248)), (534791/2251799813685248), by norm_num⟩
  | 2 => ⟨((1907289689001621/2251799813685248), (-231668022824973/2251799813685248)), (1045849/2251799813685248), by norm_num⟩
  | 3 => ⟨((1591652980513677/2251799813685248), (-392448767887877/2251799813685248)), (31045/35184372088832), by norm_num⟩
  | 4 => ⟨((1056640630530729/2251799813685248), (-277396883733365/1125899906842624)), (3501353/2251799813685248), by norm_num⟩
  | 5 => ⟨((359131967572623/2251799813685248), (-1041331707566265/4503599627370496)), (10022563/4503599627370496), by norm_num⟩
  | 6 => ⟨((-126225395614141/4503599627370496), (-1328627892270731/18014398509481984)), (31327223/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-12065979501/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-693588655/268435456), (-767260853/8388608)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1273399617957389/18014398509481984), (477036251602427/18014398509481984)), (15100491/9007199254740992), by norm_num⟩
  | 1 => ⟨((14552171069/68719476736), (-5451480463/68719476736)), (347/68719476736), by norm_num⟩
  | 2 => ⟨((-21797204261/68719476736), (8165587981/68719476736)), (261/34359738368), by norm_num⟩
  | 3 => ⟨((21766196093/68719476736), (-1019246477/8589934592)), (131/17179869184), by norm_num⟩
  | 4 => ⟨((-16301424027/68719476736), (1526694783/17179869184)), (197/34359738368), by norm_num⟩
  | 5 => ⟨((19533880825/137438953472), (-7317710133/137438953472)), (237/68719476736), by norm_num⟩
  | 6 => ⟨((-19506092405/274877906944), (3653650069/137438953472)), (475/274877906944), by norm_num⟩
  | 7 => ⟨((8347861507/274877906944), (-6254489959/549755813888)), (51/68719476736), by norm_num⟩
  | 8 => ⟨((-6251989533/549755813888), (1171048589/274877906944)), (307/1099511627776), by norm_num⟩
  | 9 => ⟨((16648254949/4398046511104), (-97448557/68719476736)), (205/2199023255552), by norm_num⟩
  | 10 => ⟨((-4987371465/4398046511104), (7473402553/17592186044416)), (493/17592186044416), by norm_num⟩
  | 11 => ⟨((10866057933/35184372088832), (-1017650601/8796093022208)), (539/70368744177664), by norm_num⟩
  | 12 => ⟨((-21701200291/281474976710656), (4064811665/140737488355328)), (135/70368744177664), by norm_num⟩
  | 13 => ⟨((10001690167/562949953421312), (-3746796151/562949953421312)), (125/281474976710656), by norm_num⟩
  | 14 => ⟨((-8560681721/2251799813685248), (6413941801/4503599627370496)), (215/2251799813685248), by norm_num⟩
  | 15 => ⟨((1709700701/2251799813685248), (-1280963497/4503599627370496)), (345/18014398509481984), by norm_num⟩
  | 16 => ⟨((-20007053/140737488355328), (3837423689/72057594037927936)), (519/144115188075855872), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (1812687292587/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222246824131513/79228162514264337593543950336), (4286836788541/633825300114114700748351602688)), (11579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888848089160441/39614081257132168796771975168), (2410795190935/19807040628566084398385987584)), (13029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888566872989035/2475880078570760549798248448), (5121587254787/2475880078570760549798248448)), (13847/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770232640068455/154742504910672534362390528), (5120065959081/154742504910672534362390528)), (3463/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548654743964515/9671406556917033397649408), (4798445855425/9671406556917033397649408)), (12991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314500456485131/151115727451828646838272), (16394627291/2361183241434822606848)), (2843/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117907027722145/4722366482869645213696), (3408568382629/37778931862957161709568)), (2311/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648289457586585/2361183241434822606848), (1277550963459/1180591620717411303424)), (6937/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620126016356425/590295810358705651712), (3511113949769/295147905179352825856)), (1193/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821819961448757/73786976294838206464), (8771334374469/73786976294838206464)), (2985/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820792600695637/9223372036854775808), (9858886771227/9223372036854775808)), (13445/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796018803364157/576460752303423488), (2461953457273/288230376151711744)), (13461/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192872117072709/144115188075855872), (268887201115/4503599627370496)), (11797/72057594037927936), by norm_num⟩
  | 4 => ⟨((744533310694195/18014398509481984), (25159606095/70368744177664)), (35463/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486030615548485/9007199254740992), (8029344292423/4503599627370496)), (44457/9007199254740992), by norm_num⟩
  | 2 => ⟨((555363375015889/1125899906842624), (7996808351739/1125899906842624)), (22325/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103130924445345/1125899906842624), (23828155438661/1125899906842624)), (527/8796093022208), by norm_num⟩
  | 0 => ⟨((540163951310575/562949953421312), (47009694991773/1125899906842624)), (136853/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540163951310575/562949953421312), (47009694991773/1125899906842624)), (522052769187545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((129329709803571/140737488355328), (180427709016307/2251799813685248)), (34257/140737488355328), by norm_num⟩
  | 2 => ⟨((943544430213129/1125899906842624), (165802754619919/1125899906842624)), (273801/562949953421312), by norm_num⟩
  | 3 => ⟨((766307495988863/1125899906842624), (138948644266551/562949953421312)), (1079103/1125899906842624), by norm_num⟩
  | 4 => ⟨((452971238682195/1125899906842624), (47285458952361/140737488355328)), (4003215/2251799813685248), by norm_num⟩
  | 5 => ⟨((110284060745541/2251799813685248), (1217526512011037/4503599627370496)), (5911169/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1273399617957389/18014398509481984), (477036251602427/18014398509481984)), (15100491/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-767260853/8388608)), (1/134217728), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-352442413/134217728), (-24952220497/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((356900624963113/18014398509481984), (1253983444299131/18014398509481984)), (24021525/18014398509481984), by norm_num⟩
  | 1 => ⟨((-4145019381/68719476736), (-7281838861/34359738368)), (281/68719476736), by norm_num⟩
  | 2 => ⟨((6309802255/68719476736), (2771215225/8589934592)), (215/34359738368), by norm_num⟩
  | 3 => ⟨((-400215303/4294967296), (-11249369243/34359738368)), (219/34359738368), by norm_num⟩
  | 4 => ⟨((609232235/8589934592), (17124478535/68719476736)), (335/68719476736), by norm_num⟩
  | 5 => ⟨((-2967713935/68719476736), (-10427171827/68719476736)), (205/68719476736), by norm_num⟩
  | 6 => ⟨((6023514443/274877906944), (5290959765/68719476736)), (209/137438953472), by norm_num⟩
  | 7 => ⟨((-5239635679/549755813888), (-18409652253/549755813888)), (183/274877906944), by norm_num⟩
  | 8 => ⟨((1994023549/549755813888), (14012149839/1099511627776)), (35/137438953472), by norm_num⟩
  | 9 => ⟨((-2698155305/2199023255552), (-18960135371/4398046511104)), (381/4398046511104), by norm_num⟩
  | 10 => ⟨((6571675493/17592186044416), (1443113939/1099511627776)), (233/8796093022208), by norm_num⟩
  | 11 => ⟨((-7275495815/70368744177664), (-6390680389/17592186044416)), (259/35184372088832), by norm_num⟩
  | 12 => ⟨((7383470085/281474976710656), (6485523279/70368744177664)), (33/17592186044416), by norm_num⟩
  | 13 => ⟨((-6916658567/1125899906842624), (-24301933715/1125899906842624)), (497/1125899906842624), by norm_num⟩
  | 14 => ⟨((376034325/281474976710656), (10569683211/2251799813685248)), (435/4503599627370496), by norm_num⟩
  | 15 => ⟨((-4884671743/18014398509481984), (-8581236719/9007199254740992)), (355/18014398509481984), by norm_num⟩
  | 16 => ⟨((7435746361/144115188075855872), (13062883867/72057594037927936)), (543/144115188075855872), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (421236818251/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777917503170437/633825300114114700748351602688), (1992233277197/633825300114114700748351602688)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472196076003147/9903520314283042199192993792), (280094110985/4951760157141521099596496896)), (3249/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472124922032679/618970019642690137449562112), (2380162306797/2475880078570760549798248448)), (6905/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770166114753105/154742504910672534362390528), (594861321305/38685626227668133590597632)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548593076701431/9671406556917033397649408), (2229968400733/9671406556917033397649408)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257948566692979/604462909807314587353088), (975230556481/302231454903657293676544)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886427207740837/75557863725914323419136), (3168072660139/75557863725914323419136)), (9211/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296516133669169/4722366482869645213696), (296850856203/590295810358705651712)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((12656574613727/4611686018427387904), (3263333253413/590295810358705651712)), (297/9223372036854775808), by norm_num⟩
  | 8 => ⟨((227714645386863/9223372036854775808), (4076129521517/73786976294838206464)), (23769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227585096686513/1152921504606846976), (2290736675023/4611686018427387904)), (26751/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397982636337601/288230376151711744), (2288131628329/576460752303423488)), (26767/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192783785702589/144115188075855872), (3998376355159/144115188075855872)), (11719/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488944783518415/36028797018963968), (2992937461443/18014398509481984)), (35191/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485896892106149/9007199254740992), (7461928126899/9007199254740992)), (2753/562949953421312), by norm_num⟩
  | 2 => ⟨((2221241456969043/4503599627370496), (7431387262683/2251799813685248)), (88275/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103040592389803/1125899906842624), (345969266455/35184372088832)), (66431/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160837454940205/2251799813685248), (43678993547365/2251799813685248)), (267537/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160837454940205/2251799813685248), (43678993547365/2251799813685248)), (1020572670943450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2072702299658125/2251799813685248), (83829126086277/2251799813685248)), (523839/2251799813685248), by norm_num⟩
  | 2 => ⟨((952364298673667/1125899906842624), (154323507233085/2251799813685248)), (501677/1125899906842624), by norm_num⟩
  | 3 => ⟨((1600575354329347/2251799813685248), (65268767606107/562949953421312)), (1834941/2251799813685248), by norm_num⟩
  | 4 => ⟨((553708472958857/1125899906842624), (185571701716797/1125899906842624)), (3034035/2251799813685248), by norm_num⟩
  | 5 => ⟨((966893113301955/4503599627370496), (182525325666177/1125899906842624)), (7968745/4503599627370496), by norm_num⟩
  | 6 => ⟨((356900624963113/18014398509481984), (1253983444299131/18014398509481984)), (24021525/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-24952220497/268435456)), (1/134217728), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨56,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile056Terms2
