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
namespace Reinmann.XiBand97.Tile051Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨51,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76371/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76371/2560))
  have he : value ((69/80), (76371/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-17595549687/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1233414693284169/9007199254740992), (-558096668075139/9007199254740992)), (7510461/2251799813685248), by norm_num⟩
  | 1 => ⟨((2584542349/8589934592), (4677824843/34359738368)), (253/34359738368), by norm_num⟩
  | 2 => ⟨((-22715279881/68719476736), (-10278231713/68719476736)), (559/68719476736), by norm_num⟩
  | 3 => ⟨((8318428539/34359738368), (3763930555/34359738368)), (103/17179869184), by norm_num⟩
  | 4 => ⟨((-9138727815/68719476736), (-8270200723/137438953472)), (455/137438953472), by norm_num⟩
  | 5 => ⟨((250997967/4294967296), (7268595315/274877906944)), (201/137438953472), by norm_num⟩
  | 6 => ⟨((-2941327477/137438953472), (-1330894689/137438953472)), (37/68719476736), by norm_num⟩
  | 7 => ⟨((14772016051/2199023255552), (6684056047/2199023255552)), (187/1099511627776), by norm_num⟩
  | 8 => ⟨((-8114359181/4398046511104), (-7343186111/8796093022208)), (413/8796093022208), by norm_num⟩
  | 9 => ⟨((3962015427/8796093022208), (3585473111/17592186044416)), (405/35184372088832), by norm_num⟩
  | 10 => ⟨((-13928700275/140737488355328), (-6302471713/140737488355328)), (179/70368744177664), by norm_num⟩
  | 11 => ⟨((5564451377/281474976710656), (5035616635/562949953421312)), (575/1125899906842624), by norm_num⟩
  | 12 => ⟨((-4075449775/1125899906842624), (-7376253755/4503599627370496)), (423/4503599627370496), by norm_num⟩
  | 13 => ⟨((22042285315/36028797018963968), (9973714485/36028797018963968)), (575/36028797018963968), by norm_num⟩
  | 14 => ⟨((-3459417931/36028797018963968), (-6261283027/144115188075855872)), (363/144115188075855872), by norm_num⟩
  | 15 => ⟨((2026964827/144115188075855872), (7337303975/1152921504606846976)), (107/288230376151711744), by norm_num⟩
  | 16 => ⟨((-17814787741/9223372036854775808), (-8060852313/9223372036854775808)), (473/9223372036854775808), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-442346965947/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889518235320899/316912650057057350374175801344), (-4189197825307/633825300114114700748351602688)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890042475779769/39614081257132168796771975168), (-147251261267/1237940039285380274899124224)), (3257/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889835651011495/2475880078570760549798248448), (-5005572266237/2475880078570760549798248448)), (6923/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442875281976463/38685626227668133590597632), (-5004480322563/154742504910672534362390528)), (6925/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549843642906113/9671406556917033397649408), (-2345270110557/4835703278458516698824704)), (12989/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259041804013237/604462909807314587353088), (-4103062734343/604462909807314587353088)), (5685/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118012614330055/4722366482869645213696), (-6665302279845/75557863725914323419136)), (18485/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297845447955349/4722366482869645213696), (-4997074139629/4722366482869645213696)), (867/295147905179352825856), by norm_num⟩
  | 9 => ⟨((101366667217021/36893488147419103232), (-3433942877057/295147905179352825856)), (19085/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823994549497861/73786976294838206464), (-8580221267747/73786976294838206464)), (11937/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823237311900501/9223372036854775808), (-4823187962435/4611686018427387904)), (6721/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594480190908981/1152921504606846976), (-9638411771315/1152921504606846976)), (26915/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195006983159531/144115188075855872), (-8424653520269/144115188075855872)), (23587/144115188075855872), by norm_num⟩
  | 4 => ⟨((746132062494751/18014398509481984), (-1577384247307/4503599627370496)), (17725/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490019090852863/9007199254740992), (-15742522840891/9007199254740992)), (22219/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114702595244931/2251799813685248), (-15695576352769/2251799813685248)), (44625/2251799813685248), by norm_num⟩
  | 1 => ⟨((34658219839295/35184372088832), (-23426114421229/1125899906842624)), (67407/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092065009547385/1125899906842624), (-23191965536393/562949953421312)), (136697/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092065009547385/1125899906842624), (-23191965536393/562949953421312)), (521457676414107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057336010759937/1125899906842624), (-22495013909317/281474976710656)), (138221/562949953421312), by norm_num⟩
  | 2 => ⟨((61609774461971/70368744177664), (-2640641957193/17592186044416)), (281701/562949953421312), by norm_num⟩
  | 3 => ⟨((837689292465603/1125899906842624), (-295930213574099/1125899906842624)), (577843/562949953421312), by norm_num⟩
  | 4 => ⟨((545473585771737/1125899906842624), (-220177273060857/562949953421312)), (581805/281474976710656), by norm_num⟩
  | 5 => ⟨((46020656834063/562949953421312), (-426684062808919/1125899906842624)), (16301549/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1233414693284169/9007199254740992), (-558096668075139/9007199254740992)), (7510461/2251799813685248), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-17595549687/268435456)), (1/134217728), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-18439285101/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1127069017824937/9007199254740992), (507851478610231/9007199254740992)), (13751921/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4949898375/17179869184), (-8921594575/68719476736)), (61/17179869184), by norm_num⟩
  | 2 => ⟨((5698781105/17179869184), (10271365337/68719476736)), (283/68719476736), by norm_num⟩
  | 3 => ⟨((-17495904561/68719476736), (-1970891059/17179869184)), (55/17179869184), by norm_num⟩
  | 4 => ⟨((20142904515/137438953472), (9076288745/137438953472)), (1/536870912), by norm_num⟩
  | 5 => ⟨((-9276150333/137438953472), (-8359570865/274877906944)), (119/137438953472), by norm_num⟩
  | 6 => ⟨((14239416985/549755813888), (802025969/68719476736)), (185/549755813888), by norm_num⟩
  | 7 => ⟨((-18735696733/2199023255552), (-8442208185/2199023255552)), (123/1099511627776), by norm_num⟩
  | 8 => ⟨((10785134001/4398046511104), (9719451359/8796093022208)), (143/4398046511104), by norm_num⟩
  | 9 => ⟨((-22074390023/35184372088832), (-4973303069/17592186044416)), (295/35184372088832), by norm_num⟩
  | 10 => ⟨((20331264561/140737488355328), (1145145351/17592186044416)), (137/70368744177664), by norm_num⟩
  | 11 => ⟨((-4255860609/140737488355328), (-3835337621/281474976710656)), (231/562949953421312), by norm_num⟩
  | 12 => ⟨((816623433/140737488355328), (2943730411/1125899906842624)), (179/2251799813685248), by norm_num⟩
  | 13 => ⟨((-4628541399/4503599627370496), (-8342387399/18014398509481984)), (1/70368744177664), by norm_num⟩
  | 14 => ⟨((12180126203/72057594037927936), (5488301961/72057594037927936)), (85/36028797018963968), by norm_num⟩
  | 15 => ⟨((-14957747747/576460752303423488), (-6739883883/576460752303423488)), (211/576460752303423488), by norm_num⟩
  | 16 => ⟨((17220743493/4611686018427387904), (7759578079/4611686018427387904)), (245/4611686018427387904), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (551458664449/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778905511980971/633825300114114700748351602688), (652718129499/633825300114114700748351602688)), (5767/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472473923944493/9903520314283042199192993792), (45886270909/2475880078570760549798248448)), (811/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889680404047051/2475880078570760549798248448), (97488574961/309485009821345068724781056)), (3447/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771346675553341/154742504910672534362390528), (779730905517/154742504910672534362390528)), (13789/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549699687620611/9671406556917033397649408), (730808980333/9671406556917033397649408)), (12927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258916686393383/604462909807314587353088), (639269177739/604462909807314587353088)), (11313/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472000023276141/18889465931478580854784), (519229386847/37778931862957161709568)), (18383/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40552985223061/147573952589676412928), (778534780059/4722366482869645213696)), (13789/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621662776836167/590295810358705651712), (1069982962557/590295810358705651712)), (18961/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823743036175851/73786976294838206464), (668362802671/36893488147419103232)), (2963/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911479486636425/4611686018427387904), (1502781514529/9223372036854775808)), (26671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594207610457353/1152921504606846976), (750744550727/576460752303423488)), (6669/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194774940644305/144115188075855872), (1312350477593/144115188075855872)), (23347/144115188075855872), by norm_num⟩
  | 4 => ⟨((93245560036853/2251799813685248), (491406109081/9007199254740992)), (4379/4503599627370496), by norm_num⟩
  | 3 => ⟨((1489622638726749/9007199254740992), (2451961601855/9007199254740992)), (43809/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114339757350179/2251799813685248), (4888749503951/4503599627370496)), (21919/1125899906842624), by norm_num⟩
  | 1 => ⟨((554301160860727/562949953421312), (911913214485/281474976710656)), (65831/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182949630213097/2251799813685248), (14440029541605/2251799813685248)), (263923/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182949630213097/2251799813685248), (14440029541605/2251799813685248)), (1006786355025481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1058055992507597/1125899906842624), (1749814579239/140737488355328)), (128773/562949953421312), by norm_num⟩
  | 2 => ⟨((1988252273600619/2251799813685248), (1644375126145/70368744177664)), (980917/2251799813685248), by norm_num⟩
  | 3 => ⟨((438580087653097/562949953421312), (92922862882293/2251799813685248)), (1778069/2251799813685248), by norm_num⟩
  | 4 => ⟨((1362912109448957/2251799813685248), (144787710169299/2251799813685248)), (1458623/1125899906842624), by norm_num⟩
  | 5 => ⟨((407799557914709/1125899906842624), (350533688278751/4503599627370496)), (7813007/4503599627370496), by norm_num⟩
  | 6 => ⟨((1127069017824937/9007199254740992), (507851478610231/9007199254740992)), (13751921/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-18439285101/268435456)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-1200158539/16777216)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-854832166843635/9007199254740992), (-752180701687067/9007199254740992)), (12945509/4503599627370496), by norm_num⟩
  | 1 => ⟨((7819358871/34359738368), (6880380817/34359738368)), (119/17179869184), by norm_num⟩
  | 2 => ⟨((-9375001837/34359738368), (-4124608159/17179869184)), (287/34359738368), by norm_num⟩
  | 3 => ⟨((1873356049/8589934592), (13187171209/68719476736)), (461/68719476736), by norm_num⟩
  | 4 => ⟨((-17968446457/137438953472), (-1976340969/17179869184)), (555/137438953472), by norm_num⟩
  | 5 => ⟨((2154322641/34359738368), (15164987735/274877906944)), (535/274877906944), by norm_num⟩
  | 6 => ⟨((-13775573539/549755813888), (-12121350801/549755813888)), (215/274877906944), by norm_num⟩
  | 7 => ⟨((2359455905/274877906944), (8304494225/1099511627776)), (297/1099511627776), by norm_num⟩
  | 8 => ⟨((-5657728161/2199023255552), (-9956653723/4398046511104)), (179/2199023255552), by norm_num⟩
  | 9 => ⟨((12059235211/17592186044416), (5305558421/8796093022208)), (3/137438953472), by norm_num⟩
  | 10 => ⟨((-11566713243/70368744177664), (-5088869383/35184372088832)), (185/35184372088832), by norm_num⟩
  | 11 => ⟨((10085733457/281474976710656), (8874600609/281474976710656)), (81/70368744177664), by norm_num⟩
  | 12 => ⟨((-2015377715/281474976710656), (-7093454283/1125899906842624)), (521/2251799813685248), by norm_num⟩
  | 13 => ⟨((2973947505/2251799813685248), (10467298765/9007199254740992)), (193/4503599627370496), by norm_num⟩
  | 14 => ⟨((-127343119/562949953421312), (-14342563559/72057594037927936)), (531/72057594037927936), by norm_num⟩
  | 15 => ⟨((5211399903/144115188075855872), (4585595381/144115188075855872)), (171/144115188075855872), by norm_num⟩
  | 16 => ⟨((-1562048899/288230376151711744), (-10995777487/2305843009213693952)), (103/576460752303423488), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-1576150335607/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222346444403697/79228162514264337593543950336), (-1865311785315/316912650057057350374175801344)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889744612124187/39614081257132168796771975168), (-1049044161479/9903520314283042199192993792)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944759689164175/1237940039285380274899124224), (-4457495283333/2475880078570760549798248448)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771185088537663/154742504910672534362390528), (-4456435207541/154742504910672534362390528)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549547603806919/9671406556917033397649408), (-4176781872289/9671406556917033397649408)), (12981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314695754377591/151115727451828646838272), (-1826779111699/302231454903657293676544)), (11363/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887781765456347/75557863725914323419136), (-5934921490145/75557863725914323419136)), (18471/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297530806087637/4722366482869645213696), (-1112336197553/1180591620717411303424)), (13861/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621434702258507/590295810358705651712), (-6114849681619/590295810358705651712)), (19069/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823455571317407/73786976294838206464), (-1909766132543/18446744073709551616)), (5963/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455658079820435/2305843009213693952), (-4293882965769/4611686018427387904)), (3357/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199234611736167/144115188075855872), (-8580042596995/1152921504606846976)), (6721/288230376151711744), by norm_num⟩
  | 5 => ⟨((597240501743475/72057594037927936), (-7498853675817/144115188075855872)), (23555/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491478960094677/36028797018963968), (-1403865777167/4503599627370496)), (8849/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489044279697735/9007199254740992), (-3502079199289/2251799813685248)), (11089/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113737725301389/2251799813685248), (-3490715872433/562949953421312)), (44523/2251799813685248), by norm_num⟩
  | 1 => ⟨((276910122776165/281474976710656), (-20830865801241/1125899906842624)), (67203/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089318415111385/1125899906842624), (-20604619609893/562949953421312)), (136085/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089318415111385/1125899906842624), (-20604619609893/562949953421312)), (519123081687545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((526208591413149/562949953421312), (-19935157149417/281474976710656)), (136645/562949953421312), by norm_num⟩
  | 2 => ⟨((978082822608153/1125899906842624), (-74536295096511/562949953421312)), (549619/1125899906842624), by norm_num⟩
  | 3 => ⟨((1659869345499265/2251799813685248), (-259002312556155/1125899906842624)), (2200929/2251799813685248), by norm_num⟩
  | 4 => ⟨((552188839651005/1125899906842624), (-763673567095291/2251799813685248)), (1064337/562949953421312), by norm_num⟩
  | 5 => ⟨((70660448765519/562949953421312), (-1498151010844469/4503599627370496)), (3531817/1125899906842624), by norm_num⟩
  | 6 => ⟨((-854832166843635/9007199254740992), (-752180701687067/9007199254740992)), (12945509/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1200158539/16777216)), (1/134217728), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-575319455/268435456), (-1243708167/16777216)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((315549279946833/9007199254740992), (1008088722530735/9007199254740992)), (19113033/9007199254740992), by norm_num⟩
  | 1 => ⟨((-747786049/8589934592), (-9555840951/34359738368)), (365/68719476736), by norm_num⟩
  | 2 => ⟨((7432714103/68719476736), (5936343181/17179869184)), (57/8589934592), by norm_num⟩
  | 3 => ⟨((-6156533567/68719476736), (-19668344861/68719476736)), (95/17179869184), by norm_num⟩
  | 4 => ⟨((239037675/4294967296), (6109250117/34359738368)), (237/68719476736), by norm_num⟩
  | 5 => ⟨((-950378093/34359738368), (-12144732993/137438953472)), (237/137438953472), by norm_num⟩
  | 6 => ⟨((787200281/68719476736), (5029754629/137438953472)), (395/549755813888), by norm_num⟩
  | 7 => ⟨((-2235564815/549755813888), (-7141983271/549755813888)), (141/549755813888), by norm_num⟩
  | 8 => ⟨((5555169875/4398046511104), (17747161723/4398046511104)), (11/137438953472), by norm_num⟩
  | 9 => ⟨((-1533786507/4398046511104), (-9800008929/8796093022208)), (391/17592186044416), by norm_num⟩
  | 10 => ⟨((6098106065/70368744177664), (19481685885/70368744177664)), (391/70368744177664), by norm_num⟩
  | 11 => ⟨((-2755131693/140737488355328), (-17603698475/281474976710656)), (89/70368744177664), by norm_num⟩
  | 12 => ⟨((4564163377/1125899906842624), (14581182467/1125899906842624)), (297/1125899906842624), by norm_num⟩
  | 13 => ⟨((-3489698439/4503599627370496), (-11148577623/4503599627370496)), (457/9007199254740992), by norm_num⟩
  | 14 => ⟨((154849551/1125899906842624), (7915192763/18014398509481984)), (327/36028797018963968), by norm_num⟩
  | 15 => ⟨((-1641756497/72057594037927936), (-20979749473/288230376151711744)), (109/72057594037927936), by norm_num⟩
  | 16 => ⟨((8159223273/2305843009213693952), (407286867/36028797018963968)), (545/2305843009213693952), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (825491177565/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222332659561831/79228162514264337593543950336), (1953630534629/633825300114114700748351602688)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889620878017817/39614081257132168796771975168), (2197421581041/39614081257132168796771975168)), (12995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889388337824935/2475880078570760549798248448), (291781232473/309485009821345068724781056)), (13809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771054528042081/154742504910672534362390528), (2333675655165/154742504910672534362390528)), (13811/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774712856520813/4835703278458516698824704), (2187211011173/9671406556917033397649408)), (6475/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314669218110627/151115727451828646838272), (1913199918193/604462909807314587353088)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943805117008729/37778931862957161709568), (1553903535563/37778931862957161709568)), (4605/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297402991779965/4722366482869645213696), (2329855779403/4722366482869645213696)), (13819/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202657538986747/73786976294838206464), (1600964131071/295147905179352825856)), (19007/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911619806203205/36893488147419103232), (1999988280495/36893488147419103232)), (23767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822392151516769/9223372036854775808), (4496629451513/9223372036854775808)), (26749/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796820101376031/576460752303423488), (4492452599269/1152921504606846976)), (6691/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194277801864835/144115188075855872), (490775212371/18014398509481984)), (23435/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491181943724427/36028797018963968), (11484229435/70368744177664)), (17593/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488686589501351/9007199254740992), (3666761481573/4503599627370496)), (5505/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113400314987809/2251799813685248), (14617998200799/4503599627370496)), (88255/4503599627370496), by norm_num⟩
  | 1 => ⟨((553592379649733/562949953421312), (21804740996181/2251799813685248)), (33205/562949953421312), by norm_num⟩
  | 0 => ⟨((2177213192088605/2251799813685248), (43122629692985/2251799813685248)), (66851/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177213192088605/2251799813685248), (43122629692985/2251799813685248)), (255016329051780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1052135650295275/1125899906842624), (83388547840285/2251799813685248)), (65917/281474976710656), by norm_num⟩
  | 2 => ⟨((1963320198229705/2251799813685248), (155850557364653/2251799813685248)), (128079/281474976710656), by norm_num⟩
  | 3 => ⟨((1701011244990383/2251799813685248), (271768871566441/2251799813685248)), (1928565/2251799813685248), by norm_num⟩
  | 4 => ⟨((313036367497603/562949953421312), (410588813235847/2251799813685248)), (844799/562949953421312), by norm_num⟩
  | 5 => ⟨((1242814832791951/4503599627370496), (228313777893343/1125899906842624)), (9980827/4503599627370496), by norm_num⟩
  | 6 => ⟨((315549279946833/9007199254740992), (1008088722530735/9007199254740992)), (19113033/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-1243708167/16777216)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-20540319059/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((429140789952245/9007199254740992), (-443776655970307/4503599627370496)), (2094405/1125899906842624), by norm_num⟩
  | 1 => ⟨((-2099465167/17179869184), (8684270085/34359738368)), (165/34359738368), by norm_num⟩
  | 2 => ⟨((5385021831/34359738368), (-11137356487/34359738368)), (425/68719476736), by norm_num⟩
  | 3 => ⟨((-9208205523/68719476736), (2380562947/8589934592)), (183/34359738368), by norm_num⟩
  | 4 => ⟨((2952322605/34359738368), (-6106023401/34359738368)), (237/68719476736), by norm_num⟩
  | 5 => ⟨((-6058046375/137438953472), (12529312639/137438953472)), (245/137438953472), by norm_num⟩
  | 6 => ⟨((10359054771/549755813888), (-10712350801/274877906944)), (211/274877906944), by norm_num⟩
  | 7 => ⟨((-3795778697/549755813888), (7850467801/549755813888)), (311/1099511627776), by norm_num⟩
  | 8 => ⟨((4867990065/2199023255552), (-10068026171/2199023255552)), (401/4398046511104), by norm_num⟩
  | 9 => ⟨((-11098798213/17592186044416), (22954646451/17592186044416)), (115/4398046511104), by norm_num⟩
  | 10 => ⟨((5693571069/35184372088832), (-11775501133/35184372088832)), (119/17592186044416), by norm_num⟩
  | 11 => ⟨((-10620888331/281474976710656), (10983114205/140737488355328)), (447/281474976710656), by norm_num⟩
  | 12 => ⟨((9080680233/1125899906842624), (-9390377241/562949953421312)), (385/1125899906842624), by norm_num⟩
  | 13 => ⟨((-7166610747/4503599627370496), (14822056659/4503599627370496)), (153/2251799813685248), by norm_num⟩
  | 14 => ⟨((1312999545/4503599627370496), (-21724471259/36028797018963968)), (451/36028797018963968), by norm_num⟩
  | 15 => ⟨((-7184591657/144115188075855872), (14859244959/144115188075855872)), (155/72057594037927936), by norm_num⟩
  | 16 => ⟨((9214056877/1152921504606846976), (-19056605405/1152921504606846976)), (25/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (-1459482086619/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111159707239517/39614081257132168796771975168), (-1726828792867/633825300114114700748351602688)), (11547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889501720387755/39614081257132168796771975168), (-971153472059/19807040628566084398385987584)), (203/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889261793923523/2475880078570760549798248448), (-2063235383279/2475880078570760549798248448)), (13805/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885464026408397/77371252455336267181195264), (-2062711607443/154742504910672534362390528)), (13807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774653607726123/4835703278458516698824704), (-483308948111/2417851639229258349412352)), (6473/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258573259947809/604462909807314587353088), (-845512586347/302231454903657293676544)), (5665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235930250039025/9444732965739290427392), (-2746873544209/75557863725914323419136)), (9207/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324319233985869/1180591620717411303424), (-2059243503503/4722366482869645213696)), (6907/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621087179060361/590295810358705651712), (-2829979149871/590295810358705651712)), (18999/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823023487010165/73786976294838206464), (-1767627142669/36893488147419103232)), (5939/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822149409651111/9223372036854775808), (-3974111240547/9223372036854775808)), (1671/576460752303423488), by norm_num⟩
  | 6 => ⟨((99587372452761/72057594037927936), (-3970302236671/1152921504606846976)), (6687/288230376151711744), by norm_num⟩
  | 5 => ⟨((9328643738727/1125899906842624), (-3469733839649/144115188075855872)), (5855/36028797018963968), by norm_num⟩
  | 4 => ⟨((372716489015443/9007199254740992), (-5196050792869/36028797018963968)), (35159/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488293555199915/9007199254740992), (-6480126371453/9007199254740992)), (1375/281474976710656), by norm_num⟩
  | 2 => ⟨((1113010196129189/2251799813685248), (-12915542513431/4503599627370496)), (44077/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106606834805883/1125899906842624), (-19261891438143/2251799813685248)), (33155/562949953421312), by norm_num⟩
  | 0 => ⟨((543739777042877/562949953421312), (-38080207317175/2251799813685248)), (266801/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543739777042877/562949953421312), (-38080207317175/2251799813685248)), (1017765053755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2100096550007927/2251799813685248), (-73561506881913/2251799813685248)), (262209/1125899906842624), by norm_num⟩
  | 2 => ⟨((1956210404357099/2251799813685248), (-137211368326087/2251799813685248)), (1012441/2251799813685248), by norm_num⟩
  | 3 => ⟨((1691061595872977/2251799813685248), (-29799974301033/281474976710656)), (1882465/2251799813685248), by norm_num⟩
  | 4 => ⟨((311179399921375/562949953421312), (-358068007944315/2251799813685248)), (3225993/2251799813685248), by norm_num⟩
  | 5 => ⟨((315549631902639/1125899906842624), (-395855394128667/2251799813685248)), (2296197/1125899906842624), by norm_num⟩
  | 6 => ⟨((429140789952245/9007199254740992), (-443776655970307/4503599627370496)), (2094405/1125899906842624), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-20540319059/268435456)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-5283445403/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-908231303797469/9007199254740992), (348692485268087/18014398509481984)), (19740785/9007199254740992), by norm_num⟩
  | 1 => ⟨((4571675261/17179869184), (-1755179327/34359738368)), (399/68719476736), by norm_num⟩
  | 2 => ⟨((-6032456553/17179869184), (1158004717/17179869184)), (529/68719476736), by norm_num⟩
  | 3 => ⟨((21226664909/68719476736), (-4074721115/68719476736)), (467/68719476736), by norm_num⟩
  | 4 => ⟨((-14004596403/68719476736), (336044457/8589934592)), (619/137438953472), by norm_num⟩
  | 5 => ⟨((7391786557/68719476736), (-2837889879/137438953472)), (329/137438953472), by norm_num⟩
  | 6 => ⟨((-13004898995/274877906944), (1248225681/137438953472)), (581/549755813888), by norm_num⟩
  | 7 => ⟨((9805906861/549755813888), (-3764730437/1099511627776)), (55/137438953472), by norm_num⟩
  | 8 => ⟨((-25878350375/4398046511104), (4967669727/4398046511104)), (583/4398046511104), by norm_num⟩
  | 9 => ⟨((15176544497/8796093022208), (-2913325601/8796093022208)), (343/8796093022208), by norm_num⟩
  | 10 => ⟨((-16020708397/35184372088832), (12013177/137438953472)), (91/8796093022208), by norm_num⟩
  | 11 => ⟨((15374388335/140737488355328), (-2951304175/140737488355328)), (351/140737488355328), by norm_num⟩
  | 12 => ⟨((-27049261483/1125899906842624), (2596220305/562949953421312)), (155/281474976710656), by norm_num⟩
  | 13 => ⟨((10982238735/2251799813685248), (-4216353369/4503599627370496)), (253/2251799813685248), by norm_num⟩
  | 14 => ⟨((-4140393947/4503599627370496), (198699969/1125899906842624)), (383/18014398509481984), by norm_num⟩
  | 15 => ⟨((5827593063/36028797018963968), (-4474714535/144115188075855872)), (541/144115188075855872), by norm_num⟩
  | 16 => ⟨((-15379352187/576460752303423488), (369032131/72057594037927936)), (179/288230376151711744), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (1922614014311/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778447321029379/633825300114114700748351602688), (2274556819879/316912650057057350374175801344)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889379718418659/39614081257132168796771975168), (2558354736297/19807040628566084398385987584)), (13033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889131497342223/2475880078570760549798248448), (169851197409/77371252455336267181195264)), (3463/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770797003725825/154742504910672534362390528), (5433814719165/154742504910672534362390528)), (13857/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193647944745259/1208925819614629174706176), (2546344481073/4835703278458516698824704)), (12995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629232130661087/302231454903657293676544), (2227295384673/302231454903657293676544)), (11377/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943631691031831/37778931862957161709568), (7235875426735/75557863725914323419136)), (18495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297141665081051/4722366482869645213696), (5424426881261/4722366482869645213696)), (1735/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620899060031831/590295810358705651712), (3727279261987/295147905179352825856)), (9549/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822785160326891/73786976294838206464), (4656078674551/36893488147419103232)), (5973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910938464907933/4611686018427387904), (10467873920667/9223372036854775808)), (26905/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593120037441841/1152921504606846976), (10457499571891/1152921504606846976)), (6735/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193817109777033/144115188075855872), (9138647211409/144115188075855872)), (23611/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490479845960235/36028797018963968), (6842328294765/18014398509481984)), (17747/18014398509481984), by norm_num⟩
  | 3 => ⟨((743894846060725/4503599627370496), (17065056020283/9007199254740992)), (44503/9007199254740992), by norm_num⟩
  | 2 => ⟨((69529666430205/140737488355328), (8501989754779/1125899906842624)), (44707/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105724945990479/1125899906842624), (25353525861651/1125899906842624)), (16893/281474976710656), by norm_num⟩
  | 0 => ⟨((542702463502501/562949953421312), (50098772503805/1125899906842624)), (34299/281474976710656), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((542702463502501/562949953421312), (50098772503805/1125899906842624)), (130840302587413699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1044137193204927/1125899906842624), (96593763232513/1125899906842624)), (138367/562949953421312), by norm_num⟩
  | 2 => ⟨((960025057795417/1125899906842624), (179158271902753/1125899906842624)), (70095/140737488355328), by norm_num⟩
  | 3 => ⟨((395039745450593/562949953421312), (611054070766555/2251799813685248)), (2269505/2251799813685248), by norm_num⟩
  | 4 => ⟨((943030245168655/2251799813685248), (857591844906013/2251799813685248)), (1104221/562949953421312), by norm_num⟩
  | 5 => ⟨((136639385009789/4503599627370496), (359150508336173/1125899906842624)), (7063807/2251799813685248), by norm_num⟩
  | 6 => ⟨((-908231303797469/9007199254740992), (348692485268087/18014398509481984)), (19740785/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5283445403/67108864)), (1/134217728), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-10843141015/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((136485879603925/2251799813685248), (679161921853535/9007199254740992)), (6617223/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2819905195/17179869184), (-14032017357/68719476736)), (69/17179869184), by norm_num⟩
  | 2 => ⟨((15272889661/68719476736), (593740741/2147483648)), (377/68719476736), by norm_num⟩
  | 3 => ⟨((-3446645993/17179869184), (-535959911/2147483648)), (343/68719476736), by norm_num⟩
  | 4 => ⟨((4666845187/34359738368), (5805625379/34359738368)), (117/34359738368), by norm_num⟩
  | 5 => ⟨((-5055220419/68719476736), (-3144384995/34359738368)), (255/137438953472), by norm_num⟩
  | 6 => ⟨((9126527115/274877906944), (11353536557/274877906944)), (29/34359738368), by norm_num⟩
  | 7 => ⟨((-7061455311/549755813888), (-8784556273/549755813888)), (361/1099511627776), by norm_num⟩
  | 8 => ⟨((9561387737/2199023255552), (11894509691/2199023255552)), (247/2199023255552), by norm_num⟩
  | 9 => ⟨((-11507874659/8796093022208), (-14315968605/8796093022208)), (75/2199023255552), by norm_num⟩
  | 10 => ⟨((6232780457/17592186044416), (1938418083/4398046511104)), (327/35184372088832), by norm_num⟩
  | 11 => ⟨((-767212835/8796093022208), (-954424269/8796093022208)), (81/35184372088832), by norm_num⟩
  | 12 => ⟨((11080804651/562949953421312), (1723085889/70368744177664)), (147/281474976710656), by norm_num⟩
  | 13 => ⟨((-4616519271/1125899906842624), (-11486038371/2251799813685248)), (247/2251799813685248), by norm_num⟩
  | 14 => ⟨((14287732503/18014398509481984), (555442295/562949953421312)), (3/140737488355328), by norm_num⟩
  | 15 => ⟨((-10317839167/72057594037927936), (-12835546613/72057594037927936)), (35/9007199254740992), by norm_num⟩
  | 16 => ⟨((13970613215/576460752303423488), (17379652293/576460752303423488)), (381/576460752303423488), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (582080442179/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778365691448673/633825300114114700748351602688), (344282565875/158456325028528675187087900672)), (11543/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944644234056541/19807040628566084398385987584), (774478452983/19807040628566084398385987584)), (12987/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889035308786969/2475880078570760549798248448), (411343666483/618970019642690137449562112)), (13799/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885350837474139/77371252455336267181195264), (822466896403/77371252455336267181195264)), (13801/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774547550059847/4835703278458516698824704), (770828581105/4835703278458516698824704)), (3235/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258387772891241/604462909807314587353088), (674240963735/302231454903657293676544)), (2831/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887140797204745/75557863725914323419136), (1095202922391/37778931862957161709568)), (4601/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324262805043889/1180591620717411303424), (821018568677/2361183241434822606848)), (6903/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620777122806097/590295810358705651712), (564138750307/147573952589676412928)), (9493/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822636370666587/73786976294838206464), (2818825903673/73786976294838206464)), (23739/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910857263652137/4611686018427387904), (792153218565/2305843009213693952)), (26715/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99560240956913/72057594037927936), (3165408072653/1152921504606846976)), (26725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298421857985293/36028797018963968), (2766130827467/144115188075855872)), (5849/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490299251322541/36028797018963968), (4142004170853/36028797018963968)), (17559/18014398509481984), by norm_num⟩
  | 3 => ⟨((92974263785059/562949953421312), (5164942460611/9007199254740992)), (21969/4503599627370496), by norm_num⟩
  | 2 => ⟨((556154707687955/1125899906842624), (10292289972983/4503599627370496)), (87999/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211133988292803/2251799813685248), (7672386706253/1125899906842624)), (66155/1125899906842624), by norm_num⟩
  | 0 => ⟨((542722435203077/562949953421312), (30316849483145/2251799813685248)), (132937/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542722435203077/562949953421312), (30316849483145/2251799813685248)), (507114414695357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046239351909849/1125899906842624), (29227525962443/1125899906842624)), (259901/1125899906842624), by norm_num⟩
  | 2 => ⟨((1942912556548847/2251799813685248), (108638388315095/2251799813685248)), (993037/2251799813685248), by norm_num⟩
  | 3 => ⟨((1671155171125471/2251799813685248), (93736080577779/1125899906842624)), (1809457/2251799813685248), by norm_num⟩
  | 4 => ⟨((306156632797879/562949953421312), (69565480388873/562949953421312)), (2987039/2251799813685248), by norm_num⟩
  | 5 => ⟨((1263238797042741/4503599627370496), (605323669868319/4503599627370496)), (3987199/2251799813685248), by norm_num⟩
  | 6 => ⟨((136485879603925/2251799813685248), (679161921853535/9007199254740992)), (6617223/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-10843141015/134217728)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile051Terms1
