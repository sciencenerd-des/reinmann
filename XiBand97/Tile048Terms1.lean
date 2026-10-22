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
namespace Reinmann.XiBand97.Tile048Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨48,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37559/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37559/1280))
  have he : value ((69/80), (37559/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-2163357985/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-95286731569217/9007199254740992), (-1350445902401457/9007199254740992)), (27692569/9007199254740992), by norm_num⟩
  | 1 => ⟨((798669237/34359738368), (22638190667/68719476736)), (233/34359738368), by norm_num⟩
  | 2 => ⟨((-1754855677/68719476736), (-6217648615/17179869184)), (515/68719476736), by norm_num⟩
  | 3 => ⟨((642635337/34359738368), (18215427133/68719476736)), (379/68719476736), by norm_num⟩
  | 4 => ⟨((-1412014157/137438953472), (-20011692091/137438953472)), (419/137438953472), by norm_num⟩
  | 5 => ⟨((310251221/68719476736), (8794036339/137438953472)), (185/137438953472), by norm_num⟩
  | 6 => ⟨((-28403817/17179869184), (-25763297037/1099511627776)), (17/34359738368), by norm_num⟩
  | 7 => ⟨((1141203471/2199023255552), (8086821349/1099511627776)), (43/274877906944), by norm_num⟩
  | 8 => ⟨((-1253740157/8796093022208), (-4442140655/2199023255552)), (95/2199023255552), by norm_num⟩
  | 9 => ⟨((612166375/17592186044416), (8675893887/17592186044416)), (373/35184372088832), by norm_num⟩
  | 10 => ⟨((-2152107207/281474976710656), (-15250309823/140737488355328)), (329/140737488355328), by norm_num⟩
  | 11 => ⟨((1719513763/1125899906842624), (24369713131/1125899906842624)), (33/70368744177664), by norm_num⟩
  | 12 => ⟨((-1259385967/4503599627370496), (-2231072193/562949953421312)), (389/4503599627370496), by norm_num⟩
  | 13 => ⟨((425715969/9007199254740992), (12066871769/18014398509481984)), (33/2251799813685248), by norm_num⟩
  | 14 => ⟨((-534510623/72057594037927936), (-15150644127/144115188075855872)), (333/144115188075855872), by norm_num⟩
  | 15 => ⟨((626367935/576460752303423488), (17754329407/1152921504606846976)), (49/144115188075855872), by norm_num⟩
  | 16 => ⟨((-1376271021/9223372036854775808), (-19505124463/9223372036854775808)), (433/9223372036854775808), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-2137897091203/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779042432470059/633825300114114700748351602688), (-2530839627787/633825300114114700748351602688)), (11557/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945024761175173/19807040628566084398385987584), (-1423358241743/19807040628566084398385987584)), (3251/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889843576399855/2475880078570760549798248448), (-1512025502059/1237940039285380274899124224)), (6909/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221438693272827/19342813113834066795298816), (-755848182113/38685626227668133590597632)), (13821/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774926029214413/4835703278458516698824704), (-708432854399/2417851639229258349412352)), (405/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259049690640213/604462909807314587353088), (-1239407948321/302231454903657293676544)), (11343/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888215625028323/75557863725914323419136), (-4026765395799/75557863725914323419136)), (18437/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162232081439681/590295810358705651712), (-3018927779625/4722366482869645213696)), (1729/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621883471223675/590295810358705651712), (-4149163696051/590295810358705651712)), (19027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824017628074727/73786976294838206464), (-5183662814221/73786976294838206464)), (11897/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823266136759317/9223372036854775808), (-5827783875315/9223372036854775808)), (837/288230376151711744), by norm_num⟩
  | 6 => ⟨((199314073345949/144115188075855872), (-5822990799735/1152921504606846976)), (26803/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597519669453527/72057594037927936), (-2544864371791/72057594037927936)), (11737/72057594037927936), by norm_num⟩
  | 4 => ⟨((373080164340499/9007199254740992), (-3811913354467/18014398509481984)), (17627/18014398509481984), by norm_num⟩
  | 3 => ⟨((745051854600561/4503599627370496), (-9510964678125/9007199254740992)), (22071/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229616106348515/4503599627370496), (-2370695399293/562949953421312)), (44255/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218546014299165/2251799813685248), (-7076936006469/562949953421312)), (133331/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185380437540653/2251799813685248), (-56054970989281/2251799813685248)), (268937/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185380437540653/2251799813685248), (-56054970989281/2251799813685248)), (1025913247115325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((529881194145961/562949953421312), (-27200783187383/562949953421312)), (535399/2251799813685248), by norm_num⟩
  | 2 => ⟨((497440661646107/562949953421312), (-204823656375707/2251799813685248)), (1059637/2251799813685248), by norm_num⟩
  | 3 => ⟨((434896858473483/562949953421312), (-180988762018875/1125899906842624)), (2065429/2251799813685248), by norm_num⟩
  | 4 => ⟨((1285698974952421/2251799813685248), (-279639223851595/1125899906842624)), (1927629/1125899906842624), by norm_num⟩
  | 5 => ⟨((595181447295275/2251799813685248), (-638656884643905/2251799813685248)), (6317493/2251799813685248), by norm_num⟩
  | 6 => ⟨((-95286731569217/9007199254740992), (-1350445902401457/9007199254740992)), (27692569/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-2163357985/33554432)), (1/134217728), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-533107351/268435456), (-18136756337/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((12633346393891/4503599627370496), (308986173790901/2251799813685248)), (12334429/4503599627370496), by norm_num⟩
  | 1 => ⟨((-443868333/68719476736), (-21712248465/68719476736)), (435/68719476736), by norm_num⟩
  | 2 => ⟨((511022303/68719476736), (24997149825/68719476736)), (503/68719476736), by norm_num⟩
  | 3 => ⟨((-24514007/4294967296), (-9593010759/34359738368)), (97/17179869184), by norm_num⟩
  | 4 => ⟨((451564697/137438953472), (11044361785/68719476736)), (449/137438953472), by norm_num⟩
  | 5 => ⟨((-51988307/34359738368), (-10172233123/137438953472)), (415/274877906944), by norm_num⟩
  | 6 => ⟨((159610001/274877906944), (31229909801/1099511627776)), (5/8589934592), by norm_num⟩
  | 7 => ⟨((-420017839/2199023255552), (-20545578503/2199023255552)), (423/2199023255552), by norm_num⟩
  | 8 => ⟨((483563407/8796093022208), (11826985697/4398046511104)), (245/4398046511104), by norm_num⟩
  | 9 => ⟨((-494864841/35184372088832), (-24206791965/35184372088832)), (503/35184372088832), by norm_num⟩
  | 10 => ⟨((227893681/70368744177664), (22295279331/140737488355328)), (233/70368744177664), by norm_num⟩
  | 11 => ⟨((-381632431/562949953421312), (-18667919211/562949953421312)), (49/70368744177664), by norm_num⟩
  | 12 => ⟨((585827431/4503599627370496), (14328157497/2251799813685248)), (151/1125899906842624), by norm_num⟩
  | 13 => ⟨((-415051541/18014398509481984), (-5075661825/4503599627370496)), (215/9007199254740992), by norm_num⟩
  | 14 => ⟨((546109423/144115188075855872), (26713470297/144115188075855872)), (569/144115188075855872), by norm_num⟩
  | 15 => ⟨((-670647155/1152921504606846976), (-8201338465/288230376151711744)), (351/576460752303423488), by norm_num⟩
  | 16 => ⟨((386055535/4611686018427387904), (4721069923/1152921504606846976)), (203/2305843009213693952), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (2019511724555/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778902682388361/633825300114114700748351602688), (597584189139/158456325028528675187087900672)), (11555/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944946176050083/19807040628566084398385987584), (2688657421949/39614081257132168796771975168)), (13001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889676643381593/2475880078570760549798248448), (2856119371353/2475880078570760549798248448)), (1727/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885671340530607/77371252455336267181195264), (1427734001439/77371252455336267181195264)), (13819/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193711961811837/1208925819614629174706176), (1338154670821/4835703278458516698824704)), (6479/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629456472144457/302231454903657293676544), (292634868971/75557863725914323419136)), (2835/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471998386830679/18889465931478580854784), (3802956718863/75557863725914323419136)), (18433/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297690211408609/4722366482869645213696), (2851083434823/4722366482869645213696)), (13829/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25338356374951/9223372036854775808), (1959198777721/295147905179352825856)), (9511/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823732086743519/73786976294838206464), (305952188057/4611686018427387904)), (5947/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455736324514197/2305843009213693952), (5503343861269/9223372036854775808)), (26775/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797096120870343/576460752303423488), (5498602661417/1152921504606846976)), (13397/576460752303423488), by norm_num⟩
  | 5 => ⟨((298689897946101/36028797018963968), (2402973941759/72057594037927936)), (23465/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491902144707629/36028797018963968), (3599136970105/18014398509481984)), (35237/36028797018963968), by norm_num⟩
  | 3 => ⟨((744791252006099/4503599627370496), (2244808342891/2251799813685248)), (44117/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228579489177331/4503599627370496), (8951369239017/2251799813685248)), (691/35184372088832), by norm_num⟩
  | 1 => ⟨((2217005523725645/2251799813685248), (1669695800567/140737488355328)), (133207/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091178455256281/1125899906842624), (52876437462491/2251799813685248)), (268565/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091178455256281/1125899906842624), (52876437462491/2251799813685248)), (1024494179732512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1056906954671357/1125899906842624), (6405723657041/140737488355328)), (533179/2251799813685248), by norm_num⟩
  | 2 => ⟨((1979618566700797/2251799813685248), (48105547156961/562949953421312)), (524775/1125899906842624), by norm_num⟩
  | 3 => ⟨((861946818575585/1125899906842624), (84581794291357/562949953421312)), (2024751/2251799813685248), by norm_num⟩
  | 4 => ⟨((1268915636299523/2251799813685248), (518021241893861/2251799813685248)), (115893/70368744177664), by norm_num⟩
  | 5 => ⟨((595879294792285/2251799813685248), (291911052563173/1125899906842624)), (1437/549755813888), by norm_num⟩
  | 6 => ⟨((12633346393891/4503599627370496), (308986173790901/2251799813685248)), (12334429/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-18136756337/268435456)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-9443742691/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((45375768883089/1125899906842624), (-539615690966797/4503599627370496)), (5100199/2251799813685248), by norm_num⟩
  | 1 => ⟨((-6641012067/68719476736), (19743986733/68719476736)), (375/68719476736), by norm_num⟩
  | 2 => ⟨((7962225721/68719476736), (-23672006227/68719476736)), (113/17179869184), by norm_num⟩
  | 3 => ⟨((-6364194473/68719476736), (18920997277/68719476736)), (91/17179869184), by norm_num⟩
  | 4 => ⟨((7630335921/137438953472), (-5671321241/34359738368)), (439/137438953472), by norm_num⟩
  | 5 => ⟨((-3659349287/137438953472), (21758775031/274877906944)), (423/274877906944), by norm_num⟩
  | 6 => ⟨((2924912119/274877906944), (-4347938649/137438953472)), (85/137438953472), by norm_num⟩
  | 7 => ⟨((-8015580507/2199023255552), (23830632075/2199023255552)), (117/549755813888), by norm_num⟩
  | 8 => ⟨((1201282663/1099511627776), (-111608125/34359738368)), (283/4398046511104), by norm_num⟩
  | 9 => ⟨((-5120977811/17592186044416), (15224865869/17592186044416)), (19/1099511627776), by norm_num⟩
  | 10 => ⟨((2455913697/35184372088832), (-14603053559/70368744177664)), (293/70368744177664), by norm_num⟩
  | 11 => ⟨((-8565852865/562949953421312), (12733306581/281474976710656)), (513/562949953421312), by norm_num⟩
  | 12 => ⟨((3423336349/1125899906842624), (-5088855943/562949953421312)), (103/562949953421312), by norm_num⟩
  | 13 => ⟨((-5051570491/9007199254740992), (3754628803/2251799813685248)), (153/4503599627370496), by norm_num⟩
  | 14 => ⟨((1730448143/18014398509481984), (-20578758075/72057594037927936)), (211/36028797018963968), by norm_num⟩
  | 15 => ⟨((-4426062317/288230376151711744), (6579427561/144115188075855872)), (17/18014398509481984), by norm_num⟩
  | 16 => ⟨((2653308477/1152921504606846976), (-7888389123/1152921504606846976)), (41/288230376151711744), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-811740476205/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889388514495225/316912650057057350374175801344), (-1921325704377/633825300114114700748351602688)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889751079048969/39614081257132168796771975168), (-2161099009711/39614081257132168796771975168)), (12995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472381662910283/618970019642690137449562112), (-1147841562733/1237940039285380274899124224)), (863/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771192813982787/154742504910672534362390528), (-1147569074991/77371252455336267181195264)), (13811/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549555326496923/9671406556917033397649408), (-2151113140333/9671406556917033397649408)), (12949/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258790254605811/604462909807314587353088), (-470411325957/151115727451828646838272)), (11333/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887794424522503/75557863725914323419136), (-764147238177/18889465931478580854784)), (18419/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162192635761975/590295810358705651712), (-286436627101/590295810358705651712)), (6909/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621450112679567/590295810358705651712), (-3149261985973/590295810358705651712)), (9503/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823476745068599/73786976294838206464), (-983566844151/18446744073709551616)), (23765/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911329381558959/4611686018427387904), (-4422876453373/9223372036854775808)), (26747/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398476652779351/288230376151711744), (-4418911595271/1152921504606846976)), (13381/576460752303423488), by norm_num⟩
  | 5 => ⟨((597255340319599/72057594037927936), (-3862091403597/144115188075855872)), (23433/144115188075855872), by norm_num⟩
  | 4 => ⟨((5826292207161/140737488355328), (-5784235169609/36028797018963968)), (35181/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489121867181449/9007199254740992), (-901842410537/1125899906842624)), (22017/4503599627370496), by norm_num⟩
  | 2 => ⟨((556917197654991/1125899906842624), (-14382909251385/4503599627370496)), (88239/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107832890167207/1125899906842624), (-21458271533637/2251799813685248)), (66395/1125899906842624), by norm_num⟩
  | 0 => ⟨((2179781844203505/2251799813685248), (-42454154946039/2251799813685248)), (267313/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179781844203505/2251799813685248), (-42454154946039/2251799813685248)), (1019718178755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1054633387963977/1125899906842624), (-82192738093293/2251799813685248)), (65951/281474976710656), by norm_num⟩
  | 2 => ⟨((246594449628725/281474976710656), (-153980305557449/2251799813685248)), (1026941/2251799813685248), by norm_num⟩
  | 3 => ⟨((53680042509841/70368744177664), (-67449492573605/562949953421312)), (1939811/2251799813685248), by norm_num⟩
  | 4 => ⟨((319512543780037/562949953421312), (-411624981622745/2251799813685248)), (3424363/2251799813685248), by norm_num⟩
  | 5 => ⟨((650136444514933/2251799813685248), (-467250575872293/2251799813685248)), (5139055/2251799813685248), by norm_num⟩
  | 6 => ⟨((45375768883089/1125899906842624), (-539615690966797/4503599627370496)), (5100199/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-9443742691/134217728)), (1/134217728), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-575319455/268435456), (-19572847303/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-417919527685185/4503599627370496), (645900374737549/9007199254740992)), (12004619/4503599627370496), by norm_num⟩
  | 1 => ⟨((15846115317/68719476736), (-12245194521/68719476736)), (457/68719476736), by norm_num⟩
  | 2 => ⟨((-9844029331/34359738368), (7607041323/34359738368)), (143/17179869184), by norm_num⟩
  | 3 => ⟨((8153831315/34359738368), (-12601858379/68719476736)), (119/17179869184), by norm_num⟩
  | 4 => ⟨((-2532688707/17179869184), (7828610421/68719476736)), (149/34359738368), by norm_num⟩
  | 5 => ⟨((629349501/8589934592), (-3890673219/68719476736)), (149/68719476736), by norm_num⟩
  | 6 => ⟨((-8340665387/274877906944), (12890613005/549755813888)), (31/34359738368), by norm_num⟩
  | 7 => ⟨((5921649967/549755813888), (-4575995711/549755813888)), (177/549755813888), by norm_num⟩
  | 8 => ⟨((-14714747381/4398046511104), (2842730543/1099511627776)), (221/2199023255552), by norm_num⟩
  | 9 => ⟨((16251010497/17592186044416), (-12558080053/17592186044416)), (491/17592186044416), by norm_num⟩
  | 10 => ⟨((-4038224405/17592186044416), (12482262653/70368744177664)), (245/35184372088832), by norm_num⟩
  | 11 => ⟨((14595797349/281474976710656), (-11279002717/281474976710656)), (445/281474976710656), by norm_num⟩
  | 12 => ⟨((-12089731297/1125899906842624), (1167802869/140737488355328)), (371/1125899906842624), by norm_num⟩
  | 13 => ⟨((18487294581/9007199254740992), (-7143091975/4503599627370496)), (569/9007199254740992), by norm_num⟩
  | 14 => ⟨((-13125486069/36028797018963968), (10142809571/36028797018963968)), (203/18014398509481984), by norm_num⟩
  | 15 => ⟨((2174373841/36028797018963968), (-840131165/18014398509481984)), (541/288230376151711744), by norm_num⟩
  | 16 => ⟨((-10806232033/1152921504606846976), (4175295037/576460752303423488)), (169/576460752303423488), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (3235277688233/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889327736445105/316912650057057350374175801344), (3828349382473/633825300114114700748351602688)), (11573/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944807011339189/19807040628566084398385987584), (4306070110715/39614081257132168796771975168)), (6511/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944690313868055/1237940039285380274899124224), (2287098666945/1237940039285380274899124224)), (865/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771046338763691/154742504910672534362390528), (1143267512555/38685626227668133590597632)), (3461/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549417526789665/9671406556917033397649408), (2143027826175/4835703278458516698824704)), (12983/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258669201045859/604462909807314587353088), (3749101422299/604462909807314587353088)), (2841/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471899203875043/18889465931478580854784), (6090045446777/75557863725914323419136)), (9237/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648696047628709/2361183241434822606848), (2282785394851/2361183241434822606848)), (13863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621243977645117/590295810358705651712), (3137235231387/295147905179352825856)), (19073/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227902146240557/9223372036854775808), (244947054309/2305843009213693952)), (23857/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455591031015943/2305843009213693952), (4405760515727/4611686018427387904)), (13431/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49800272097175/36028797018963968), (8803309070921/1152921504606846976)), (26891/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194246350236341/144115188075855872), (1923415687929/36028797018963968)), (11781/72057594037927936), by norm_num⟩
  | 4 => ⟨((745563501149755/18014398509481984), (11522043192787/36028797018963968)), (2213/2251799813685248), by norm_num⟩
  | 3 => ⟨((1488604374947761/9007199254740992), (14370297363911/9007199254740992)), (22187/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113297891968957/2251799813685248), (7160988755291/1125899906842624)), (44545/2251799813685248), by norm_num⟩
  | 1 => ⟨((553490473194239/562949953421312), (10681197374607/562949953421312)), (67247/1125899906842624), by norm_num⟩
  | 0 => ⟨((544000153103849/562949953421312), (42243874597717/1125899906842624)), (136219/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((544000153103849/562949953421312), (42243874597717/1125899906842624)), (519634251121139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049791472744325/1125899906842624), (10205469468997/140737488355328)), (136745/562949953421312), by norm_num⟩
  | 2 => ⟨((972907473156513/1125899906842624), (152249623737157/1125899906842624)), (1099339/2251799813685248), by norm_num⟩
  | 3 => ⟨((820116422236059/1125899906842624), (263122495736829/1125899906842624)), (549307/562949953421312), by norm_num⟩
  | 4 => ⟨((133972277329363/281474976710656), (766643921016591/2251799813685248)), (4227949/2251799813685248), by norm_num⟩
  | 5 => ⟨((498237583020713/4503599627370496), (1459583131681157/4503599627370496)), (13807187/4503599627370496), by norm_num⟩
  | 6 => ⟨((-417919527685185/4503599627370496), (645900374737549/9007199254740992)), (12004619/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-19572847303/268435456)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-296925695/134217728), (-10101659577/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((61055439475871/562949953421312), (265363347899499/18014398509481984)), (4326729/4503599627370496), by norm_num⟩
  | 1 => ⟨((-19116712677/68719476736), (-649112271/17179869184)), (171/68719476736), by norm_num⟩
  | 2 => ⟨((6129174987/17179869184), (3329880205/68719476736)), (111/34359738368), by norm_num⟩
  | 3 => ⟨((-20961364593/68719476736), (-711747841/17179869184)), (3/1073741824), by norm_num⟩
  | 4 => ⟨((13441209661/68719476736), (3651194335/137438953472)), (249/137438953472), by norm_num⟩
  | 5 => ⟨((-13790408833/137438953472), (-3746051425/274877906944)), (129/137438953472), by norm_num⟩
  | 6 => ⟨((5895283379/137438953472), (800702683/137438953472)), (223/549755813888), by norm_num⟩
  | 7 => ⟨((-17281260931/1099511627776), (-586789095/274877906944)), (165/1099511627776), by norm_num⟩
  | 8 => ⟨((2770347445/549755813888), (188135539/274877906944)), (107/2199023255552), by norm_num⟩
  | 9 => ⟨((-25265069863/17592186044416), (-3431524479/17592186044416)), (123/8796093022208), by norm_num⟩
  | 10 => ⟨((6480362471/17592186044416), (3520674603/70368744177664)), (127/35184372088832), by norm_num⟩
  | 11 => ⟨((-24177165899/281474976710656), (-1641882193/140737488355328)), (239/281474976710656), by norm_num⟩
  | 12 => ⟨((2583883589/140737488355328), (2807563117/1125899906842624)), (103/562949953421312), by norm_num⟩
  | 13 => ⟨((-16313921357/4503599627370496), (-1107885725/2251799813685248)), (41/1125899906842624), by norm_num⟩
  | 14 => ⟨((23911075487/36028797018963968), (3247623747/36028797018963968)), (243/36028797018963968), by norm_num⟩
  | 15 => ⟨((-16354852721/144115188075855872), (-2221330785/144115188075855872)), (21/18014398509481984), by norm_num⟩
  | 16 => ⟨((20974684489/1152921504606846976), (2848800485/1152921504606846976)), (109/576460752303423488), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (175845857903/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889278444784189/316912650057057350374175801344), (208057154875/633825300114114700748351602688)), (11529/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889503578999595/39614081257132168796771975168), (117009635413/19807040628566084398385987584)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472315971066629/618970019642690137449562112), (248589384075/2475880078570760549798248448)), (13781/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770930273054341/154742504910672534362390528), (248526307355/154742504910672534362390528)), (3445/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((48415919838887/302231454903657293676544), (232926416765/9671406556917033397649408)), (1615/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258575339730077/604462909807314587353088), (203743643759/604462909807314587353088)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887445638136321/75557863725914323419136), (330957904753/75557863725914323419136)), (9185/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297279889993831/4722366482869645213696), (248108655827/4722366482869645213696)), (6889/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810545803597347/295147905179352825856), (340971122393/590295810358705651712)), (9473/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911514785459447/36893488147419103232), (106486665287/18446744073709551616)), (23683/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822157007379121/9223372036854775808), (478822824007/9223372036854775808)), (6661/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593406496855925/1152921504606846976), (239182146509/576460752303423488)), (13323/576460752303423488), by norm_num⟩
  | 5 => ⟨((149259365486655/18014398509481984), (52256687671/18014398509481984)), (23317/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490880847820621/36028797018963968), (156512805251/9007199254740992)), (34979/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488315837780471/9007199254740992), (780766544575/9007199254740992)), (21865/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226075906462489/4503599627370496), (1556153909311/4503599627370496)), (10935/562949953421312), by norm_num⟩
  | 1 => ⟨((1106662061546551/1125899906842624), (2320829228439/2251799813685248)), (65635/1125899906842624), by norm_num⟩
  | 0 => ⟨((2175287606650103/2251799813685248), (4588328888329/2251799813685248)), (131375/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175287606650103/2251799813685248), (4588328888329/2251799813685248)), (501155857566451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((131335362554373/140737488355328), (4432425522623/1125899906842624)), (127179/562949953421312), by norm_num⟩
  | 2 => ⟨((980473401020327/1125899906842624), (16545249451637/2251799813685248)), (953467/2251799813685248), by norm_num⟩
  | 3 => ⟨((1707540160446741/2251799813685248), (28816375064935/2251799813685248)), (837319/1125899906842624), by norm_num⟩
  | 4 => ⟨((647229606813093/1125899906842624), (5462865460201/281474976710656)), (1291309/1125899906842624), by norm_num⟩
  | 5 => ⟨((46454915198041/140737488355328), (25122860335207/1125899906842624)), (3069511/2251799813685248), by norm_num⟩
  | 6 => ⟨((61055439475871/562949953421312), (265363347899499/18014398509481984)), (4326729/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-10101659577/134217728)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-611009281/268435456), (-10393522457/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-26113130473843/562949953421312), (-825054812866057/9007199254740992)), (20621553/9007199254740992), by norm_num⟩
  | 1 => ⟨((8412359421/68719476736), (8305995755/34359738368)), (417/68719476736), by norm_num⟩
  | 2 => ⟨((-11100349395/68719476736), (-21919998977/68719476736)), (553/68719476736), by norm_num⟩
  | 3 => ⟨((9764819477/68719476736), (9641355661/34359738368)), (489/68719476736), by norm_num⟩
  | 4 => ⟨((-6442479603/68719476736), (-6361022581/34359738368)), (325/68719476736), by norm_num⟩
  | 5 => ⟨((6800829207/137438953472), (13429682613/137438953472)), (345/137438953472), by norm_num⟩
  | 6 => ⟨((-2991296361/137438953472), (-5906950389/137438953472)), (305/274877906944), by norm_num⟩
  | 7 => ⟨((9021945813/1099511627776), (8907874697/549755813888)), (231/549755813888), by norm_num⟩
  | 8 => ⟨((-744044757/274877906944), (-11754196005/2199023255552)), (307/2199023255552), by norm_num⟩
  | 9 => ⟨((1745401573/2199023255552), (13786665387/8796093022208)), (181/4398046511104), by norm_num⟩
  | 10 => ⟨((-7369943703/35184372088832), (-1819190017/4398046511104)), (3/274877906944), by norm_num⟩
  | 11 => ⟨((3536309809/70368744177664), (13966390541/140737488355328)), (371/140737488355328), by norm_num⟩
  | 12 => ⟨((-6221682881/562949953421312), (-12286035109/562949953421312)), (41/70368744177664), by norm_num⟩
  | 13 => ⟨((5052116249/2251799813685248), (19952954465/4503599627370496)), (535/4503599627370496), by norm_num⟩
  | 14 => ⟨((-3809378405/9007199254740992), (-7522427247/9007199254740992)), (405/18014398509481984), by norm_num⟩
  | 15 => ⟨((10723379201/144115188075855872), (10587795607/72057594037927936)), (143/36028797018963968), by norm_num⟩
  | 16 => ⟨((-442181445/36028797018963968), (-13970899801/576460752303423488)), (95/144115188075855872), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-2656745585307/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778453114289893/633825300114114700748351602688), (-3143074348133/633825300114114700748351602688)), (11565/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944693279641533/19807040628566084398385987584), (-110476540423/1237940039285380274899124224)), (13013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944569595500387/1237940039285380274899124224), (-3755329356357/2475880078570760549798248448)), (13829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885402587691757/77371252455336267181195264), (-3754347457817/154742504910672534362390528)), (1729/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549191726409065/9671406556917033397649408), (-3518657741665/9671406556917033397649408)), (12971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314617978957701/151115727451828646838272), (-1538891412145/302231454903657293676544)), (11353/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887276770635023/75557863725914323419136), (-1249860666451/18889465931478580854784)), (18455/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297152536904951/4722366482869645213696), (-3747872516761/4722366482869645213696)), (13847/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620915356589085/590295810358705651712), (-5150547997605/590295810358705651712)), (19049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822807549936307/73786976294838206464), (-6434022020679/73786976294838206464)), (1489/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821904889607143/9223372036854775808), (-904069260167/1152921504606846976)), (26821/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796575727401389/576460752303423488), (-7225408315917/1152921504606846976)), (6711/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193848480418565/144115188075855872), (-6314200300023/144115188075855872)), (5879/36028797018963968), by norm_num⟩
  | 4 => ⟨((745267319781527/18014398509481984), (-9455254015119/36028797018963968)), (35327/36028797018963968), by norm_num⟩
  | 3 => ⟨((743935836366549/4503599627370496), (-1473878206947/1125899906842624)), (11063/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112576772067307/2251799813685248), (-23498083224585/4503599627370496)), (88785/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211856133689801/2251799813685248), (-35037755485911/2251799813685248)), (133883/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172017635227841/2251799813685248), (-34620667785837/1125899906842624)), (135301/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172017635227841/2251799813685248), (-34620667785837/1125899906842624)), (516132359031295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523233261738753/562949953421312), (-33394043518965/562949953421312)), (33667/140737488355328), by norm_num⟩
  | 2 => ⟨((1937350788574775/2251799813685248), (-248304478320079/2251799813685248)), (1065245/2251799813685248), by norm_num⟩
  | 3 => ⟨((819716064812125/1125899906842624), (-427260783979525/2251799813685248)), (1033955/1125899906842624), by norm_num⟩
  | 4 => ⟨((1112526040233377/2251799813685248), (-622137947367633/2251799813685248)), (29655/17592186044416), by norm_num⟩
  | 5 => ⟨((755536579648593/4503599627370496), (-1229495913193251/4503599627370496)), (11696435/4503599627370496), by norm_num⟩
  | 6 => ⟨((-26113130473843/562949953421312), (-825054812866057/9007199254740992)), (20621553/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-10393522457/134217728)), (1/134217728), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-21330480595/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-526227233951789/9007199254740992), (86818789336913/1125899906842624)), (4948119/2251799813685248), by norm_num⟩
  | 1 => ⟨((10872266897/68719476736), (-1793744201/8589934592)), (411/68719476736), by norm_num⟩
  | 2 => ⟨((-7360661139/34359738368), (19430197377/68719476736)), (559/68719476736), by norm_num⟩
  | 3 => ⟨((3322173313/17179869184), (-8769658319/34359738368)), (507/68719476736), by norm_num⟩
  | 4 => ⟨((-2249153027/17179869184), (11874337487/68719476736)), (345/68719476736), by norm_num⟩
  | 5 => ⟨((9745310891/137438953472), (-1607815101/17179869184)), (47/17179869184), by norm_num⟩
  | 6 => ⟨((-8796930373/274877906944), (2902696005/68719476736)), (341/274877906944), by norm_num⟩
  | 7 => ⟨((1701609219/137438953472), (-280737375/17179869184)), (265/549755813888), by norm_num⟩
  | 8 => ⟨((-9216086375/2199023255552), (12164014477/2199023255552)), (361/2199023255552), by norm_num⟩
  | 9 => ⟨((11092277583/8796093022208), (-1830042325/1099511627776)), (437/8796093022208), by norm_num⟩
  | 10 => ⟨((-1501922227/4398046511104), (3964677189/8796093022208)), (119/8796093022208), by norm_num⟩
  | 11 => ⟨((11832089567/140737488355328), (-7808396261/70368744177664)), (471/140737488355328), by norm_num⟩
  | 12 => ⟨((-2670157711/140737488355328), (881063711/35184372088832)), (427/562949953421312), by norm_num⟩
  | 13 => ⟨((278112351/70368744177664), (-734143003/140737488355328)), (357/2251799813685248), by norm_num⟩
  | 14 => ⟨((-13771743233/18014398509481984), (4544219673/4503599627370496)), (555/18014398509481984), by norm_num⟩
  | 15 => ⟨((1243152401/9007199254740992), (-3281593333/18014398509481984)), (403/72057594037927936), by norm_num⟩
  | 16 => ⟨((-6733038219/288230376151711744), (8886719485/288230376151711744)), (137/144115188075855872), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1445362628203/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889180221405919/316912650057057350374175801344), (3419549039613/633825300114114700748351602688)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889282271272483/39614081257132168796771975168), (3846200011863/39614081257132168796771975168)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889028339450827/2475880078570760549798248448), (4085612704385/2475880078570760549798248448)), (13833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885347136338819/77371252455336267181195264), (1021129075957/38685626227668133590597632)), (13837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774543850413929/4835703278458516698824704), (478508675221/1208925819614629174706176)), (811/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314595209804719/151115727451828646838272), (1674198211151/302231454903657293676544)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943564334801381/37778931862957161709568), (5438961814487/75557863725914323419136)), (18463/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297041372425331/4722366482869645213696), (4077312484229/4722366482869645213696)), (6927/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810381180772989/295147905179352825856), (5603204051131/590295810358705651712)), (9529/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822616090766237/73786976294838206464), (1749839108471/18446744073709551616)), (11919/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821689202657777/9223372036854775808), (7867887845875/9223372036854775808)), (13419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24889615620959/18014398509481984), (1964977063337/288230376151711744)), (26863/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596829509823497/72057594037927936), (6868450358551/144115188075855872)), (23535/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490249627045961/36028797018963968), (10284756003831/36028797018963968)), (1105/1125899906842624), by norm_num⟩
  | 3 => ⟨((743756989148127/4503599627370496), (12824628992063/9007199254740992)), (22151/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112216951574595/2251799813685248), (6388870644599/1125899906842624)), (88909/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210766161407337/2251799813685248), (38099389318237/2251799813685248)), (134131/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169796360830371/2251799813685248), (75267062211777/2251799813685248)), (271349/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2169796360830371/2251799813685248), (75267062211777/2251799813685248)), (1035114296920012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088263391905589/2251799813685248), (72526073003901/1125899906842624)), (541075/2251799813685248), by norm_num⟩
  | 2 => ⟨((963630035524591/1125899906842624), (134517768668657/1125899906842624)), (268317/562949953421312), by norm_num⟩
  | 3 => ⟨((1617351257858833/2251799813685248), (57565224676311/281474976710656)), (523407/562949953421312), by norm_num⟩
  | 4 => ⟨((266869278387745/562949953421312), (661537942926017/2251799813685248)), (3863837/2251799813685248), by norm_num⟩
  | 5 => ⟨((623390173281587/4503599627370496), (1254421657782099/4503599627370496)), (2966797/1125899906842624), by norm_num⟩
  | 6 => ⟨((-526227233951789/9007199254740992), (86818789336913/1125899906842624)), (4948119/2251799813685248), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-21330480595/268435456)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile048Terms1
