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
namespace Reinmann.XiBand97.Tile002Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9561/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9561/640))
  have he : value ((69/80), (9561/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-20060163/8388608), (-347455105/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-172448057504305/2251799813685248), (451113962349467/9007199254740992)), (149820493/9007199254740992), by norm_num⟩
  | 1 => ⟨((911955909/4294967296), (-596405737/4294967296)), (25/536870912), by norm_num⟩
  | 2 => ⟨((-632119667/2147483648), (413396955/2147483648)), (35/536870912), by norm_num⟩
  | 3 => ⟨((146050655/536870912), (-47757489/268435456)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((-404938399/2147483648), (264823751/2147483648)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((898182111/8589934592), (-146849469/2147483648)), (205/8589934592), by norm_num⟩
  | 6 => ⟨((-830096531/17179869184), (542870909/17179869184)), (191/17179869184), by norm_num⟩
  | 7 => ⟨((41098505/2147483648), (-215022537/17179869184)), (153/34359738368), by norm_num⟩
  | 8 => ⟨((-227898503/34359738368), (596169061/137438953472)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((1123322345/549755813888), (-734636273/549755813888)), (133/274877906944), by norm_num⟩
  | 10 => ⟨((-622902173/1099511627776), (407368849/1099511627776)), (297/2199023255552), by norm_num⟩
  | 11 => ⟨((314009371/2199023255552), (-821430019/8796093022208)), (151/4398046511104), by norm_num⟩
  | 12 => ⟨((-1160825121/35184372088832), (94895317/4398046511104)), (281/35184372088832), by norm_num⟩
  | 13 => ⟨((247576203/35184372088832), (-647644765/140737488355328)), (121/70368744177664), by norm_num⟩
  | 14 => ⟨((-784487987/562949953421312), (64130449/70368744177664)), (193/562949953421312), by norm_num⟩
  | 15 => ⟨((580016679/2251799813685248), (-758644735/4503599627370496)), (9/140737488355328), by norm_num⟩
  | 16 => ⟨((-201018463/4503599627370496), (525852459/18014398509481984)), (101/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (1668919680127/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444568146261559/158456325028528675187087900672), (61688975919/9903520314283042199192993792)), (92589/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889183336207789/39614081257132168796771975168), (277541600895/2475880078570760549798248448)), (26047/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888923092592301/2475880078570760549798248448), (4717054400005/2475880078570760549798248448)), (110729/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221323610198015/19342813113834066795298816), (2357878861057/77371252455336267181195264)), (110761/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774494371780601/4835703278458516698824704), (2209822728983/4835703278458516698824704)), (103873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258294098643873/604462909807314587353088), (3865812721707/604462909807314587353088)), (22731/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886987429674015/75557863725914323419136), (6279364445651/75557863725914323419136)), (18477/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162116899014269/590295810358705651712), (4707265509749/4722366482869645213696)), (110919/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101288497335709/36893488147419103232), (6468822516137/590295810358705651712)), (152605/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822432477219493/73786976294838206464), (8080529264699/73786976294838206464)), (190895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910740901328613/4611686018427387904), (567689903689/576460752303423488)), (53737/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398181739706047/288230376151711744), (9073598250901/1152921504606846976)), (107593/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193475466292877/144115188075855872), (3964393241355/72057594037927936)), (188557/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489971970597129/36028797018963968), (11871976374669/36028797018963968)), (141687/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487162856009305/9007199254740992), (7401455513883/4503599627370496)), (355159/9007199254740992), by norm_num⟩
  | 2 => ⟨((69491236913459/140737488355328), (14747414748839/2251799813685248)), (356577/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104832378371875/1125899906842624), (21982706690595/1125899906842624)), (269209/562949953421312), by norm_num⟩
  | 0 => ⟨((270934435887057/281474976710656), (21706852316335/562949953421312)), (34097/35184372088832), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((270934435887057/281474976710656), (21706852316335/562949953421312)), (130069732800233353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1041480454802965/1125899906842624), (167151875621411/2251799813685248)), (1092317/562949953421312), by norm_num⟩
  | 2 => ⟨((1914373726840161/2251799813685248), (77309452814303/562949953421312)), (4365995/1125899906842624), by norm_num⟩
  | 3 => ⟨((792521324589565/1125899906842624), (525798730081173/2251799813685248)), (17245365/2251799813685248), by norm_num⟩
  | 4 => ⟨((992937241389411/2251799813685248), (370109903641451/1125899906842624)), (8082919/562949953421312), by norm_num⟩
  | 5 => ⟨((24313828852711/281474976710656), (652803867376127/2251799813685248)), (99539707/4503599627370496), by norm_num⟩
  | 6 => ⟨((-172448057504305/2251799813685248), (451113962349467/9007199254740992)), (149820493/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-347455105/8388608)), (1/16777216), by norm_num⟩, -7, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-81995171/33554432), (-710104915/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-134297101664655/18014398509481984), (1558660206680895/18014398509481984)), (16207267/1125899906842624), by norm_num⟩
  | 1 => ⟨((90716443/4294967296), (-526430237/2147483648)), (177/4294967296), by norm_num⟩
  | 2 => ⟨((-64254759/2147483648), (372872293/1073741824)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((3792655/134217728), (-88035563/268435456)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((-42981603/2147483648), (997694127/4294967296)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((97420841/8589934592), (-565336063/4294967296)), (197/8589934592), by norm_num⟩
  | 6 => ⟨((-23001169/4294967296), (1067811785/17179869184)), (47/4294967296), by norm_num⟩
  | 7 => ⟨((148953643/68719476736), (-1728764913/68719476736)), (307/68719476736), by norm_num⟩
  | 8 => ⟨((-52752181/68719476736), (1224489955/137438953472)), (219/137438953472), by norm_num⟩
  | 9 => ⟨((66425859/274877906944), (-1541885013/549755813888)), (139/274877906944), by norm_num⟩
  | 10 => ⟨((-18819863/274877906944), (873697839/1099511627776)), (317/2199023255552), by norm_num⟩
  | 11 => ⟨((77557363/4398046511104), (-1800270819/8796093022208)), (329/8796093022208), by norm_num⟩
  | 12 => ⟨((-146491037/35184372088832), (1700183769/35184372088832)), (313/35184372088832), by norm_num⟩
  | 13 => ⟨((63852363/70368744177664), (-1482148721/140737488355328)), (275/140737488355328), by norm_num⟩
  | 14 => ⟨((-51687819/281474976710656), (1199783867/562949953421312)), (7/17592186044416), by norm_num⟩
  | 15 => ⟨((39051365/1125899906842624), (-1812929953/4503599627370496)), (341/4503599627370496), by norm_num⟩
  | 16 => ⟨((-6915053/1125899906842624), (642052167/9007199254740992)), (61/4503599627370496), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (2158096561441/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778196884611409/633825300114114700748351602688), (2552439617585/633825300114114700748351602688)), (23113/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889098462464251/39614081257132168796771975168), (1435441018607/19807040628566084398385987584)), (104025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944416647329289/1237940039285380274899124224), (1524775773471/1237940039285380274899124224)), (6909/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885249755621691/77371252455336267181195264), (3048696155525/154742504910672534362390528)), (110565/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387226353216381/2417851639229258349412352), (2857244080547/9671406556917033397649408)), (51839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314555409481341/151115727451828646838272), (624795082327/151115727451828646838272)), (90741/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943435265410147/37778931862957161709568), (4059465771393/75557863725914323419136)), (147495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296848260799899/4722366482869645213696), (760777633999/1180591620717411303424)), (55329/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101281102030029/36893488147419103232), (2090929494491/295147905179352825856)), (152215/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911143188555729/36893488147419103232), (652962374431/9223372036854775808)), (95179/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821319919244529/9223372036854775808), (2935840507861/4611686018427387904)), (53569/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398142042088887/288230376151711744), (5865461066201/1152921504606846976)), (107215/576460752303423488), by norm_num⟩
  | 5 => ⟨((596669997931435/72057594037927936), (5125288537227/144115188075855872)), (23475/18014398509481984), by norm_num⟩
  | 4 => ⟨((93110980413281/2251799813685248), (7673971866421/36028797018963968)), (4407/562949953421312), by norm_num⟩
  | 3 => ⟨((1486929567218083/9007199254740992), (9568075559797/9007199254740992)), (353171/9007199254740992), by norm_num⟩
  | 2 => ⟨((138955563485553/281474976710656), (19063152552043/4503599627370496)), (44261/281474976710656), by norm_num⟩
  | 1 => ⟨((1104554144078021/1125899906842624), (28412823753239/2251799813685248)), (66679/140737488355328), by norm_num⟩
  | 0 => ⟨((2166716179125263/2251799813685248), (56101566969387/2251799813685248)), (2152207/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166716179125263/2251799813685248), (56101566969387/2251799813685248)), (8210018166548918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520862421534347/562949953421312), (107963569486147/2251799813685248)), (2124507/1125899906842624), by norm_num⟩
  | 2 => ⟨((1922509468212837/2251799813685248), (99891945808477/1125899906842624)), (4135069/1125899906842624), by norm_num⟩
  | 3 => ⟨((811823730910353/1125899906842624), (42642159051587/281474976710656)), (7794503/1125899906842624), by norm_num⟩
  | 4 => ⟨((559520528053447/1125899906842624), (491950184131895/2251799813685248)), (13602027/1125899906842624), by norm_num⟩
  | 5 => ⟨((897271502951315/4503599627370496), (488953281066295/2251799813685248)), (19462429/1125899906842624), by norm_num⟩
  | 6 => ⟨((-134297101664655/18014398509481984), (1558660206680895/18014398509481984)), (16207267/1125899906842624), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-710104915/16777216)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-1448861729/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((258617497079279/4503599627370496), (535613964436821/9007199254740992)), (172266211/18014398509481984), by norm_num⟩
  | 1 => ⟨((-178218057/1073741824), (-738202799/4294967296)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((515116439/2147483648), (1066840261/4294967296)), (177/4294967296), by norm_num⟩
  | 3 => ⟨((-496292669/2147483648), (-1027854987/4294967296)), (173/4294967296), by norm_num⟩
  | 4 => ⟨((717235157/4294967296), (742720757/4294967296)), (127/4294967296), by norm_num⟩
  | 5 => ⟨((-829230497/8589934592), (-107336955/1073741824)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((798928137/17179869184), (413658271/8589934592)), (73/8589934592), by norm_num⟩
  | 7 => ⟨((-659771235/34359738368), (-341607481/17179869184)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((119186509/17179869184), (123421577/17179869184)), (45/34359738368), by norm_num⟩
  | 9 => ⟨((-76554071/34359738368), (-634194205/274877906944)), (59/137438953472), by norm_num⟩
  | 10 => ⟨((708063119/1099511627776), (91652851/137438953472)), (69/549755813888), by norm_num⟩
  | 11 => ⟨((-93025711/549755813888), (-770649635/4398046511104)), (147/4398046511104), by norm_num⟩
  | 12 => ⟨((11203287/274877906944), (185621995/4398046511104)), (9/1099511627776), by norm_num⟩
  | 13 => ⟨((-318834849/35184372088832), (-660328089/70368744177664)), (65/35184372088832), by norm_num⟩
  | 14 => ⟨((1053201421/562949953421312), (272656237/140737488355328)), (217/562949953421312), by norm_num⟩
  | 15 => ⟨((-405885819/1125899906842624), (-840616413/2251799813685248)), (169/2251799813685248), by norm_num⟩
  | 16 => ⟨((293290227/4503599627370496), (607423485/9007199254740992)), (31/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (1045805420627/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778123607456323/633825300114114700748351602688), (19325029287/9903520314283042199192993792)), (46161/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889016191865495/39614081257132168796771975168), (173887725869/4951760157141521099596496896)), (103871/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472186525245405/618970019642690137449562112), (184708741661/309485009821345068724781056)), (27593/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770412563517623/154742504910672534362390528), (369311855183/38685626227668133590597632)), (55191/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548824160511251/9671406556917033397649408), (1384470702507/9671406556917033397649408)), (51747/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258150803046283/604462909807314587353088), (1210963296133/604462909807314587353088)), (11321/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943377956473067/37778931862957161709568), (983487342475/37778931862957161709568)), (147193/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296762724657305/4722366482869645213696), (11519498601/36893488147419103232)), (110413/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50636897305033/18446744073709551616), (2026237804883/590295810358705651712)), (75923/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822141267483509/73786976294838206464), (2531007625791/73786976294838206464)), (189851/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910579048440141/4611686018427387904), (2844924936835/9223372036854775808)), (213643/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592408124939841/1152921504606846976), (1420927390223/576460752303423488)), (106859/576460752303423488), by norm_num⟩
  | 5 => ⟨((596600977185895/72057594037927936), (620793332107/36028797018963968)), (11693/9007199254740992), by norm_num⟩
  | 4 => ⟨((186196575668109/4503599627370496), (3717871573217/36028797018963968)), (140401/18014398509481984), by norm_num⟩
  | 3 => ⟨((743341327665603/4503599627370496), (2317654484965/4503599627370496)), (87825/2251799813685248), by norm_num⟩
  | 2 => ⟨((2222815903400927/4503599627370496), (9234623205165/4503599627370496)), (703495/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208450022584349/2251799813685248), (6881142870011/1125899906842624)), (528747/1125899906842624), by norm_num⟩
  | 0 => ⟨((2165603017630133/2251799813685248), (27167994849951/2251799813685248)), (2124055/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165603017630133/2251799813685248), (27167994849951/2251799813685248)), (8102626809127043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520594493072465/562949953421312), (26128029353429/1125899906842624)), (4136751/2251799813685248), by norm_num⟩
  | 2 => ⟨((1924490488661259/2251799813685248), (24162197924637/562949953421312)), (980377/281474976710656), by norm_num⟩
  | 3 => ⟨((410152206865673/562949953421312), (165200902170833/2251799813685248)), (14079253/2251799813685248), by norm_num⟩
  | 4 => ⟨((147898692552409/281474976710656), (240723048966513/2251799813685248)), (22581451/2251799813685248), by norm_num⟩
  | 5 => ⟨((148990808829667/562949953421312), (505943720119387/4503599627370496)), (57117001/4503599627370496), by norm_num⟩
  | 6 => ⟨((258617497079279/4503599627370496), (535613964436821/9007199254740992)), (172266211/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1448861729/33554432)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-42607059/16777216), (-368991025/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1421312762272787/18014398509481984), (-6908758136935/18014398509481984)), (88599285/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1995548581/8589934592), (2425005/2147483648)), (127/8589934592), by norm_num⟩
  | 2 => ⟨((1468942757/4294967296), (-7140279/4294967296)), (3/134217728), by norm_num⟩
  | 3 => ⟨((-1441737437/4294967296), (7008039/4294967296)), (3/134217728), by norm_num⟩
  | 4 => ⟨((1061276977/4294967296), (-2579343/2147483648)), (9/536870912), by norm_num⟩
  | 5 => ⟨((-1249946119/8589934592), (3037887/4294967296)), (87/8589934592), by norm_num⟩
  | 6 => ⟨((1226796691/17179869184), (-5963249/17179869184)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((-516032571/17179869184), (1254173/8589934592)), (151/68719476736), by norm_num⟩
  | 8 => ⟨((1519426417/137438953472), (-923209/17179869184)), (113/137438953472), by norm_num⟩
  | 9 => ⟨((-1988381497/549755813888), (4832591/274877906944)), (75/274877906944), by norm_num⟩
  | 10 => ⟨((1170933597/1099511627776), (-1422927/274877906944)), (45/549755813888), by norm_num⟩
  | 11 => ⟨((-626862277/2199023255552), (6094141/4398046511104)), (49/2199023255552), by norm_num⟩
  | 12 => ⟨((1230505149/17592186044416), (-5981275/17592186044416)), (49/8796093022208), by norm_num⟩
  | 13 => ⟨((-1114814561/70368744177664), (5418923/70368744177664)), (91/70368744177664), by norm_num⟩
  | 14 => ⟨((58616133/17592186044416), (-284923/17592186044416)), (155/562949953421312), by norm_num⟩
  | 15 => ⟨((-736390941/1125899906842624), (7158941/2251799813685248)), (123/2251799813685248), by norm_num⟩
  | 16 => ⟨((1084129095/9007199254740992), (-2634883/4503599627370496)), (23/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-1582930619/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889026295814643/316912650057057350374175801344), (-1871878593/158456325028528675187087900672)), (92201/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944468180937337/19807040628566084398385987584), (-8421607623/39614081257132168796771975168)), (103727/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888661363772735/2475880078570760549798248448), (-4472820699/1237940039285380274899124224)), (55105/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770327918648897/154742504910672534362390528), (-8943036385/154742504910672534362390528)), (55105/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548744903993333/9671406556917033397649408), (-8381329859/9671406556917033397649408)), (51661/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258081551566523/604462909807314587353088), (-7330898083/604462909807314587353088)), (90407/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235830445354559/9444732965739290427392), (-11907526557/75557863725914323419136)), (146911/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162084827815225/590295810358705651712), (-4463056255/2361183241434822606848)), (13773/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620265333760169/590295810358705651712), (-12266044345/590295810358705651712)), (151503/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910998716313829/36893488147419103232), (-15321523305/73786976294838206464)), (189379/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910498409146425/4611686018427387904), (-1076347387/576460752303423488)), (53263/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398061878662349/288230376151711744), (-8601317119/576460752303423488)), (106527/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193062170506767/144115188075855872), (-15031043597/144115188075855872)), (23303/18014398509481984), by norm_num⟩
  | 4 => ⟨((744682212798249/18014398509481984), (-22504112795/36028797018963968)), (279639/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486425039239439/9007199254740992), (-28056006435/9007199254740992)), (349555/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222308459144357/4503599627370496), (-55890237777/4503599627370496)), (699133/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207708194044267/2251799813685248), (-83283112753/2251799813685248)), (16387/35184372088832), by norm_num⟩
  | 0 => ⟨((2164195924214133/2251799813685248), (-82185181573/1125899906842624)), (2097863/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164195924214133/2251799813685248), (-82185181573/1125899906842624)), (8002712258345793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2080000159384565/2251799813685248), (-315951416125/2251799813685248)), (4032803/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921307807612801/2251799813685248), (-583692202037/2251799813685248)), (7451379/2251799813685248), by norm_num⟩
  | 3 => ⟨((819660639561031/1125899906842624), (-996049807093/2251799813685248)), (12719375/2251799813685248), by norm_num⟩
  | 4 => ⟨((18647397959559/35184372088832), (-725129131777/1125899906842624)), (4632697/562949953421312), by norm_num⟩
  | 5 => ⟨((1265015952134971/4503599627370496), (-3074494882711/4503599627370496)), (19666169/2251799813685248), by norm_num⟩
  | 6 => ⟨((1421312762272787/18014398509481984), (-6908758136935/18014398509481984)), (88599285/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-368991025/8388608)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-43349291/16777216), (-375418995/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((487577310793331/9007199254740992), (-473862749796301/9007199254740992)), (154592171/18014398509481984), by norm_num⟩
  | 1 => ⟨((-696492713/4294967296), (676901785/4294967296)), (7/268435456), by norm_num⟩
  | 2 => ⟨((1043252849/4294967296), (-506954131/2147483648)), (85/2147483648), by norm_num⟩
  | 3 => ⟨((-1041768743/4294967296), (1012465901/4294967296)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((780215061/4294967296), (-379134597/2147483648)), (131/4294967296), by norm_num⟩
  | 5 => ⟨((-29216443/268435456), (908628599/8589934592)), (159/8589934592), by norm_num⟩
  | 6 => ⟨((933596173/17179869184), (-453668003/8589934592)), (161/17179869184), by norm_num⟩
  | 7 => ⟨((-399543455/17179869184), (97076277/4294967296)), (35/8589934592), by norm_num⟩
  | 8 => ⟨((598462611/68719476736), (-36351817/4294967296)), (107/68719476736), by norm_num⟩
  | 9 => ⟨((-199203751/68719476736), (387201107/137438953472)), (145/274877906944), by norm_num⟩
  | 10 => ⟨((477408885/549755813888), (-463980341/549755813888)), (11/68719476736), by norm_num⟩
  | 11 => ⟨((-1040137603/4398046511104), (1010880641/4398046511104)), (97/2199023255552), by norm_num⟩
  | 12 => ⟨((1038657929/17592186044416), (-1009442587/17592186044416)), (49/4398046511104), by norm_num⟩
  | 13 => ⟨((-957397255/70368744177664), (930467611/70368744177664)), (183/70368744177664), by norm_num⟩
  | 14 => ⟨((3201011/1099511627776), (-796409101/281474976710656)), (159/281474976710656), by norm_num⟩
  | 15 => ⟨((-654634459/1125899906842624), (636220919/1125899906842624)), (129/1125899906842624), by norm_num⟩
  | 16 => ⟨((245138697/2251799813685248), (-476486885/4503599627370496)), (195/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-502244409883/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777983690112573/633825300114114700748351602688), (-1187761298883/633825300114114700748351602688)), (92317/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118053676441081/2475880078570760549798248448), (-1335933254459/39614081257132168796771975168)), (103865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888578944594633/2475880078570760549798248448), (-354763780835/618970019642690137449562112)), (110365/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13830042664631/1208925819614629174706176), (-354658654903/38685626227668133590597632)), (110375/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548667559260223/9671406556917033397649408), (-1329523341873/9671406556917033397649408)), (103487/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9828233079823/4722366482869645213696), (-1162886502799/604462909807314587353088)), (45281/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943266722959277/37778931862957161709568), (-1888853936265/75557863725914323419136)), (73591/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296595968237401/4722366482869645213696), (-1415908809263/4722366482869645213696)), (27601/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620151576090521/590295810358705651712), (-1945686459359/590295810358705651712)), (151833/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821855073829505/73786976294838206464), (-2430327184349/73786976294838206464)), (189833/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910418221415299/4611686018427387904), (-2731671534893/9223372036854775808)), (53405/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796043431362767/576460752303423488), (-2728616611417/1152921504606846976)), (53423/288230376151711744), by norm_num⟩
  | 5 => ⟨((596460645080293/72057594037927936), (-2384107224669/144115188075855872)), (93531/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489152488011425/36028797018963968), (-3569307397433/36028797018963968)), (70189/9007199254740992), by norm_num⟩
  | 3 => ⟨((743079521792379/4503599627370496), (-4449665842629/9007199254740992)), (351231/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221773271493689/4503599627370496), (-4431763360943/2251799813685248)), (351663/2251799813685248), by norm_num⟩
  | 1 => ⟨((551724376923341/562949953421312), (-412691487427/70368744177664)), (1057157/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162543444717581/2251799813685248), (-6514424306101/562949953421312)), (2123051/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162543444717581/2251799813685248), (-6514424306101/562949953421312)), (8098796853072356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2076523462826759/2251799813685248), (-12512413842163/562949953421312)), (4126933/2251799813685248), by norm_num⟩
  | 2 => ⟨((478444475556507/562949953421312), (-92307746938935/2251799813685248)), (7794855/2251799813685248), by norm_num⟩
  | 3 => ⟨((101419571044251/140737488355328), (-39225628588825/562949953421312)), (6944289/1125899906842624), by norm_num⟩
  | 4 => ⟨((1158442020103291/2251799813685248), (-226137127891647/2251799813685248)), (21952513/2251799813685248), by norm_num⟩
  | 5 => ⟨((286626259022851/1125899906842624), (-58168303785945/562949953421312)), (53992353/4503599627370496), by norm_num⟩
  | 6 => ⟨((487577310793331/9007199254740992), (-473862749796301/9007199254740992)), (154592171/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-375418995/8388608)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-88110603/33554432), (-1526133111/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((92208040871479/18014398509481984), (-1300519218313919/18014398509481984)), (206966667/18014398509481984), by norm_num⟩
  | 1 => ⟨((-133862233/8589934592), (1888017627/8589934592)), (303/8589934592), by norm_num⟩
  | 2 => ⟨((101886643/4294967296), (-1437028007/4294967296)), (29/536870912), by norm_num⟩
  | 3 => ⟨((-25849681/1073741824), (1458354671/4294967296)), (119/2147483648), by norm_num⟩
  | 4 => ⟨((39349967/2147483648), (-277499595/1073741824)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((-47920743/4294967296), (675882995/4294967296)), (225/8589934592), by norm_num⟩
  | 6 => ⟨((24315963/4294967296), (-42869603/536870912)), (115/8589934592), by norm_num⟩
  | 7 => ⟨((-10575785/4294967296), (1193302567/34359738368)), (101/17179869184), by norm_num⟩
  | 8 => ⟨((128792859/137438953472), (-454129555/34359738368)), (155/68719476736), by norm_num⟩
  | 9 => ⟨((-43568083/137438953472), (1228984551/274877906944)), (53/68719476736), by norm_num⟩
  | 10 => ⟨((106115205/1099511627776), (-1496668417/1099511627776)), (65/274877906944), by norm_num⟩
  | 11 => ⟨((-117480045/4398046511104), (828480105/2199023255552)), (145/2199023255552), by norm_num⟩
  | 12 => ⟨((14902943/2199023255552), (-840775423/8796093022208)), (37/2199023255552), by norm_num⟩
  | 13 => ⟨((-111685771/70368744177664), (787618351/35184372088832)), (279/70368744177664), by norm_num⟩
  | 14 => ⟨((48575691/140737488355328), (-342560249/70368744177664)), (245/281474976710656), by norm_num⟩
  | 15 => ⟨((-39437275/562949953421312), (1112461189/1125899906842624)), (25/140737488355328), by norm_num⟩
  | 16 => ⟨((120067669/9007199254740992), (-846728263/4503599627370496)), (307/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-976967745691/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444479192341803/158456325028528675187087900672), (-1155138611707/316912650057057350374175801344)), (23107/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888783438265825/39614081257132168796771975168), (-2598469907067/39614081257132168796771975168)), (25999/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472124678622855/618970019642690137449562112), (-2760134722817/2475880078570760549798248448)), (110513/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770165080676291/154742504910672534362390528), (-2759303076981/154742504910672534362390528)), (27633/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548592043091241/9671406556917033397649408), (-646490831869/2417851639229258349412352)), (25911/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628973799089541/302231454903657293676544), (-2261834960437/604462909807314587353088)), (90709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943212756916243/37778931862957161709568), (-918456758443/18889465931478580854784)), (9215/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648257379148635/2361183241434822606848), (-1376961550773/2361183241434822606848)), (110613/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((12656558508777/4611686018427387904), (-29564797063/4611686018427387904)), (152147/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910857165630691/36893488147419103232), (-1181711161809/18446744073709551616)), (190265/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820677237653539/9223372036854775808), (-2656430144113/4611686018427387904)), (13385/576460752303423488), by norm_num⟩
  | 6 => ⟨((397981643240619/288230376151711744), (-5306816394523/1152921504606846976)), (53575/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192779820094393/144115188075855872), (-1159168312467/36028797018963968)), (93835/72057594037927936), by norm_num⟩
  | 4 => ⟨((372234464733735/9007199254740992), (-6941448373413/36028797018963968)), (281821/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485886535632693/9007199254740992), (-4326562162965/4503599627370496)), (176415/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221215671917783/4503599627370496), (-17235375854527/4503599627370496)), (176831/1125899906842624), by norm_num⟩
  | 1 => ⟨((2206029931968605/2251799813685248), (-25676530032995/2251799813685248)), (1065161/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160685275182863/2251799813685248), (-50650803007577/2251799813685248)), (536777/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160685275182863/2251799813685248), (-50650803007577/2251799813685248)), (2047641756297874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2072118190164721/2251799813685248), (-24300660202905/562949953421312)), (1054263/562949953421312), by norm_num⟩
  | 2 => ⟨((1902578290749253/2251799813685248), (-178892776288291/2251799813685248)), (2031295/562949953421312), by norm_num⟩
  | 3 => ⟨((49790748288567/70368744177664), (-302298197619035/2251799813685248)), (15021165/2251799813685248), by norm_num⟩
  | 4 => ⟨((135848735683673/281474976710656), (-213896860625153/1125899906842624)), (25290129/2251799813685248), by norm_num⟩
  | 5 => ⟨((886495132605855/4503599627370496), (-825867177884273/4503599627370496)), (68041601/4503599627370496), by norm_num⟩
  | 6 => ⟨((92208040871479/18014398509481984), (-1300519218313919/18014398509481984)), (206966667/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1526133111/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile002Terms2
