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
namespace Reinmann.XiBand97.Tile004Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10277/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10277/640))
  have he : value ((69/80), (10277/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-89456925/33554432), (-416371747/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((252996176443253/4503599627370496), (738011541160589/18014398509481984)), (65226657/9007199254740992), by norm_num⟩
  | 1 => ⟨((-372897111/2147483648), (-67985803/536870912)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((1152640801/4294967296), (840588013/4294967296)), (77/2147483648), by norm_num⟩
  | 3 => ⟨((-593810275/2147483648), (-866097745/4294967296)), (161/4294967296), by norm_num⟩
  | 4 => ⟨((917746385/4294967296), (669286225/4294967296)), (127/4294967296), by norm_num⟩
  | 5 => ⟨((-1134717215/8589934592), (-413758427/4294967296)), (159/8589934592), by norm_num⟩
  | 6 => ⟨((292288257/4294967296), (852629909/17179869184)), (83/8589934592), by norm_num⟩
  | 7 => ⟨((-1032543327/34359738368), (-188251089/8589934592)), (37/8589934592), by norm_num⟩
  | 8 => ⟨((797908815/68719476736), (145473027/17179869184)), (29/17179869184), by norm_num⟩
  | 9 => ⟨((-548082227/137438953472), (-399700713/137438953472)), (161/274877906944), by norm_num⟩
  | 10 => ⟨((677658173/549755813888), (494196749/549755813888)), (101/549755813888), by norm_num⟩
  | 11 => ⟨((-95212281/274877906944), (-555484775/2199023255552)), (115/2199023255552), by norm_num⟩
  | 12 => ⟨((392406937/4398046511104), (572342341/8796093022208)), (15/1099511627776), by norm_num⟩
  | 13 => ⟨((-93303577/4398046511104), (-544349069/35184372088832)), (29/8796093022208), by norm_num⟩
  | 14 => ⟨((329606077/70368744177664), (480744595/140737488355328)), (13/17592186044416), by norm_num⟩
  | 15 => ⟨((-1086748135/1125899906842624), (-792534375/1125899906842624)), (87/562949953421312), by norm_num⟩
  | 16 => ⟨((839796155/4503599627370496), (306219675/2251799813685248)), (17/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (820778608173/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777857331528511/633825300114114700748351602688), (121300092335/79228162514264337593543950336)), (11537/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472179178945275/9903520314283042199192993792), (1091450094817/39614081257132168796771975168)), (3245/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1888428014545089/2475880078570760549798248448), (1159350518097/2475880078570760549798248448)), (110337/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27657728082441/2417851639229258349412352), (289749022229/38685626227668133590597632)), (110345/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548526194809067/9671406556917033397649408), (543091201449/4835703278458516698824704)), (3233/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1257890210640487/604462909807314587353088), (475016670759/302231454903657293676544)), (90533/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886332689366857/75557863725914323419136), (1543099050437/75557863725914323419136)), (36783/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324111379007231/1180591620717411303424), (289176914789/1180591620717411303424)), (110363/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202493111419079/73786976294838206464), (1589471683673/590295810358705651712)), (37943/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455399249550207/18446744073709551616), (248167345195/9223372036854775808)), (94875/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455136623174623/2305843009213693952), (2231444360919/9223372036854775808)), (213515/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795898696550729/576460752303423488), (2228870045673/1152921504606846976)), (213575/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192668543877849/144115188075855872), (1947369122727/144115188075855872)), (186945/144115188075855872), by norm_num⟩
  | 4 => ⟨((372193611383745/9007199254740992), (2915279178837/36028797018963968)), (280551/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485688369918351/9007199254740992), (1817007832885/4503599627370496)), (350925/9007199254740992), by norm_num⟩
  | 2 => ⟨((277604692698275/562949953421312), (7237869517637/4503599627370496)), (351279/2251799813685248), by norm_num⟩
  | 1 => ⟨((34461060681631/35184372088832), (5390853621735/1125899906842624)), (1055621/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079909822543673/1125899906842624), (10632432167527/1125899906842624)), (132403/140737488355328), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079909822543673/1125899906842624), (10632432167527/1125899906842624)), (505077362597417787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2071395812586215/2251799813685248), (20396249907225/1125899906842624)), (2051921/1125899906842624), by norm_num⟩
  | 2 => ⟨((952352992990811/1125899906842624), (37524389507027/1125899906842624)), (7698809/2251799813685248), by norm_num⟩
  | 3 => ⟨((402153041290401/562949953421312), (126961426819499/2251799813685248)), (6768699/1125899906842624), by norm_num⟩
  | 4 => ⟨((8921731041465/17592186044416), (22674273091119/281474976710656)), (20867887/2251799813685248), by norm_num⟩
  | 5 => ⟨((282267112687959/1125899906842624), (183985108451171/2251799813685248)), (49055971/4503599627370496), by norm_num⟩
  | 6 => ⟨((252996176443253/4503599627370496), (738011541160589/18014398509481984)), (65226657/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-416371747/8388608)), (1/16777216), by norm_num⟩, -8, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-422359519/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((600587957987283/9007199254740992), (-25192177082471/4503599627370496)), (81329591/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1795902317/8589934592), (75330663/4294967296)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((351940083/1073741824), (-118099429/4294967296)), (99/4294967296), by norm_num⟩
  | 3 => ⟨((-1471341459/4294967296), (123433359/4294967296)), (105/4294967296), by norm_num⟩
  | 4 => ⟨((576672829/2147483648), (-48378073/2147483648)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((-22601929/134217728), (60675667/4294967296)), (27/2147483648), by norm_num⟩
  | 6 => ⟨((755927655/8589934592), (-126832135/17179869184)), (115/17179869184), by norm_num⟩
  | 7 => ⟨((-169300485/4294967296), (3550727/1073741824)), (105/34359738368), by norm_num⟩
  | 8 => ⟨((1061681383/68719476736), (-2783321/2147483648)), (21/17179869184), by norm_num⟩
  | 9 => ⟨((-369877315/68719476736), (124118569/274877906944)), (119/274877906944), by norm_num⟩
  | 10 => ⟨((1855597091/1099511627776), (-77834611/549755813888)), (151/1099511627776), by norm_num⟩
  | 11 => ⟨((-1057857081/2199023255552), (88745445/2199023255552)), (11/274877906944), by norm_num⟩
  | 12 => ⟨((1105634919/8796093022208), (-46376805/4398046511104)), (47/4398046511104), by norm_num⟩
  | 13 => ⟨((-533340291/17592186044416), (2796427/1099511627776)), (23/8796093022208), by norm_num⟩
  | 14 => ⟨((1911183311/281474976710656), (-160332447/281474976710656)), (167/281474976710656), by norm_num⟩
  | 15 => ⟨((-399500281/281474976710656), (8378691/70368744177664)), (71/562949953421312), by norm_num⟩
  | 16 => ⟨((313157705/1125899906842624), (-105085349/4503599627370496)), (113/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-109023042853/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888899391930165/316912650057057350374175801344), (-128889007985/633825300114114700748351602688)), (92213/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944325446064433/19807040628566084398385987584), (-72483211763/19807040628566084398385987584)), (103741/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472089533146889/618970019642690137449562112), (-153984362767/2475880078570760549798248448)), (55113/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770024777890261/154742504910672534362390528), (-38484154531/38685626227668133590597632)), (110227/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774230402786075/4835703278458516698824704), (-36066217939/2417851639229258349412352)), (103339/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78614566340317/37778931862957161709568), (-126181078631/604462909807314587353088)), (90423/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29472499160819/1180591620717411303424), (-204949270063/75557863725914323419136)), (146939/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648188033718985/2361183241434822606848), (-153628892721/4722366482869645213696)), (55103/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809924788000453/295147905179352825856), (-26388106131/73786976294838206464)), (151537/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113842382396959/4611686018427387904), (-131839453809/36893488147419103232)), (94713/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113775819735361/576460752303423488), (-18522567247/576460752303423488)), (213111/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795832234468885/576460752303423488), (-296014355935/1152921504606846976)), (1665/9007199254740992), by norm_num⟩
  | 5 => ⟨((1192552743428385/144115188075855872), (-258623049185/144115188075855872)), (93245/72057594037927936), by norm_num⟩
  | 4 => ⟨((744300879162979/18014398509481984), (-48394614571/4503599627370496)), (279755/36028797018963968), by norm_num⟩
  | 3 => ⟨((371368569478173/2251799813685248), (-482588316269/9007199254740992)), (174865/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110207316221005/2251799813685248), (-961115398169/4503599627370496)), (699571/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102443307964455/1125899906842624), (-1431562771115/2251799813685248)), (1049647/2251799813685248), by norm_num⟩
  | 0 => ⟨((134914309368925/140737488355328), (-352867470859/281474976710656)), (2100521/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((134914309368925/140737488355328), (-352867470859/281474976710656)), (8012851723677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2069309601169039/2251799813685248), (-1353068658139/562949953421312)), (4032487/2251799813685248), by norm_num⟩
  | 2 => ⟨((237699467485401/281474976710656), (-2486826713735/562949953421312)), (3715379/1125899906842624), by norm_num⟩
  | 3 => ⟨((1605812109518955/2251799813685248), (-4200141643077/562949953421312)), (12615877/2251799813685248), by norm_num⟩
  | 4 => ⟨((1145017535027189/2251799813685248), (-11980884395065/1125899906842624)), (18181619/2251799813685248), by norm_num⟩
  | 5 => ⟨((1163949815779997/4503599627370496), (-24368636384301/2251799813685248)), (37754577/4503599627370496), by norm_num⟩
  | 6 => ⟨((600587957987283/9007199254740992), (-25192177082471/4503599627370496)), (81329591/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-422359519/8388608)), (1/16777216), by norm_num⟩, -8, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-91975095/33554432), (-1712369655/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((836510670198481/18014398509481984), (-201615118434823/4503599627370496)), (132106903/18014398509481984), by norm_num⟩
  | 1 => ⟨((-79228757/536870912), (611060809/4294967296)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((503586509/2147483648), (-121374009/536870912)), (41/1073741824), by norm_num⟩
  | 3 => ⟨((-533475011/2147483648), (1028621691/4294967296)), (11/268435456), by norm_num⟩
  | 4 => ⟨((847706151/4294967296), (-51078361/268435456)), (71/2147483648), by norm_num⟩
  | 5 => ⟨((-134702789/1073741824), (1038910597/8589934592)), (91/4294967296), by norm_num⟩
  | 6 => ⟨((285395143/4294967296), (-275142817/4294967296)), (49/4294967296), by norm_num⟩
  | 7 => ⟨((-1036572717/34359738368), (499667819/17179869184)), (45/8589934592), by norm_num⟩
  | 8 => ⟨((823570973/68719476736), (-793985613/68719476736)), (145/68719476736), by norm_num⟩
  | 9 => ⟨((-290816987/68719476736), (280369891/68719476736)), (13/17179869184), by norm_num⟩
  | 10 => ⟨((739385631/549755813888), (-712824485/549755813888)), (67/274877906944), by norm_num⟩
  | 11 => ⟨((-854475395/2199023255552), (823779849/2199023255552)), (39/549755813888), by norm_num⟩
  | 12 => ⟨((905189601/8796093022208), (-872672235/8796093022208)), (21/1099511627776), by norm_num⟩
  | 13 => ⟨((-885151163/35184372088832), (853353643/35184372088832)), (167/35184372088832), by norm_num⟩
  | 14 => ⟨((401865435/70368744177664), (-96857279/17592186044416)), (77/70368744177664), by norm_num⟩
  | 15 => ⟨((-681146659/562949953421312), (328338823/281474976710656)), (33/140737488355328), by norm_num⟩
  | 16 => ⟨((541180187/2251799813685248), (-521739227/2251799813685248)), (53/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (-999246485515/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444435379293169/158456325028528675187087900672), (-73828473779/39614081257132168796771975168)), (92317/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236073305211949/4951760157141521099596496896), (-1328599095949/39614081257132168796771975168)), (103865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888289618565929/2475880078570760549798248448), (-705621020751/1237940039285380274899124224)), (27591/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769956224067497/154742504910672534362390528), (-1410798461207/154742504910672534362390528)), (55187/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774198247059777/4835703278458516698824704), (-165269055695/1208925819614629174706176)), (51743/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257776746730947/604462909807314587353088), (-578206247211/302231454903657293676544)), (90561/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943074177938715/37778931862957161709568), (-1878287834039/75557863725914323419136)), (147181/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296307305605197/4722366482869645213696), (-703972087047/2361183241434822606848)), (110403/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809877458261029/295147905179352825856), (-241833760641/73786976294838206464)), (151831/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910679813208131/36893488147419103232), (-151028711243/4611686018427387904)), (189831/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910139791238967/4611686018427387904), (-2715936684121/9223372036854775808)), (213617/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591530649178237/1152921504606846976), (-2712715197323/1152921504606846976)), (213689/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192435330030533/144115188075855872), (-2370006652737/144115188075855872)), (46765/36028797018963968), by norm_num⟩
  | 4 => ⟨((744212499468209/18014398509481984), (-3547784240089/36028797018963968)), (17547/2251799813685248), by norm_num⟩
  | 3 => ⟨((371313054118019/2251799813685248), (-4422113445393/9007199254740992)), (351225/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219967199085453/4503599627370496), (-1100811103423/562949953421312)), (703311/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204207280737627/2251799813685248), (-13115780696969/2251799813685248)), (1057131/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078619040776839/1125899906842624), (-12929048911373/1125899906842624)), (2122991/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078619040776839/1125899906842624), (-12929048911373/1125899906842624)), (8098567971236418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066350423782729/2251799813685248), (-3096527109157/140737488355328)), (1029109/562949953421312), by norm_num⟩
  | 2 => ⟨((947541916696393/1125899906842624), (-90928297485409/2251799813685248)), (3867993/1125899906842624), by norm_num⟩
  | 3 => ⟨((1591204848018491/2251799813685248), (-76524007824887/1125899906842624)), (13645763/2251799813685248), by norm_num⟩
  | 4 => ⟨((1114001856656095/2251799813685248), (-216298751782001/2251799813685248)), (21140123/2251799813685248), by norm_num⟩
  | 5 => ⟨((265168994897541/1125899906842624), (-428025989900407/4503599627370496)), (49955985/4503599627370496), by norm_num⟩
  | 6 => ⟨((836510670198481/18014398509481984), (-201615118434823/4503599627370496)), (132106903/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-1712369655/33554432)), (1/16777216), by norm_num⟩, -8, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-867182493/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((20700895626757/2251799813685248), (-69341202679799/1125899906842624)), (173914103/18014398509481984), by norm_num⟩
  | 1 => ⟨((-254187059/8589934592), (212860795/1073741824)), (269/8589934592), by norm_num⟩
  | 2 => ⟨((204549145/4294967296), (-685172467/2147483648)), (109/2147483648), by norm_num⟩
  | 3 => ⟨((-109736383/2147483648), (735161697/2147483648)), (59/1073741824), by norm_num⟩
  | 4 => ⟨((176613895/4294967296), (-1183197107/4294967296)), (3/67108864), by norm_num⟩
  | 5 => ⟨((-227399279/8589934592), (761712913/4294967296)), (249/8589934592), by norm_num⟩
  | 6 => ⟨((121995007/8589934592), (-817286427/8589934592)), (269/17179869184), by norm_num⟩
  | 7 => ⟨((-224392445/34359738368), (1503282013/34359738368)), (249/34359738368), by norm_num⟩
  | 8 => ⟨((90286427/34359738368), (-1209719533/68719476736)), (101/34359738368), by norm_num⟩
  | 9 => ⟨((-129164799/137438953472), (1730638649/274877906944)), (291/274877906944), by norm_num⟩
  | 10 => ⟨((41576545/137438953472), (-557071091/274877906944)), (189/549755813888), by norm_num⟩
  | 11 => ⟨((-97330717/1099511627776), (652051879/1099511627776)), (223/2199023255552), by norm_num⟩
  | 12 => ⟨((208863661/8796093022208), (-1399249353/8796093022208)), (121/4398046511104), by norm_num⟩
  | 13 => ⟨((-206863443/35184372088832), (1385849205/35184372088832)), (241/35184372088832), by norm_num⟩
  | 14 => ⟨((190247925/140737488355328), (-79658509/8796093022208)), (7/4398046511104), by norm_num⟩
  | 15 => ⟨((-163302519/562949953421312), (547009811/281474976710656)), (97/281474976710656), by norm_num⟩
  | 16 => ⟨((262825265/4503599627370496), (-1760756657/4503599627370496)), (157/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-115820248925/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777685475304543/633825300114114700748351602688), (-1095268154047/316912650057057350374175801344)), (361/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((1888523309847489/39614081257132168796771975168), (-1231881304323/19807040628566084398385987584)), (51991/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888222425466911/2475880078570760549798248448), (-654251635629/618970019642690137449562112)), (110497/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769888901197045/154742504910672534362390528), (-2616173053387/154742504910672534362390528)), (110515/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548333241173633/9671406556917033397649408), (-306472124817/1208925819614629174706176)), (103627/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257721262791759/604462909807314587353088), (-16753281413/4722366482869645213696)), (45347/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471514484189769/18889465931478580854784), (-3483024255011/75557863725914323419136)), (147413/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648119633034009/2361183241434822606848), (-326352252127/590295810358705651712)), (110591/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619660996780635/590295810358705651712), (-1793759888229/295147905179352825856)), (76057/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821241679668413/73786976294838206464), (-4480869911727/73786976294838206464)), (47555/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820146141779541/9223372036854775808), (-1259032381457/2305843009213693952)), (214103/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591396272640579/1152921504606846976), (-157189833041/36028797018963968)), (53559/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192316701061443/144115188075855872), (-4394512577661/144115188075855872)), (93803/72057594037927936), by norm_num⟩
  | 4 => ⟨((372061241191943/9007199254740992), (-3289092895933/18014398509481984)), (281709/36028797018963968), by norm_num⟩
  | 3 => ⟨((185627941699095/1125899906842624), (-8199012226343/9007199254740992)), (176331/4503599627370496), by norm_num⟩
  | 2 => ⟨((554874746722821/1125899906842624), (-16327065487793/4503599627370496)), (706905/4503599627370496), by norm_num⟩
  | 1 => ⟨((275434763053881/281474976710656), (-24313902818973/2251799813685248)), (133041/281474976710656), by norm_num⟩
  | 0 => ⟨((1077836917991325/1125899906842624), (-47925221892555/2251799813685248)), (1072311/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077836917991325/1125899906842624), (-47925221892555/2251799813685248)), (4090541843894576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1031315668475297/1125899906842624), (-91758731206543/2251799813685248)), (524679/281474976710656), by norm_num⟩
  | 2 => ⟨((1885615382687593/2251799813685248), (-168100586273427/2251799813685248)), (8031715/2251799813685248), by norm_num⟩
  | 3 => ⟨((1566430347353979/2251799813685248), (-281528623805351/2251799813685248)), (14650381/2251799813685248), by norm_num⟩
  | 4 => ⟨((527232850064901/1125899906842624), (-97920556103027/562949953421312)), (24045925/2251799813685248), by norm_num⟩
  | 5 => ⟨((212825967478251/1125899906842624), (-366831428338365/2251799813685248)), (61770971/4503599627370496), by norm_num⟩
  | 6 => ⟨((20700895626757/2251799813685248), (-69341202679799/1125899906842624)), (173914103/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-867182493/16777216)), (1/16777216), by norm_num⟩, -8, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-94291587/33554432), (-1755497529/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-251166721997169/9007199254740992), (-961077369856745/18014398509481984)), (195409891/18014398509481984), by norm_num⟩
  | 1 => ⟨((390207971/4294967296), (93319501/536870912)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-158916905/1073741824), (-1216175773/4294967296)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((690355491/4294967296), (1320806025/4294967296)), (277/4294967296), by norm_num⟩
  | 4 => ⟨((-562311209/4294967296), (-1075828385/4294967296)), (57/1073741824), by norm_num⟩
  | 5 => ⟨((732825681/8589934592), (1402061095/8589934592)), (299/8589934592), by norm_num⟩
  | 6 => ⟨((-49742017/1073741824), (-761341733/8589934592)), (41/2147483648), by norm_num⟩
  | 7 => ⟨((370432671/17179869184), (354360695/8589934592)), (77/8589934592), by norm_num⟩
  | 8 => ⟨((-301726351/34359738368), (-577270677/34359738368)), (253/68719476736), by norm_num⟩
  | 9 => ⟨((218456351/68719476736), (835912709/137438953472)), (185/137438953472), by norm_num⟩
  | 10 => ⟨((-569401505/549755813888), (-1089393721/549755813888)), (243/549755813888), by norm_num⟩
  | 11 => ⟨((674605481/2199023255552), (1290672695/2199023255552)), (145/1099511627776), by norm_num⟩
  | 12 => ⟨((-732643261/8796093022208), (-87607005/549755813888)), (317/8796093022208), by norm_num⟩
  | 13 => ⟨((734468453/35184372088832), (1405204085/35184372088832)), (5/549755813888), by norm_num⟩
  | 14 => ⟨((-85463183/17592186044416), (-1308083019/140737488355328)), (75/35184372088832), by norm_num⟩
  | 15 => ⟨((148505227/140737488355328), (568248101/281474976710656)), (263/562949953421312), by norm_num⟩
  | 16 => ⟨((-241922183/1125899906842624), (-925703585/2251799813685248)), (27/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (-2673507314521/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777630604959413/633825300114114700748351602688), (-3160116410553/633825300114114700748351602688)), (92511/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888461443922523/39614081257132168796771975168), (-1777131763969/19807040628566084398385987584)), (3253/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((944078253400045/1237940039285380274899124224), (-3775322052279/2475880078570760549798248448)), (110625/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769822773418883/154742504910672534362390528), (-3774104222497/154742504910672534362390528)), (110651/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548271024403859/9671406556917033397649408), (-884232305691/2417851639229258349412352)), (103763/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257666601369075/604462909807314587353088), (-3093520099537/604462909807314587353088)), (90821/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942984348326513/37778931862957161709568), (-5024546937247/75557863725914323419136)), (36909/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296171973091083/4722366482869645213696), (-1883145488029/2361183241434822606848)), (110773/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619567880137587/590295810358705651712), (-5175208399851/590295810358705651712)), (152385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910562201126539/36893488147419103232), (-6463851549783/73786976294838206464)), (190593/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820012995048795/9223372036854775808), (-3632372632503/4611686018427387904)), (214571/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397815404430479/288230376151711744), (-906986792555/144115188075855872)), (107381/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192197186594515/144115188075855872), (-3169481130341/72057594037927936)), (188133/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488062323458601/36028797018963968), (-9488582796513/36028797018963968)), (141315/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484789364802269/9007199254740992), (-739127489659/562949953421312)), (354045/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219013166105035/4503599627370496), (-2943535353207/562949953421312)), (710367/4503599627370496), by norm_num⟩
  | 1 => ⟨((550676519348279/562949953421312), (-17531936210737/1125899906842624)), (267815/562949953421312), by norm_num⟩
  | 0 => ⟨((2153959057486939/2251799813685248), (-8637395717627/281474976710656)), (1082739/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153959057486939/2251799813685248), (-8637395717627/281474976710656)), (4130321506980514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2058249094105199/2251799813685248), (-132193610647005/2251799813685248)), (2137839/1125899906842624), by norm_num⟩
  | 2 => ⟨((468393566453893/562949953421312), (-241662138620929/2251799813685248)), (8318349/2251799813685248), by norm_num⟩
  | 3 => ⟨((1532942635177789/2251799813685248), (-402142287418641/2251799813685248)), (488367/70368744177664), by norm_num⟩
  | 4 => ⟨((485876828418947/1125899906842624), (-273763704058163/1125899906842624)), (3357427/281474976710656), by norm_num⟩
  | 5 => ⟨((35777986514509/281474976710656), (-118141443529399/562949953421312)), (72487799/4503599627370496), by norm_num⟩
  | 6 => ⟨((-251166721997169/9007199254740992), (-961077369856745/18014398509481984)), (195409891/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-1755497529/33554432)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-1775832425/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-929556764987155/18014398509481984), (-487658869569217/18014398509481984)), (5953911/562949953421312), by norm_num⟩
  | 1 => ⟨((730435241/4294967296), (191598425/2147483648)), (151/4294967296), by norm_num⟩
  | 2 => ⟨((-601848849/2147483648), (-631477153/4294967296)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((1322397083/4294967296), (43359285/268435456)), (139/2147483648), by norm_num⟩
  | 4 => ⟨((-68100079/268435456), (-71452565/536870912)), (231/4294967296), by norm_num⟩
  | 5 => ⟨((718229603/4294967296), (376793597/4294967296)), (77/2147483648), by norm_num⟩
  | 6 => ⟨((-197263967/2147483648), (-103487519/2147483648)), (171/8589934592), by norm_num⟩
  | 7 => ⟨((743028405/17179869184), (194901703/8589934592)), (163/17179869184), by norm_num⟩
  | 8 => ⟨((-1224450205/68719476736), (-321182109/34359738368)), (135/34359738368), by norm_num⟩
  | 9 => ⟨((896797361/137438953472), (29404551/8589934592)), (25/17179869184), by norm_num⟩
  | 10 => ⟨((-1182279121/549755813888), (-620240661/549755813888)), (133/274877906944), by norm_num⟩
  | 11 => ⟨((354236283/549755813888), (92918729/274877906944)), (161/1099511627776), by norm_num⟩
  | 12 => ⟨((-778336667/4398046511104), (-204163315/2199023255552)), (89/2199023255552), by norm_num⟩
  | 13 => ⟨((98664257/2199023255552), (207042763/8796093022208)), (91/8796093022208), by norm_num⟩
  | 14 => ⟨((-743271533/70368744177664), (-389930955/70368744177664)), (173/70368744177664), by norm_num⟩
  | 15 => ⟨((20414181/8796093022208), (342706351/281474976710656)), (153/281474976710656), by norm_num⟩
  | 16 => ⟨((-1076508965/2251799813685248), (-564752113/2251799813685248)), (127/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-3462925309823/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888788427876581/316912650057057350374175801344), (-4092997405379/633825300114114700748351602688)), (92603/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118025049593837/2475880078570760549798248448), (-4603477150843/39614081257132168796771975168)), (104205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472022954288299/618970019642690137449562112), (-2444887283103/1237940039285380274899124224)), (27687/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769757804481459/154742504910672534362390528), (-4888177648669/154742504910672534362390528)), (55391/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774104909775951/4835703278458516698824704), (-4580970346585/9671406556917033397649408)), (51947/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257612750957745/604462909807314587353088), (-4006653445139/604462909807314587353088)), (90943/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885880635076077/75557863725914323419136), (-6507633838695/75557863725914323419136)), (73925/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296105442234105/4722366482869645213696), (-4877945875991/4722366482869645213696)), (110947/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619475613834897/590295810358705651712), (-6702661240649/590295810358705651712)), (152647/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821007891948373/73786976294838206464), (-8371559160667/73786976294838206464)), (95477/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819880305460395/9223372036854775808), (-9408705584997/9223372036854775808)), (215021/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99445432122209/72057594037927936), (-9397092530421/1152921504606846976)), (215269/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192077061974911/144115188075855872), (-4104702535363/72057594037927936)), (5895/4503599627370496), by norm_num⟩
  | 4 => ⟨((185984704582937/4503599627370496), (-12288040291077/36028797018963968)), (141759/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484550671458237/9007199254740992), (-7657255047161/4503599627370496)), (177689/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109256217026445/2251799813685248), (-30492709357065/4503599627370496)), (89213/562949953421312), by norm_num⟩
  | 1 => ⟨((550474292732991/562949953421312), (-22699685597191/1125899906842624)), (269487/562949953421312), by norm_num⟩
  | 0 => ⟨((2152113324227257/2251799813685248), (-44723235464017/1125899906842624)), (1092807/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152113324227257/2251799813685248), (-44723235464017/1125899906842624)), (4168727879050826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2053286913452641/2251799813685248), (-85486703000605/1125899906842624)), (4351351/2251799813685248), by norm_num⟩
  | 2 => ⟨((1859292827875433/2251799813685248), (-311801657462771/2251799813685248)), (8596269/2251799813685248), by norm_num⟩
  | 3 => ⟨((1492028521262731/2251799813685248), (-128726048807027/562949953421312)), (518011/70368744177664), by norm_num⟩
  | 4 => ⟨((870869055979083/2251799813685248), (-682344620804339/2251799813685248)), (14773793/1125899906842624), by norm_num⟩
  | 5 => ⟨((32509409733237/562949953421312), (-1055569526493159/4503599627370496)), (2547613/140737488355328), by norm_num⟩
  | 6 => ⟨((-929556764987155/18014398509481984), (-487658869569217/18014398509481984)), (5953911/562949953421312), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1775832425/33554432)), (1/16777216), by norm_num⟩, -8, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile004Terms3
