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
namespace Reinmann.XiBand97.Tile042Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35411/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35411/1280))
  have he : value ((69/80), (35411/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1286866721/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((216492776425535/9007199254740992), (-1590531993232833/18014398509481984)), (486334689/18014398509481984), by norm_num⟩
  | 1 => ⟨((-286219325/4294967296), (525699981/2147483648)), (323/4294967296), by norm_num⟩
  | 2 => ⟨((99196059/1073741824), (-1457549839/4294967296)), (225/2147483648), by norm_num⟩
  | 3 => ⟨((-366706499/4294967296), (673531041/2147483648)), (209/2147483648), by norm_num⟩
  | 4 => ⟨((31772697/536870912), (-233428071/1073741824)), (291/4294967296), by norm_num⟩
  | 5 => ⟨((-70474097/2147483648), (1035520059/8589934592)), (325/8589934592), by norm_num⟩
  | 6 => ⟨((130263791/8589934592), (-478511873/8589934592)), (151/8589934592), by norm_num⟩
  | 7 => ⟨((-412763335/68719476736), (1516247569/68719476736)), (481/68719476736), by norm_num⟩
  | 8 => ⟨((143052871/68719476736), (-131372841/17179869184)), (335/137438953472), by norm_num⟩
  | 9 => ⟨((-352557135/549755813888), (1295085715/549755813888)), (415/549755813888), by norm_num⟩
  | 10 => ⟨((390998375/2199023255552), (-1436296019/2199023255552)), (463/2199023255552), by norm_num⟩
  | 11 => ⟨((-394210067/8796093022208), (1448093871/8796093022208)), (469/8796093022208), by norm_num⟩
  | 12 => ⟨((182163731/17592186044416), (-41822591/1099511627776)), (435/35184372088832), by norm_num⟩
  | 13 => ⟨((-19425581/8796093022208), (1141728927/140737488355328)), (373/140737488355328), by norm_num⟩
  | 14 => ⟨((246213243/562949953421312), (-226110339/140737488355328)), (149/281474976710656), by norm_num⟩
  | 15 => ⟨((-182039483/2251799813685248), (668705041/2251799813685248)), (443/4503599627370496), by norm_num⟩
  | 16 => ⟨((252360309/18014398509481984), (-231755507/4503599627370496)), (309/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-1699921350383/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778278771115501/633825300114114700748351602688), (-2010716915795/633825300114114700748351602688)), (46199/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889190638825867/39614081257132168796771975168), (-2261585351297/39614081257132168796771975168)), (207921/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888931305482577/2475880078570760549798248448), (-2402348232679/2475880078570760549798248448)), (110473/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885298802291223/77371252455336267181195264), (-2401689007053/154742504910672534362390528)), (220979/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193624682870455/1208925819614629174706176), (-2250883247783/9671406556917033397649408)), (207203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258302269264449/604462909807314587353088), (-1968822905257/604462909807314587353088)), (90669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887001720624797/75557863725914323419136), (-3198025391817/75557863725914323419136)), (73685/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296946796357033/4722366482869645213696), (-2397371744867/4722366482869645213696)), (221113/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202579168902731/73786976294838206464), (-3294522822027/590295810358705651712)), (76031/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822456373441703/73786976294838206464), (-4115360344761/73786976294838206464)), (380297/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821511642473891/9223372036854775808), (-1156485674405/2305843009213693952)), (107007/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199095060846259/144115188075855872), (-4621149985649/1152921504606846976)), (26767/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193508941983125/144115188075855872), (-4038120482261/144115188075855872)), (93753/36028797018963968), by norm_num⟩
  | 4 => ⟨((745015217814417/18014398509481984), (-3023212155731/18014398509481984)), (563067/36028797018963968), by norm_num⟩
  | 3 => ⟨((371812579769137/2251799813685248), (-3769620297943/4503599627370496)), (176199/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111968709945523/2251799813685248), (-15022247301195/4503599627370496)), (706243/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105048991864025/1125899906842624), (-699789357837/70368744177664)), (66437/70368744177664), by norm_num⟩
  | 0 => ⟨((135547685194747/140737488355328), (-44228904352951/2251799813685248)), (535141/281474976710656), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((135547685194747/140737488355328), (-44228904352951/2251799813685248)), (2041400910497569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2087919434769257/2251799813685248), (-85195858954171/2251799813685248)), (4207347/1125899906842624), by norm_num⟩
  | 2 => ⟨((1932742513457091/2251799813685248), (-39497758324519/562949953421312)), (16241321/2251799813685248), by norm_num⟩
  | 3 => ⟨((823903713414307/1125899906842624), (-67802649450545/562949953421312)), (235619/17592186044416), by norm_num⟩
  | 4 => ⟨((586578369777007/1125899906842624), (-396929455786453/2251799813685248)), (51404313/2251799813685248), by norm_num⟩
  | 5 => ⟨((1082461891401887/4503599627370496), (-206794788485791/1125899906842624)), (143368347/4503599627370496), by norm_num⟩
  | 6 => ⟨((216492776425535/9007199254740992), (-1590531993232833/18014398509481984)), (486334689/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1286866721/16777216)), (1/8388608), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-82187811/1048576)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-193074929256813/2251799813685248), (-15520914015983/1125899906842624)), (132896693/4503599627370496), by norm_num⟩
  | 1 => ⟨((1043362553/4294967296), (167747729/4294967296)), (361/4294967296), by norm_num⟩
  | 2 => ⟨((-739017177/2147483648), (-29704069/536870912)), (513/4294967296), by norm_num⟩
  | 3 => ⟨((697931109/2147483648), (224421239/4294967296)), (243/2147483648), by norm_num⟩
  | 4 => ⟨((-494346933/2147483648), (-19869789/536870912)), (173/2147483648), by norm_num⟩
  | 5 => ⟨((560236131/4294967296), (45036281/2147483648)), (197/4294967296), by norm_num⟩
  | 6 => ⟨((-264544747/4294967296), (-2658279/268435456)), (187/8589934592), by norm_num⟩
  | 7 => ⟨((1713169617/68719476736), (275436673/68719476736)), (19/2147483648), by norm_num⟩
  | 8 => ⟨((-1213443755/137438953472), (-97546357/68719476736)), (27/8589934592), by norm_num⟩
  | 9 => ⟨((1527975573/549755813888), (245661903/549755813888)), (273/274877906944), by norm_num⟩
  | 10 => ⟨((-1731632313/2199023255552), (-278405033/2199023255552)), (621/2199023255552), by norm_num⟩
  | 11 => ⟨((6968869/34359738368), (143414701/4398046511104)), (321/4398046511104), by norm_num⟩
  | 12 => ⟨((-842423153/17592186044416), (-270882963/35184372088832)), (19/1099511627776), by norm_num⟩
  | 13 => ⟨((1468778165/140737488355328), (236144377/140737488355328)), (133/35184372088832), by norm_num⟩
  | 14 => ⟨((-594480271/281474976710656), (-11947275/35184372088832)), (27/35184372088832), by norm_num⟩
  | 15 => ⟨((1796575399/4503599627370496), (288846327/4503599627370496)), (655/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1272520349/18014398509481984), (-204590817/18014398509481984)), (233/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-3884623436235/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778189063142031/633825300114114700748351602688), (-1148612501369/158456325028528675187087900672)), (23163/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944544615230827/19807040628566084398385987584), (-5167630904975/39614081257132168796771975168)), (104263/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944411455985837/1237940039285380274899124224), (-5489236077507/2475880078570760549798248448)), (110813/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885244241884233/77371252455336267181195264), (-685961626481/19342813113834066795298816)), (110851/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774447195017883/4835703278458516698824704), (-1285768251149/2417851639229258349412352)), (207927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258211308956701/604462909807314587353088), (-2249275018317/302231454903657293676544)), (711/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((235856558123831/9444732965739290427392), (-913383965951/9444732965739290427392)), (36991/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162104198944867/590295810358705651712), (-5477616471971/4722366482869645213696)), (111039/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620475644792011/590295810358705651712), (-3763678575559/295147905179352825856)), (305573/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911128085153835/36893488147419103232), (-9402650649437/73786976294838206464)), (23893/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910641100058833/4611686018427387904), (-5284492758161/4611686018427387904)), (430519/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398131447110679/288230376151711744), (-2639436483919/288230376151711744)), (431075/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193297683520509/144115188075855872), (-9225391423851/144115188075855872)), (377817/144115188075855872), by norm_num⟩
  | 4 => ⟨((186212723984711/4503599627370496), (-6906417634043/18014398509481984)), (567977/36028797018963968), by norm_num⟩
  | 3 => ⟨((743409514208241/4503599627370496), (-2152737487535/1125899906842624)), (712167/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111506864186793/2251799813685248), (-17155776968133/2251799813685248)), (715469/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104280442183519/1125899906842624), (-6392171406097/281474976710656)), (540739/562949953421312), by norm_num⟩
  | 0 => ⟨((541272441935777/562949953421312), (-12619855813895/281474976710656)), (2196195/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541272441935777/562949953421312), (-12619855813895/281474976710656)), (8377819065574264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038596101054399/1125899906842624), (-48535612316871/562949953421312)), (4420185/1125899906842624), by norm_num⟩
  | 2 => ⟨((949692803041473/1125899906842624), (-22386047555485/140737488355328)), (8917063/1125899906842624), by norm_num⟩
  | 3 => ⟨((386288233462099/562949953421312), (-302120898993341/1125899906842624)), (35759531/2251799813685248), by norm_num⟩
  | 4 => ⟨((898121327773061/2251799813685248), (-829244217215709/2251799813685248)), (2133331/70368744177664), by norm_num⟩
  | 5 => ⟨((105671869135151/4503599627370496), (-1322962925723035/4503599627370496)), (209470417/4503599627370496), by norm_num⟩
  | 6 => ⟨((-193074929256813/2251799813685248), (-15520914015983/1125899906842624)), (132896693/4503599627370496), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-82187811/1048576)), (1/8388608), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1341534429/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-110482000965717/9007199254740992), (368173889792199/4503599627370496)), (125520131/4503599627370496), by norm_num⟩
  | 1 => ⟨((19033793/536870912), (-1014861501/4294967296)), (87/1073741824), by norm_num⟩
  | 2 => ⟨((-220058951/4294967296), (1466663511/4294967296)), (505/4294967296), by norm_num⟩
  | 3 => ⟨((13251087/268435456), (-1413067597/4294967296)), (489/4294967296), by norm_num⟩
  | 4 => ⟨((-153202271/4294967296), (1021072669/4294967296)), (355/4294967296), by norm_num⟩
  | 5 => ⟨((177124607/8589934592), (-590255921/4294967296)), (103/2147483648), by norm_num⟩
  | 6 => ⟨((-170651987/17179869184), (142171587/2147483648)), (399/17179869184), by norm_num⟩
  | 7 => ⟨((70463955/17179869184), (-939265691/34359738368)), (331/34359738368), by norm_num⟩
  | 8 => ⟨((-101833513/68719476736), (1357413513/137438953472)), (481/137438953472), by norm_num⟩
  | 9 => ⟨((261632631/549755813888), (-871873263/274877906944)), (155/137438953472), by norm_num⟩
  | 10 => ⟨((-75621557/549755813888), (1008015143/1099511627776)), (361/1099511627776), by norm_num⟩
  | 11 => ⟨((158963209/4398046511104), (-529734273/2199023255552)), (381/4398046511104), by norm_num⟩
  | 12 => ⟨((-153154257/17592186044416), (1020752655/17592186044416)), (369/17592186044416), by norm_num⟩
  | 13 => ⟨((272413993/140737488355328), (-1815602859/140737488355328)), (659/140737488355328), by norm_num⟩
  | 14 => ⟨((-224965061/562949953421312), (1499362065/562949953421312)), (273/281474976710656), by norm_num⟩
  | 15 => ⟨((10837211/140737488355328), (-1155657005/2251799813685248)), (423/2251799813685248), by norm_num⟩
  | 16 => ⟨((-250588549/18014398509481984), (1670139185/18014398509481984)), (613/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (280016873953/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889060332616171/316912650057057350374175801344), (662313251991/158456325028528675187087900672)), (184921/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472253179866437/9903520314283042199192993792), (744940360213/9903520314283042199192993792)), (208071/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59023193618239/77371252455336267181195264), (1582595563235/1237940039285380274899124224)), (110557/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885204207915773/77371252455336267181195264), (1582142685933/77371252455336267181195264)), (110579/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548820014608837/9671406556917033397649408), (1482777740575/4835703278458516698824704)), (103691/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258146918156611/604462909807314587353088), (2593899338921/604462909807314587353088)), (90753/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117921819885883/4722366482869645213696), (2106641981995/37778931862957161709568)), (295033/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296757207450629/4722366482869645213696), (394798319715/590295810358705651712)), (27669/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620372444150505/590295810358705651712), (4340221226669/590295810358705651712)), (304483/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227766238354203/9223372036854775808), (5421438520005/73786976294838206464)), (380789/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821143911148885/9223372036854775808), (6093845000255/9223372036854775808)), (107161/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199049023337911/144115188075855872), (6087259228499/1152921504606846976)), (428965/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596593020993943/72057594037927936), (2659475466827/72057594037927936)), (375705/144115188075855872), by norm_num⟩
  | 4 => ⟨((372386204185975/9007199254740992), (7963644854797/36028797018963968)), (564281/36028797018963968), by norm_num⟩
  | 3 => ⟨((92915068020799/562949953421312), (9928733847111/9007199254740992)), (353309/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222712390510633/4503599627370496), (618130709915/140737488355328)), (708523/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104122103231353/1125899906842624), (14738848213829/1125899906842624)), (1067561/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082495794395931/1125899906842624), (58188882142177/2251799813685248)), (4308623/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082495794395931/1125899906842624), (58188882142177/2251799813685248)), (16436092385298918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2080026210620003/2251799813685248), (111891332109883/2251799813685248)), (4253863/1125899906842624), by norm_num⟩
  | 2 => ⟨((1915796129143781/2251799813685248), (206711895182949/2251799813685248)), (1035185/140737488355328), by norm_num⟩
  | 3 => ⟨((805476796557551/1125899906842624), (351734506977647/2251799813685248)), (31223927/2251799813685248), by norm_num⟩
  | 4 => ⟨((1097546194271559/2251799813685248), (251633366516217/1125899906842624)), (6803761/281474976710656), by norm_num⟩
  | 5 => ⟨((844950992713617/4503599627370496), (30662055535881/140737488355328)), (77389109/2251799813685248), by norm_num⟩
  | 6 => ⟨((-110482000965717/9007199254740992), (368173889792199/4503599627370496)), (125520131/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1341534429/16777216)), (1/8388608), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-683314569/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1385831237083401/18014398509481984), (157836530516787/9007199254740992)), (108579613/9007199254740992), by norm_num⟩
  | 1 => ⟨((-486432971/2147483648), (-221605317/4294967296)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((179034025/536870912), (326251667/4294967296)), (229/4294967296), by norm_num⟩
  | 3 => ⟨((-1405746031/4294967296), (-320209375/4294967296)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((129347919/536870912), (235709241/4294967296)), (169/4294967296), by norm_num⟩
  | 5 => ⟨((-1218742575/8589934592), (-277612591/8589934592)), (201/8589934592), by norm_num⟩
  | 6 => ⟨((149521381/2147483648), (272471111/17179869184)), (199/17179869184), by norm_num⟩
  | 7 => ⟨((-125787595/4294967296), (-229221303/34359738368)), (169/34359738368), by norm_num⟩
  | 8 => ⟨((1481495591/137438953472), (168732035/68719476736)), (251/137438953472), by norm_num⟩
  | 9 => ⟨((-969371859/274877906944), (-110404707/137438953472)), (83/137438953472), by norm_num⟩
  | 10 => ⟨((1141702515/1099511627776), (130031969/549755813888)), (197/1099511627776), by norm_num⟩
  | 11 => ⟨((-611213343/2199023255552), (-69612945/1099511627776)), (213/4398046511104), by norm_num⟩
  | 12 => ⟨((74986683/1099511627776), (136647379/8796093022208)), (211/17592186044416), by norm_num⟩
  | 13 => ⟨((-543492215/35184372088832), (-247599919/70368744177664)), (193/70368744177664), by norm_num⟩
  | 14 => ⟨((457222761/140737488355328), (104148979/140737488355328)), (41/70368744177664), by norm_num⟩
  | 15 => ⟨((-11218871/17592186044416), (-163552167/1125899906842624)), (65/562949953421312), by norm_num⟩
  | 16 => ⟨((528532497/4503599627370496), (15049043/562949953421312)), (193/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (291739005585/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222256565981437/79228162514264337593543950336), (43124126283/79228162514264337593543950336)), (46117/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944468143306533/19807040628566084398385987584), (97008016149/9903520314283042199192993792)), (51883/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888661279130733/2475880078570760549798248448), (51522165403/309485009821345068724781056)), (220507/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221290978593963/19342813113834066795298816), (206028646599/77371252455336267181195264)), (220513/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548744814135413/9671406556917033397649408), (386176229825/9671406556917033397649408)), (206737/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258081467366429/604462909807314587353088), (168888387049/302231454903657293676544)), (90451/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235830426946209/9444732965739290427392), (274324225135/37778931862957161709568)), (36747/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296678502945627/4722366482869645213696), (411277498931/4722366482869645213696)), (220493/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810132577266243/295147905179352825856), (565167418971/590295810358705651712)), (303193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821997186411337/73786976294838206464), (88243868373/9223372036854775808)), (47377/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910498255427363/4611686018427387904), (198374123349/2305843009213693952)), (106607/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592247169237839/1152921504606846976), (198156132733/288230376151711744)), (426471/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193061825664807/144115188075855872), (692566797733/144115188075855872)), (373211/144115188075855872), by norm_num⟩
  | 4 => ⟨((744681911701203/18014398509481984), (259223521415/9007199254740992)), (559915/36028797018963968), by norm_num⟩
  | 3 => ⟨((92901508656335/562949953421312), (161587706421/1125899906842624)), (700067/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222306216209621/4503599627370496), (321898040751/562949953421312)), (350165/1125899906842624), by norm_num⟩
  | 1 => ⟨((2207703734805503/2251799813685248), (3837329879057/2251799813685248)), (525581/562949953421312), by norm_num⟩
  | 0 => ⟨((270522834868639/281474976710656), (3786738019851/1125899906842624)), (263131/140737488355328), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((270522834868639/281474976710656), (3786738019851/1125899906842624)), (1003765106738042787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2079949239652393/2251799813685248), (227462294341/35184372088832)), (2030221/562949953421312), by norm_num⟩
  | 2 => ⟨((7504373713059/8796093022208), (26893191384497/2251799813685248)), (15107247/2251799813685248), by norm_num⟩
  | 3 => ⟨((819339606118419/1125899906842624), (45887772668285/2251799813685248)), (26138303/2251799813685248), by norm_num⟩
  | 4 => ⟨((1191564124230687/2251799813685248), (8348359688811/281474976710656)), (39108027/2251799813685248), by norm_num⟩
  | 5 => ⟨((78568516978297/281474976710656), (141363982228325/4503599627370496)), (87417409/4503599627370496), by norm_num⟩
  | 6 => ⟨((1385831237083401/18014398509481984), (157836530516787/9007199254740992)), (108579613/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-683314569/8388608)), (1/8388608), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1390436359/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((249500475422501/9007199254740992), (-316238459239589/4503599627370496)), (96141727/4503599627370496), by norm_num⟩
  | 1 => ⟨((-356405557/4294967296), (112934799/536870912)), (69/1073741824), by norm_num⟩
  | 2 => ⟨((533847815/4294967296), (-1353289689/4294967296)), (415/4294967296), by norm_num⟩
  | 3 => ⟨((-66636047/536870912), (337841133/1073741824)), (417/4294967296), by norm_num⟩
  | 4 => ⟨((399247513/4294967296), (-506040793/2147483648)), (157/2147483648), by norm_num⟩
  | 5 => ⟨((-59801933/1073741824), (303192547/2147483648)), (189/4294967296), by norm_num⟩
  | 6 => ⟨((238867441/8589934592), (-1211044931/17179869184)), (379/17179869184), by norm_num⟩
  | 7 => ⟨((-102226129/8589934592), (32392557/1073741824)), (327/34359738368), by norm_num⟩
  | 8 => ⟨((153121057/34359738368), (-194078857/17179869184)), (247/68719476736), by norm_num⟩
  | 9 => ⟨((-407741949/274877906944), (258403687/68719476736)), (331/274877906944), by norm_num⟩
  | 10 => ⟨((244297143/549755813888), (-154821653/137438953472)), (399/1099511627776), by norm_num⟩
  | 11 => ⟨((-532253699/4398046511104), (168656081/549755813888)), (437/4398046511104), by norm_num⟩
  | 12 => ⟨((33218533/1099511627776), (-168416155/2199023255552)), (219/8796093022208), by norm_num⟩
  | 13 => ⟨((-489914247/70368744177664), (1241919289/70368744177664)), (203/35184372088832), by norm_num⟩
  | 14 => ⟨((13104035/8796093022208), (-1062987913/281474976710656)), (349/281474976710656), by norm_num⟩
  | 15 => ⟨((-167493037/562949953421312), (424590293/562949953421312)), (35/140737488355328), by norm_num⟩
  | 16 => ⟨((501764297/9007199254740992), (-317989711/2251799813685248)), (421/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1556694217337/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888991314909231/316912650057057350374175801344), (-920359245999/316912650057057350374175801344)), (184763/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888857571984235/39614081257132168796771975168), (-1035172461891/19807040628566084398385987584)), (103941/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944288768800309/1237940039285380274899124224), (-2199161800151/2475880078570760549798248448)), (220901/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885121983366329/77371252455336267181195264), (-2198509948247/154742504910672534362390528)), (55233/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774333032792293/4835703278458516698824704), (-515102684505/2417851639229258349412352)), (51789/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258012434602085/604462909807314587353088), (-901083671665/302231454903657293676544)), (90647/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943265499001179/37778931862957161709568), (-2927224942115/75557863725914323419136)), (294663/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296593980626997/4722366482869645213696), (-548571111715/1180591620717411303424)), (110525/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620148596985863/590295810358705651712), (-753824770067/147573952589676412928)), (152015/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821850981312731/73786976294838206464), (-941590697275/18446744073709551616)), (380167/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820831332807299/9223372036854775808), (-4233364909881/9223372036854775808)), (427867/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592081121671521/1152921504606846976), (-4228628217825/1152921504606846976)), (214045/576460752303423488), by norm_num⟩
  | 5 => ⟨((596457779372941/72057594037927936), (-1847363781971/72057594037927936)), (374831/144115188075855872), by norm_num⟩
  | 4 => ⟨((186142809960903/4503599627370496), (-5531463701707/36028797018963968)), (562749/36028797018963968), by norm_num⟩
  | 3 => ⟨((743072037154697/4503599627370496), (-3447884281749/4503599627370496)), (704319/9007199254740992), by norm_num⟩
  | 2 => ⟨((555433999782455/1125899906842624), (-13736002907559/4503599627370496)), (44103/140737488355328), by norm_num⟩
  | 1 => ⟨((1103411706894219/1125899906842624), (-10232844469797/1125899906842624)), (530903/562949953421312), by norm_num⟩
  | 0 => ⟨((1081161702799205/1125899906842624), (-20190613394069/1125899906842624)), (4274039/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081161702799205/1125899906842624), (-20190613394069/1125899906842624)), (16304164895064543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1037839118405557/1125899906842624), (-38776658253589/1125899906842624)), (2090427/562949953421312), by norm_num⟩
  | 2 => ⟨((477665199157821/562949953421312), (-17871896325791/281474976710656)), (15991381/2251799813685248), by norm_num⟩
  | 3 => ⟨((1612125002547497/2251799813685248), (-242629963559775/2251799813685248)), (29168203/2251799813685248), by norm_num⟩
  | 4 => ⟨((564010554842509/1125899906842624), (-86852709606933/562949953421312)), (24025169/1125899906842624), by norm_num⟩
  | 5 => ⟨((31967132642029/140737488355328), (-696130725472437/4503599627370496)), (31483707/1125899906842624), by norm_num⟩
  | 6 => ⟨((249500475422501/9007199254740992), (-316238459239589/4503599627370496)), (96141727/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1390436359/16777216)), (1/8388608), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-353270445/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-67402238688041/1125899906842624), (-732685910172507/18014398509481984)), (119077407/4503599627370496), by norm_num⟩
  | 1 => ⟨((391402489/2147483648), (531835245/4294967296)), (87/1073741824), by norm_num⟩
  | 2 => ⟨((-297908415/1073741824), (-101199021/536870912)), (133/1073741824), by norm_num⟩
  | 3 => ⟨((151164809/536870912), (410803587/2147483648)), (271/2147483648), by norm_num⟩
  | 4 => ⟨((-460224653/2147483648), (-625350369/4294967296)), (207/2147483648), by norm_num⟩
  | 5 => ⟨((560465713/4294967296), (190389323/2147483648)), (253/4294967296), by norm_num⟩
  | 6 => ⟨((-1137566959/17179869184), (-772859421/17179869184)), (129/4294967296), by norm_num⟩
  | 7 => ⟨((494764019/17179869184), (672282243/34359738368)), (451/34359738368), by norm_num⟩
  | 8 => ⟨((-753160079/68719476736), (-511694593/68719476736)), (345/68719476736), by norm_num⟩
  | 9 => ⟨((509558391/137438953472), (346192371/137438953472)), (469/274877906944), by norm_num⟩
  | 10 => ⟨((-310272391/274877906944), (-843192353/1099511627776)), (573/1099511627776), by norm_num⟩
  | 11 => ⟨((343502275/1099511627776), (233374367/1099511627776)), (319/2199023255552), by norm_num⟩
  | 12 => ⟨((-5446877/68719476736), (-473675665/8796093022208)), (163/4398046511104), by norm_num⟩
  | 13 => ⟨((653120561/35184372088832), (443728059/35184372088832)), (307/35184372088832), by norm_num⟩
  | 14 => ⟨((-142031443/35184372088832), (-771965733/281474976710656)), (537/281474976710656), by norm_num⟩
  | 15 => ⟨((28827861/35184372088832), (313368933/562949953421312)), (219/562949953421312), by norm_num⟩
  | 16 => ⟨((-702136557/4503599627370496), (-238514687/2251799813685248)), (335/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-3314923307723/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111119462085195/39614081257132168796771975168), (-1959735070221/316912650057057350374175801344)), (46293/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472194273905365/9903520314283042199192993792), (-4408386250131/39614081257132168796771975168)), (208369/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472122895359307/618970019642690137449562112), (-2341327089095/1237940039285380274899124224)), (221449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885078752429289/77371252455336267181195264), (-1170310325561/38685626227668133590597632)), (110757/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774292235352695/4835703278458516698824704), (-548395369627/1208925819614629174706176)), (103869/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257940502711723/604462909807314587353088), (-3837267292005/604462909807314587353088)), (11365/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1886413104049081/75557863725914323419136), (-6232747291079/75557863725914323419136)), (147809/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162063085271631/590295810358705651712), (-4672100912539/4722366482869645213696)), (221827/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620024386871987/590295810358705651712), (-6420143842779/590295810358705651712)), (305195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455423396261053/18446744073709551616), (-8019190701057/73786976294838206464)), (381769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227581416740427/1152921504606846976), (-1126669978607/1152921504606846976)), (429869/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397974367788919/288230376151711744), (-9003080649685/1152921504606846976)), (53793/144115188075855872), by norm_num⟩
  | 5 => ⟨((596375384043673/72057594037927936), (-7866142432901/144115188075855872)), (188543/72057594037927936), by norm_num⟩
  | 4 => ⟨((372221782450881/9007199254740992), (-11776134726369/36028797018963968)), (566699/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485810665281439/9007199254740992), (-7339920907031/4503599627370496)), (88781/1125899906842624), by norm_num⟩
  | 2 => ⟨((555256693974449/1125899906842624), (-29238949870433/4503599627370496)), (1426133/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205654472155789/2251799813685248), (-21778725607003/1125899906842624)), (2153335/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079785252900057/1125899906842624), (-85916170569181/2251799813685248)), (4363459/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079785252900057/1125899906842624), (-85916170569181/2251799813685248)), (16645275124556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2067840645894709/2251799813685248), (-10299651572315/140737488355328)), (2175613/562949953421312), by norm_num⟩
  | 2 => ⟨((1886849669508543/2251799813685248), (-302663326007551/2251799813685248)), (17256775/2251799813685248), by norm_num⟩
  | 3 => ⟨((385091579337365/562949953421312), (-507221106582371/2251799813685248)), (33558875/2251799813685248), by norm_num⟩
  | 4 => ⟨((469725400944941/1125899906842624), (-346969700983115/1125899906842624)), (30515471/1125899906842624), by norm_num⟩
  | 5 => ⟨((178086841082911/2251799813685248), (-1158045974918593/4503599627370496)), (177080297/4503599627370496), by norm_num⟩
  | 6 => ⟨((-67402238688041/1125899906842624), (-732685910172507/18014398509481984)), (119077407/4503599627370496), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-353270445/4194304)), (1/8388608), by norm_num⟩, -13, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile042Terms2
