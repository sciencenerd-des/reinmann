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
namespace Reinmann.XiBand97.Tile065Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨65,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (81383/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (81383/2560))
  have he : value ((69/80), (81383/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2862621597/1073741824), (-26377800435/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-100285508193627/2251799813685248), (961828657577359/18014398509481984)), (1792129/4503599627370496), by norm_num⟩
  | 1 => ⟨((37840181065/274877906944), (-45365191855/274877906944)), (85/68719476736), by norm_num⟩
  | 2 => ⟨((-58482803057/274877906944), (17528216741/68719476736)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((30128804507/137438953472), (-9030077013/34359738368)), (273/137438953472), by norm_num⟩
  | 4 => ⟨((-11641176725/68719476736), (55824702809/274877906944)), (53/34359738368), by norm_num⟩
  | 5 => ⟨((57573394343/549755813888), (-17255652633/137438953472)), (527/549755813888), by norm_num⟩
  | 6 => ⟨((-59320602033/1099511627776), (17779318283/274877906944)), (545/1099511627776), by norm_num⟩
  | 7 => ⟨((26194642749/1099511627776), (-62807574405/2199023255552)), (483/2199023255552), by norm_num⟩
  | 8 => ⟨((-20242188197/2199023255552), (6066902465/549755813888)), (375/4398046511104), by norm_num⟩
  | 9 => ⟨((55617300503/17592186044416), (-66677522061/17592186044416)), (517/17592186044416), by norm_num⟩
  | 10 => ⟨((-34383087399/35184372088832), (41220610275/35184372088832)), (321/35184372088832), by norm_num⟩
  | 11 => ⟨((9661780257/35184372088832), (-5791575287/17592186044416)), (363/140737488355328), by norm_num⟩
  | 12 => ⟨((-39819963933/562949953421312), (1491833757/17592186044416)), (47/70368744177664), by norm_num⟩
  | 13 => ⟨((18936184463/1125899906842624), (-45403780689/2251799813685248)), (359/2251799813685248), by norm_num⟩
  | 14 => ⟨((-16723585737/4503599627370496), (40098575329/9007199254740992)), (319/9007199254740992), by norm_num⟩
  | 15 => ⟨((55139534385/72057594037927936), (-66104745953/72057594037927936)), (33/4503599627370496), by norm_num⟩
  | 16 => ⟨((-42609660411/288230376151711744), (51083144027/288230376151711744)), (205/144115188075855872), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973031325/10141204801825835211973625643008), (368964889993/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777851304751987/633825300114114700748351602688), (3489796622205/633825300114114700748351602688)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472177401514147/9903520314283042199192993792), (1962553077569/19807040628566084398385987584)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888420018833445/2475880078570760549798248448), (1042322549609/618970019642690137449562112)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770086105299955/154742504910672534362390528), (4168013630619/154742504910672534362390528)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548517706731333/9671406556917033397649408), (3906156846999/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628941128603941/302231454903657293676544), (213533236463/37778931862957161709568)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886318779136001/75557863725914323419136), (5549323671847/75557863725914323419136)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296434221720667/4722366482869645213696), (259985677751/295147905179352825856)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619927963451027/590295810358705651712), (2858038097121/295147905179352825856)), (2383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821573744354983/73786976294838206464), (7139685470105/73786976294838206464)), (5961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113782341149311/576460752303423488), (2006178269969/2305843009213693952)), (6711/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795882387412801/576460752303423488), (2003857444843/288230376151711744)), (3359/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192635982180483/144115188075855872), (1750767099097/36028797018963968)), (2943/72057594037927936), by norm_num⟩
  | 4 => ⟨((744358794830725/18014398509481984), (2620941222251/9007199254740992)), (8843/36028797018963968), by norm_num⟩
  | 3 => ⟨((371400834947537/2251799813685248), (13068302218205/9007199254740992)), (1385/1125899906842624), by norm_num⟩
  | 2 => ⟨((2220625851852791/4503599627370496), (13013820453621/2251799813685248)), (22237/4503599627370496), by norm_num⟩
  | 1 => ⟨((551271787932975/562949953421312), (38769920084517/2251799813685248)), (33551/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079285311558671/1125899906842624), (76458872490771/2251799813685248)), (16973/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079285311558671/1125899906842624), (76458872490771/2251799813685248)), (64746858836936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2066605187335315/2251799813685248), (146586632641335/2251799813685248)), (67387/1125899906842624), by norm_num⟩
  | 2 => ⟨((1887099081200153/2251799813685248), (67265458849741/562949953421312)), (264927/2251799813685248), by norm_num⟩
  | 3 => ⟨((193664455083631/281474976710656), (450969343972407/2251799813685248)), (507351/2251799813685248), by norm_num⟩
  | 4 => ⟨((975666483257793/2251799813685248), (155141201680633/562949953421312)), (450683/1125899906842624), by norm_num⟩
  | 5 => ⟨((62930150780411/562949953421312), (1075520619424219/4503599627370496)), (2555803/4503599627370496), by norm_num⟩
  | 6 => ⟨((-100285508193627/2251799813685248), (961828657577359/18014398509481984)), (1792129/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2862621597/1073741824), (-26377800435/268435456)), (1/536870912), by norm_num⟩, -16, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1451894239/536870912), (-53514270309/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((792939281217541/18014398509481984), (907868501166757/18014398509481984)), (4500055/18014398509481984), by norm_num⟩
  | 1 => ⟨((-4742157993/34359738368), (-1357372491/8589934592)), (217/274877906944), by norm_num⟩
  | 2 => ⟨((7434504479/34359738368), (34048268755/137438953472)), (343/274877906944), by norm_num⟩
  | 3 => ⟨((-31081127723/137438953472), (-71172099829/274877906944)), (361/274877906944), by norm_num⟩
  | 4 => ⟨((12181837025/68719476736), (55789926837/274877906944)), (285/274877906944), by norm_num⟩
  | 5 => ⟨((-30556863625/274877906944), (-34985798581/274877906944)), (359/549755813888), by norm_num⟩
  | 6 => ⟨((63873912769/1099511627776), (18282961515/274877906944)), (189/549755813888), by norm_num⟩
  | 7 => ⟨((-57221795439/2199023255552), (-32757782903/1099511627776)), (341/2199023255552), by norm_num⟩
  | 8 => ⟨((11213663039/1099511627776), (25677959705/2199023255552)), (269/4398046511104), by norm_num⟩
  | 9 => ⟨((-62507334397/17592186044416), (-2236474837/549755813888)), (377/17592186044416), by norm_num⟩
  | 10 => ⟨((39198277091/35184372088832), (44879705059/35184372088832)), (119/17592186044416), by norm_num⟩
  | 11 => ⟨((-22346540199/70368744177664), (-25585464659/70368744177664)), (273/140737488355328), by norm_num⟩
  | 12 => ⟨((46711631693/562949953421312), (53482050967/562949953421312)), (287/562949953421312), by norm_num⟩
  | 13 => ⟨((-45065861843/2251799813685248), (-51597741989/2251799813685248)), (279/2251799813685248), by norm_num⟩
  | 14 => ⟨((10093124939/2251799813685248), (23112060223/4503599627370496)), (63/2251799813685248), by norm_num⟩
  | 15 => ⟨((-33756730525/36028797018963968), (-9662364153/9007199254740992)), (53/9007199254740992), by norm_num⟩
  | 16 => ⟨((52922016655/288230376151711744), (15148143457/72057594037927936)), (167/144115188075855872), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031362285/10141204801825835211973625643008), (277739244379/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888898933740241/316912650057057350374175801344), (1313393379959/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944324905594031/19807040628566084398385987584), (738611637949/19807040628566084398385987584)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888356916945019/2475880078570760549798248448), (784558474217/1237940039285380274899124224)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770023486804159/154742504910672534362390528), (392157578341/38685626227668133590597632)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387114878771621/2417851639229258349412352), (1470074075625/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257831852252405/604462909807314587353088), (80362387847/37778931862957161709568)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1886237831479809/75557863725914323419136), (1044226966495/37778931862957161709568)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648187175173423/2361183241434822606848), (782746905593/2361183241434822606848)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404961750613087/147573952589676412928), (2151179127613/590295810358705651712)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910737291556149/36893488147419103232), (1343456616351/36893488147419103232)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910204350898521/4611686018427387904), (1509973291037/4611686018427387904)), (3339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591659510199449/1152921504606846976), (1508206005533/576460752303423488)), (6681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596273896698875/72057594037927936), (658847380331/36028797018963968)), (5849/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488593115328947/36028797018963968), (1972577898011/18014398509481984)), (4389/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485461352440989/9007199254740992), (4917600195765/9007199254740992)), (10983/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110191227471843/2251799813685248), (4896893841887/2251799813685248)), (10997/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204822667866721/2251799813685248), (14587571857901/2251799813685248)), (16533/1125899906842624), by norm_num⟩
  | 0 => ⟨((539609782288719/562949953421312), (28765228171549/2251799813685248)), (519/17592186044416), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((539609782288719/562949953421312), (28765228171549/2251799813685248)), (1979827947968239/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1034290883142907/1125899906842624), (27572608216415/1125899906842624)), (64527/1125899906842624), by norm_num⟩
  | 2 => ⟨((1898920811222877/2251799813685248), (101316634380699/2251799813685248)), (243429/2251799813685248), by norm_num⟩
  | 3 => ⟨((1596782789056447/2251799813685248), (85439329188727/1125899906842624)), (216235/1125899906842624), by norm_num⟩
  | 4 => ⟨((139916731508483/281474976710656), (121172450168927/1125899906842624)), (339489/1125899906842624), by norm_num⟩
  | 5 => ⟨((1060642437580589/4503599627370496), (60232896631301/562949953421312)), (1642331/4503599627370496), by norm_num⟩
  | 6 => ⟨((792939281217541/18014398509481984), (907868501166757/18014398509481984)), (4500055/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1451894239/536870912), (-53514270309/536870912)), (1/536870912), by norm_num⟩, -16, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-735800759/268435456), (-108481291957/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1019645404767239/18014398509481984), (-557182066882961/18014398509481984)), (1730689/9007199254740992), by norm_num⟩
  | 1 => ⟨((-49445922611/274877906944), (27019570951/274877906944)), (85/137438953472), by norm_num⟩
  | 2 => ⟨((39285450937/137438953472), (-21467412739/137438953472)), (273/274877906944), by norm_num⟩
  | 3 => ⟨((-41617092609/137438953472), (11370765547/68719476736)), (291/274877906944), by norm_num⟩
  | 4 => ⟨((66130680287/274877906944), (-36136905001/274877906944)), (233/274877906944), by norm_num⟩
  | 5 => ⟨((-21016686179/137438953472), (22969005871/274877906944)), (149/274877906944), by norm_num⟩
  | 6 => ⟨((44528106675/549755813888), (-380191339/8589934592)), (159/549755813888), by norm_num⟩
  | 7 => ⟨((-80864411415/2199023255552), (44188106649/2199023255552)), (291/2199023255552), by norm_num⟩
  | 8 => ⟨((64247863109/4398046511104), (-17554022699/2199023255552)), (233/4398046511104), by norm_num⟩
  | 9 => ⟨((-22687018605/4398046511104), (6198625453/2199023255552)), (83/4398046511104), by norm_num⟩
  | 10 => ⟨((57680453101/35184372088832), (-15759652291/17592186044416)), (213/35184372088832), by norm_num⟩
  | 11 => ⟨((-33329379075/70368744177664), (36425471511/140737488355328)), (31/17592186044416), by norm_num⟩
  | 12 => ⟨((70615040555/562949953421312), (-38587369753/562949953421312)), (265/562949953421312), by norm_num⟩
  | 13 => ⟨((-17262953855/562949953421312), (18866575115/1125899906842624)), (261/2251799813685248), by norm_num⟩
  | 14 => ⟨((62700110425/9007199254740992), (-8565570187/2251799813685248)), (239/9007199254740992), by norm_num⟩
  | 15 => ⟨((-26568576813/18014398509481984), (29036632685/36028797018963968)), (205/36028797018963968), by norm_num⟩
  | 16 => ⟨((84436367307/288230376151711744), (-23069995431/144115188075855872)), (41/36028797018963968), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-162862671575/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777741947582933/633825300114114700748351602688), (-770110047669/633825300114114700748351602688)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888586949351057/39614081257132168796771975168), (-433084837161/19807040628566084398385987584)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472072547370015/618970019642690137449562112), (-115006014155/309485009821345068724781056)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442489207602249/38685626227668133590597632), (-57484934715/9671406556917033397649408)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548397100174711/9671406556917033397649408), (-430983458889/4835703278458516698824704)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257777314603639/604462909807314587353088), (-188478523327/151115727451828646838272)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943074674523541/37778931862957161709568), (-612267578113/37778931862957161709568)), (2299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296308111986439/4722366482869645213696), (-229474582847/1180591620717411303424)), (3449/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404939031274733/147573952589676412928), (-1261293342007/590295810358705651712)), (2371/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910680643297157/36893488147419103232), (-1575392377853/73786976294838206464)), (741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820281655280675/9223372036854775808), (-221329328723/1152921504606846976)), (3335/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397883244439665/288230376151711744), (-1768534808145/1152921504606846976)), (417/72057594037927936), by norm_num⟩
  | 5 => ⟨((596218827232189/72057594037927936), (-772554492243/72057594037927936)), (365/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488429057384069/36028797018963968), (-2312953835569/36028797018963968)), (8763/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485258285565243/9007199254740992), (-1441484536003/4503599627370496)), (5479/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219982306993467/4503599627370496), (-5741342901795/4503599627370496)), (10967/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204237302866887/2251799813685248), (-8550785957751/2251799813685248)), (32945/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157327184970425/2251799813685248), (-16858210397875/2251799813685248)), (33035/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157327184970425/2251799813685248), (-16858210397875/2251799813685248)), (126018528464889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1033345938540231/1125899906842624), (-16150936402187/1125899906842624)), (63793/1125899906842624), by norm_num⟩
  | 2 => ⟨((237042158335515/281474976710656), (-59293031053263/2251799813685248)), (237857/2251799813685248), by norm_num⟩
  | 3 => ⟨((797712865870607/1125899906842624), (-3120825388141/70368744177664)), (206573/1125899906842624), by norm_num⟩
  | 4 => ⟨((1125948208079317/2251799813685248), (-35378243470855/562949953421312)), (155521/562949953421312), by norm_num⟩
  | 5 => ⟨((8657889998679/35184372088832), (-70759522403213/1125899906842624)), (175075/562949953421312), by norm_num⟩
  | 6 => ⟨((1019645404767239/18014398509481984), (-557182066882961/18014398509481984)), (1730689/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-108481291957/1073741824)), (1/536870912), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-745252095/268435456), (-109874730503/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-15782318120181/1125899906842624), (-1092959593663433/18014398509481984)), (3021995/9007199254740992), by norm_num⟩
  | 1 => ⟨((12402666567/274877906944), (53681964319/274877906944)), (149/137438953472), by norm_num⟩
  | 2 => ⟨((-4990330447/68719476736), (-86397788589/274877906944)), (241/137438953472), by norm_num⟩
  | 3 => ⟨((21417672045/274877906944), (23175312751/68719476736)), (519/274877906944), by norm_num⟩
  | 4 => ⟨((-17235206693/274877906944), (-18649613487/68719476736)), (105/68719476736), by norm_num⟩
  | 5 => ⟨((693474877/17179869184), (96049263995/549755813888)), (543/549755813888), by norm_num⟩
  | 6 => ⟨((-23810234845/1099511627776), (-6441055289/68719476736)), (585/1099511627776), by norm_num⟩
  | 7 => ⟨((21897768379/2199023255552), (94779232715/2199023255552)), (135/549755813888), by norm_num⟩
  | 8 => ⟨((-8810774657/2199023255552), (-38135322611/2199023255552)), (437/4398046511104), by norm_num⟩
  | 9 => ⟨((1575599419/1099511627776), (27278415117/4398046511104)), (627/17592186044416), by norm_num⟩
  | 10 => ⟨((-8114654207/17592186044416), (-70244664769/35184372088832)), (405/35184372088832), by norm_num⟩
  | 11 => ⟨((18996410367/140737488355328), (41110700591/70368744177664)), (119/35184372088832), by norm_num⟩
  | 12 => ⟨((-10191181015/281474976710656), (-11027520023/70368744177664)), (1/1099511627776), by norm_num⟩
  | 13 => ⟨((10093583445/1125899906842624), (87375304887/2251799813685248)), (509/2251799813685248), by norm_num⟩
  | 14 => ⟨((-4641427391/2251799813685248), (-80357216169/9007199254740992)), (235/4503599627370496), by norm_num⟩
  | 15 => ⟨((15936190317/36028797018963968), (34487986731/18014398509481984)), (405/36028797018963968), by norm_num⟩
  | 16 => ⟨((-6412077219/72057594037927936), (-111012546737/288230376151711744)), (327/144115188075855872), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-585475734561/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444420984525835/158456325028528675187087900672), (-43254858619/9903520314283042199192993792)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888521496923779/39614081257132168796771975168), (-3113600570995/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888220386648683/2475880078570760549798248448), (-413407945403/309485009821345068724781056)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((442471683968225/38685626227668133590597632), (-413276229769/19342813113834066795298816)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774165538442067/4835703278458516698824704), (-3098452549879/9671406556917033397649408)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628859617434583/302231454903657293676544), (-2710027268405/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886054390091019/75557863725914323419136), (-4401697703277/75557863725914323419136)), (1153/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81014774153637/295147905179352825856), (-3299439723643/4722366482869645213696)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619656680964847/590295810358705651712), (-4533751928067/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821235751265273/73786976294838206464), (-707840822267/9223372036854775808)), (93/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1820138740032617/9223372036854775808), (-795554440663/1152921504606846976)), (6701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591387957702501/1152921504606846976), (-6356778485039/1152921504606846976)), (3353/576460752303423488), by norm_num⟩
  | 5 => ⟨((149038550142095/18014398509481984), (-5553577724515/144115188075855872)), (5873/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488230473622777/36028797018963968), (-129893538427/562949953421312)), (8821/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485001864178907/9007199254740992), (-5180739005061/4503599627370496)), (11047/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219445048275945/4503599627370496), (-20633181070449/4503599627370496)), (5539/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203370929383761/2251799813685248), (-15363086654703/1125899906842624)), (16695/1125899906842624), by norm_num⟩
  | 0 => ⟨((1077677901877961/1125899906842624), (-15140743439705/562949953421312)), (4213/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077677901877961/1125899906842624), (-15140743439705/562949953421312)), (16071320116949037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2061413602924589/2251799813685248), (-115938154173803/2251799813685248)), (132669/2251799813685248), by norm_num⟩
  | 2 => ⟨((470288739809955/562949953421312), (-212271523125059/2251799813685248)), (128283/1125899906842624), by norm_num⟩
  | 3 => ⟨((1551507713922867/2251799813685248), (-88665880955595/562949953421312)), (119261/562949953421312), by norm_num⟩
  | 4 => ⟨((253285167421075/562949953421312), (-244365946614473/1125899906842624)), (807647/2251799813685248), by norm_num⟩
  | 5 => ⟨((699525018452009/4503599627370496), (-879570474413871/4503599627370496)), (2154691/4503599627370496), by norm_num⟩
  | 6 => ⟨((-15782318120181/1125899906842624), (-1092959593663433/18014398509481984)), (3021995/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-109874730503/1073741824)), (1/536870912), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-3017330773/1073741824), (-55606755051/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-134918942380927/2251799813685248), (-52461602761853/9007199254740992)), (5690965/18014398509481984), by norm_num⟩
  | 1 => ⟨((107319076925/549755813888), (10432432027/549755813888)), (71/68719476736), by norm_num⟩
  | 2 => ⟨((-10926747281/34359738368), (-2124366917/68719476736)), (465/274877906944), by norm_num⟩
  | 3 => ⟨((94934393301/274877906944), (4614261665/137438953472)), (507/274877906944), by norm_num⟩
  | 4 => ⟨((-38663177269/137438953472), (-3758427489/137438953472)), (415/274877906944), by norm_num⟩
  | 5 => ⟨((100774691207/549755813888), (1224531959/68719476736)), (543/549755813888), by norm_num⟩
  | 6 => ⟨((-54722278757/549755813888), (-10639048897/1099511627776)), (37/68719476736), by norm_num⟩
  | 7 => ⟨((12735033355/274877906944), (2475932027/549755813888)), (553/2199023255552), by norm_num⟩
  | 8 => ⟨((-82983936171/4398046511104), (-4033412783/2199023255552)), (113/1099511627776), by norm_num⟩
  | 9 => ⟨((120164300067/17592186044416), (11681109533/17592186044416)), (657/17592186044416), by norm_num⟩
  | 10 => ⟨((-9787672251/4398046511104), (-3805818253/17592186044416)), (215/17592186044416), by norm_num⟩
  | 11 => ⟨((92768526767/140737488355328), (9017980563/140737488355328)), (511/140737488355328), by norm_num⟩
  | 12 => ⟨((-100749605299/562949953421312), (-2448454271/140737488355328)), (557/562949953421312), by norm_num⟩
  | 13 => ⟨((50500298497/1125899906842624), (9818215857/2251799813685248)), (35/140737488355328), by norm_num⟩
  | 14 => ⟨((-94019912973/9007199254740992), (-9139627169/9007199254740992)), (131/2251799813685248), by norm_num⟩
  | 15 => ⟨((40843460395/18014398509481984), (3970371685/18014398509481984)), (457/36028797018963968), by norm_num⟩
  | 16 => ⟨((-66535968457/144115188075855872), (-6467927121/144115188075855872)), (187/72057594037927936), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (-3966045599205/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888812085589217/316912650057057350374175801344), (-1171977884181/158456325028528675187087900672)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944226928387195/19807040628566084398385987584), (-329537159003/2475880078570760549798248448)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118009248397489/154742504910672534362390528), (-350032688295/154742504910672534362390528)), (3465/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884906855802657/77371252455336267181195264), (-5598713607537/154742504910672534362390528)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774130983490437/4835703278458516698824704), (-5246872022375/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257658114698243/604462909807314587353088), (-4589091605659/604462909807314587353088)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885953854301451/75557863725914323419136), (-3726836210591/37778931862957161709568)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296159922415801/4722366482869645213696), (-2793552135457/2361183241434822606848)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619549819402763/590295810358705651712), (-3838575912391/295147905179352825856)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821099593552953/73786976294838206464), (-9588768942131/73786976294838206464)), (5975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454995505339917/2305843009213693952), (-10776824130057/9223372036854775808)), (6729/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591226823404437/1152921504606846976), (-10763657680933/1152921504606846976)), (6739/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192162456058167/144115188075855872), (-2350850393927/36028797018963968)), (2953/72057594037927936), by norm_num⟩
  | 4 => ⟨((186000211040971/4503599627370496), (-14075537987219/36028797018963968)), (8879/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484698698220663/9007199254740992), (-8771380021655/4503599627370496)), (11133/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109393749396707/2251799813685248), (-545794278389/70368744177664)), (5593/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101128865574921/1125899906842624), (-26005294767373/1125899906842624)), (16911/1125899906842624), by norm_num⟩
  | 0 => ⟨((269078612161643/281474976710656), (-1601326054305/35184372088832)), (2147/70368744177664), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((269078612161643/281474976710656), (-1601326054305/35184372088832)), (8190155297732331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((16040321922789/17592186044416), (-195942717396369/2251799813685248)), (137611/2251799813685248), by norm_num⟩
  | 2 => ⟨((57968593672507/70368744177664), (-357315942149379/2251799813685248)), (137447/1125899906842624), by norm_num⟩
  | 3 => ⟨((183926860314929/281474976710656), (-294350892647321/1125899906842624)), (540147/2251799813685248), by norm_num⟩
  | 4 => ⟨((201893164907327/562949953421312), (-384680984066097/1125899906842624)), (61771/140737488355328), by norm_num⟩
  | 5 => ⟨((53517867979479/4503599627370496), (-551839188409313/2251799813685248)), (1384263/2251799813685248), by norm_num⟩
  | 6 => ⟨((-134918942380927/2251799813685248), (-52461602761853/9007199254740992)), (5690965/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-55606755051/536870912)), (1/536870912), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-3052282179/1073741824), (-7031359843/67108864)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-118364422747853/4503599627370496), (468434830335737/9007199254740992)), (2951935/9007199254740992), by norm_num⟩
  | 1 => ⟨((11905207157/137438953472), (-23557812243/137438953472)), (299/274877906944), by norm_num⟩
  | 2 => ⟨((-19618810323/137438953472), (77642706073/274877906944)), (495/274877906944), by norm_num⟩
  | 3 => ⟨((10776733055/68719476736), (-42649615509/137438953472)), (273/137438953472), by norm_num⟩
  | 4 => ⟨((-17759177049/137438953472), (35141543779/137438953472)), (451/274877906944), by norm_num⟩
  | 5 => ⟨((23412540171/274877906944), (-23164159103/137438953472)), (299/274877906944), by norm_num⟩
  | 6 => ⟨((-25721304341/549755813888), (50896859695/549755813888)), (165/274877906944), by norm_num⟩
  | 7 => ⟨((24220920883/1099511627776), (-47927927585/1099511627776)), (39/137438953472), by norm_num⟩
  | 8 => ⟨((-9978525497/1099511627776), (78981315323/4398046511104)), (129/1099511627776), by norm_num⟩
  | 9 => ⟨((14616707645/4398046511104), (-57846562393/8796093022208)), (95/2199023255552), by norm_num⟩
  | 10 => ⟨((-38539427133/35184372088832), (76261133163/35184372088832)), (503/35184372088832), by norm_num⟩
  | 11 => ⟨((11547242249/35184372088832), (-45698955295/70368744177664)), (303/70368744177664), by norm_num⟩
  | 12 => ⟨((-12685942235/140737488355328), (50205433867/281474976710656)), (335/281474976710656), by norm_num⟩
  | 13 => ⟨((6432430169/281474976710656), (-50913513789/1125899906842624)), (341/1125899906842624), by norm_num⟩
  | 14 => ⟨((-24228846273/4503599627370496), (47943610207/4503599627370496)), (323/4503599627370496), by norm_num⟩
  | 15 => ⟨((42588973209/36028797018963968), (-84274302939/36028797018963968)), (285/18014398509481984), by norm_num⟩
  | 16 => ⟨((-35091576997/144115188075855872), (69438588621/144115188075855872)), (471/144115188075855872), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197534110748245/1267650600228229401496703205376), (2655665360599/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777580558716285/633825300114114700748351602688), (3138858178547/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472101289982919/9903520314283042199192993792), (3530344793491/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944048363795867/1237940039285380274899124224), (3749903277769/2475880078570760549798248448)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442440754887531/38685626227668133590597632), (3748679705195/154742504910672534362390528)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193526879008183/1208925819614629174706176), (1756543823549/4835703278458516698824704)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257617634975589/604462909807314587353088), (3072652642547/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885889176682721/75557863725914323419136), (4990625949211/75557863725914323419136)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296112377206793/4722366482869645213696), (1870420156117/2361183241434822606848)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809743003702441/295147905179352825856), (5140197661845/590295810358705651712)), (4763/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910511084336559/36893488147419103232), (6420064100559/73786976294838206464)), (5957/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819898129734159/9223372036854775808), (7215451487675/9223372036854775808)), (3353/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591146936549727/1152921504606846976), (3603279825599/576460752303423488)), (839/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192097047473317/144115188075855872), (3147874334413/72057594037927936)), (735/18014398509481984), by norm_num⟩
  | 4 => ⟨((371978131986617/9007199254740992), (2355917911781/9007199254740992)), (8833/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484602842021197/9007199254740992), (5872371835331/4503599627370496)), (1383/1125899906842624), by norm_num⟩
  | 2 => ⟨((1109321139810825/2251799813685248), (11692612606601/2251799813685248)), (11099/2251799813685248), by norm_num⟩
  | 1 => ⟨((275269390657203/281474976710656), (17409072531719/1125899906842624)), (16737/1125899906842624), by norm_num⟩
  | 0 => ⟨((2152878543032463/2251799813685248), (4287704998425/140737488355328)), (67659/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152878543032463/2251799813685248), (4287704998425/140737488355328)), (258098610884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2056212804924531/2251799813685248), (32794773438959/562949953421312)), (133497/2251799813685248), by norm_num⟩
  | 2 => ⟨((934986120636917/1125899906842624), (59892564756391/562949953421312)), (129679/1125899906842624), by norm_num⟩
  | 3 => ⟨((1527401438272729/2251799813685248), (397894814174815/2251799813685248)), (485947/2251799813685248), by norm_num⟩
  | 4 => ⟨((965731881348471/2251799813685248), (539786092669801/2251799813685248)), (415487/1125899906842624), by norm_num⟩
  | 5 => ⟨((284780661636009/2251799813685248), (925994638833577/4503599627370496)), (1111153/2251799813685248), by norm_num⟩
  | 6 => ⟨((-118364422747853/4503599627370496), (468434830335737/9007199254740992)), (2951935/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3052282179/1073741824), (-7031359843/67108864)), (1/536870912), by norm_num⟩, -17, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile065Terms3
