/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile000Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (4561/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4561/320))
  have he : value ((15/16), (4561/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24308947/8388608), (-5774641/131072)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((990569859380567/18014398509481984), (-148301516503651/36028797018963968)), (33328797/9007199254740992), by norm_num⟩
  | 1 => ⟨((-730012295/4294967296), (109292575/8589934592)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((564124749/2147483648), (-84456997/4294967296)), (79/4294967296), by norm_num⟩
  | 3 => ⟨((-145311129/536870912), (43510027/2147483648)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((1796651475/8589934592), (-134491341/8589934592)), (131/8589934592), by norm_num⟩
  | 5 => ⟨((-1110705197/8589934592), (83143689/8589934592)), (83/8589934592), by norm_num⟩
  | 6 => ⟨((572206153/8589934592), (-85666891/17179869184)), (87/17179869184), by norm_num⟩
  | 7 => ⟨((-1010693435/34359738368), (37828571/17179869184)), (39/17179869184), by norm_num⟩
  | 8 => ⟨((1562048157/137438953472), (-116929719/137438953472)), (123/137438953472), by norm_num⟩
  | 9 => ⟨((-1072968259/274877906944), (20079707/68719476736)), (43/137438953472), by norm_num⟩
  | 10 => ⟨((82914761/68719476736), (-99307563/1099511627776)), (27/274877906944), by norm_num⟩
  | 11 => ⟨((-745579771/2199023255552), (55811617/2199023255552)), (123/4398046511104), by norm_num⟩
  | 12 => ⟨((1536412483/17592186044416), (-57505359/8796093022208)), (129/17592186044416), by norm_num⟩
  | 13 => ⟨((-730633263/35184372088832), (54692771/35184372088832)), (125/70368744177664), by norm_num⟩
  | 14 => ⟨((1290524819/281474976710656), (-96604387/281474976710656)), (7/17592186044416), by norm_num⟩
  | 15 => ⟨((-1063751201/1125899906842624), (39814435/562949953421312)), (47/562949953421312), by norm_num⟩
  | 16 => ⟨((1644050061/9007199254740992), (-123068109/9007199254740992)), (147/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (-97327645117/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111093804159837/39614081257132168796771975168), (-57512858487/316912650057057350374175801344)), (23053/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888315815786455/39614081257132168796771975168), (-32342960145/9903520314283042199192993792)), (103739/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944001107879761/1237940039285380274899124224), (-137416979769/2475880078570760549798248448)), (6889/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769668975507459/154742504910672534362390528), (-137371330377/154742504910672534362390528)), (110225/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387031840596067/2417851639229258349412352), (-64368570603/4835703278458516698824704)), (103337/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314385355035765/151115727451828646838272), (-56298270845/302231454903657293676544)), (90421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885766256841019/75557863725914323419136), (-45719643731/18889465931478580854784)), (18367/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648010499715677/2361183241434822606848), (-34269881951/1180591620717411303424)), (110205/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50605052523965/18446744073709551616), (-47088854069/147573952589676412928)), (75767/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820868733813887/73786976294838206464), (-58812759153/18446744073709551616)), (189421/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819728223694013/9223372036854775808), (-132195996227/4611686018427387904)), (213105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590980407790811/1152921504606846976), (-132030310641/576460752303423488)), (213113/1152921504606846976), by norm_num⟩
  | 5 => ⟨((297988780838495/36028797018963968), (-3604387687/2251799813685248)), (186483/144115188075855872), by norm_num⟩
  | 4 => ⟨((743853595837537/18014398509481984), (-345278154629/36028797018963968)), (4371/562949953421312), by norm_num⟩
  | 3 => ⟨((1484359323025495/9007199254740992), (-430300476111/9007199254740992)), (174857/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109097226250735/2251799813685248), (-856721843733/4503599627370496)), (699531/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201580564376433/2251799813685248), (-79714297089/140737488355328)), (1049573/2251799813685248), by norm_num⟩
  | 0 => ⟨((538028271381301/562949953421312), (-314062860435/281474976710656)), (2100319/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((538028271381301/562949953421312), (-314062860435/281474976710656)), (8012081154830168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2056836665528505/2251799813685248), (-300159360309/140737488355328)), (4019365/2251799813685248), by norm_num⟩
  | 2 => ⟨((117421461558969/140737488355328), (-4386740057677/1125899906842624)), (3679937/1125899906842624), by norm_num⟩
  | 3 => ⟨((1567457156299863/2251799813685248), (-1829993682107/281474976710656)), (12338475/2251799813685248), by norm_num⟩
  | 4 => ⟨((1090997340787127/2251799813685248), (-5095367138001/562949953421312)), (34675669/4503599627370496), by norm_num⟩
  | 5 => ⟨((528403895458605/2251799813685248), (-78998596079219/9007199254740992)), (68456893/9007199254740992), by norm_num⟩
  | 6 => ⟨((990569859380567/18014398509481984), (-148301516503651/36028797018963968)), (33328797/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-5774641/131072)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-98634119/33554432), (-374891849/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((723622754326185/18014398509481984), (-309915444064325/9007199254740992)), (1637717/281474976710656), by norm_num⟩
  | 1 => ⟨((-540951481/4294967296), (926721651/8589934592)), (159/8589934592), by norm_num⟩
  | 2 => ⟨((53004695/268435456), (-363216297/2147483648)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((-886378211/4294967296), (189810433/1073741824)), (133/4294967296), by norm_num⟩
  | 4 => ⟨((347404219/2147483648), (-595149515/4294967296)), (53/2147483648), by norm_num⟩
  | 5 => ⟨((-871427135/8589934592), (746435145/8589934592)), (135/8589934592), by norm_num⟩
  | 6 => ⟨((455392457/8589934592), (-780147693/17179869184)), (143/17179869184), by norm_num⟩
  | 7 => ⟨((-407965833/17179869184), (349449797/17179869184)), (65/17179869184), by norm_num⟩
  | 8 => ⟨((639587255/68719476736), (-547848909/68719476736)), (13/8589934592), by norm_num⟩
  | 9 => ⟨((-111412341/34359738368), (381728241/137438953472)), (147/274877906944), by norm_num⟩
  | 10 => ⟨((558932401/549755813888), (-957525353/1099511627776)), (187/1099511627776), by norm_num⟩
  | 11 => ⟨((-318641693/1099511627776), (136468873/549755813888)), (27/549755813888), by norm_num⟩
  | 12 => ⟨((666066123/8796093022208), (-71316227/1099511627776)), (115/8796093022208), by norm_num⟩
  | 13 => ⟨((-160649729/8796093022208), (137607149/8796093022208)), (113/35184372088832), by norm_num⟩
  | 14 => ⟨((575675767/140737488355328), (-986208959/281474976710656)), (205/281474976710656), by norm_num⟩
  | 15 => ⟨((-240670405/281474976710656), (824600663/1125899906842624)), (173/1125899906842624), by norm_num⟩
  | 16 => ⟨((754620663/4503599627370496), (-161595663/1125899906842624)), (137/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (-230657947905/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777436082206081/633825300114114700748351602688), (-1090328182301/633825300114114700748351602688)), (23077/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888242917402251/39614081257132168796771975168), (-1226310505673/39614081257132168796771975168)), (51927/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((943962368921955/1237940039285380274899124224), (-1302564484047/2475880078570760549798248448)), (110353/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769591471343169/154742504910672534362390528), (-1302125504403/154742504910672534362390528)), (55181/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548054674378469/9671406556917033397649408), (-152534556233/1208925819614629174706176)), (51737/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257477790328419/604462909807314587353088), (-266818978573/151115727451828646838272)), (90549/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471415701584723/18889465931478580854784), (-1733450140425/75557863725914323419136)), (18395/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1295943366097597/4722366482869645213696), (-162415503525/590295810358705651712)), (55193/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619254861232685/590295810358705651712), (-892665322619/295147905179352825856)), (75903/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820735099138623/73786976294838206464), (-2229805073635/73786976294838206464)), (47449/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909788866777709/4611686018427387904), (-1252989123535/4611686018427387904)), (213575/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590829729452433/1152921504606846976), (-2502791580917/1152921504606846976)), (213641/1152921504606846976), by norm_num⟩
  | 5 => ⟨((297955767264759/36028797018963968), (-2186363002691/144115188075855872)), (187011/144115188075855872), by norm_num⟩
  | 4 => ⟨((371877172791989/9007199254740992), (-1636199321677/18014398509481984)), (70167/9007199254740992), by norm_num⟩
  | 3 => ⟨((742055234742137/4503599627370496), (-254876446263/562949953421312)), (87775/2251799813685248), by norm_num⟩
  | 2 => ⟨((554423645857231/1125899906842624), (-507421303929/281474976710656)), (702999/4503599627370496), by norm_num⟩
  | 1 => ⟨((1100412715721225/1125899906842624), (-12085266689005/2251799813685248)), (1056511/2251799813685248), by norm_num⟩
  | 0 => ⟨((67205686030627/70368744177664), (-23801658045525/2251799813685248)), (2121153/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((67205686030627/70368744177664), (-23801658045525/2251799813685248)), (8091556557662200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2053662225857269/2251799813685248), (-22731779233935/1125899906842624)), (2048229/1125899906842624), by norm_num⟩
  | 2 => ⟨((1872041012324953/2251799813685248), (-82926370373675/2251799813685248)), (3818715/1125899906842624), by norm_num⟩
  | 3 => ⟨((1553273407194703/2251799813685248), (-34470552266523/562949953421312)), (828833/140737488355328), by norm_num⟩
  | 4 => ⟨((265748176122715/562949953421312), (-190220078504329/2251799813685248)), (19919151/2251799813685248), by norm_num⟩
  | 5 => ⟨((971462742724505/4503599627370496), (-179591946378981/2251799813685248)), (44343081/4503599627370496), by norm_num⟩
  | 6 => ⟨((723622754326185/18014398509481984), (-309915444064325/9007199254740992)), (1637717/281474976710656), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-374891849/8388608)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-99972929/33554432), (-1519921767/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((231730571179573/18014398509481984), (-885716004332871/18014398509481984)), (34211761/4503599627370496), by norm_num⟩
  | 1 => ⟨((-87791947/2147483648), (335556643/2147483648)), (209/8589934592), by norm_num⟩
  | 2 => ⟨((279007533/4294967296), (-533208537/2147483648)), (21/536870912), by norm_num⟩
  | 3 => ⟨((-147783493/2147483648), (1129710289/4294967296)), (45/1073741824), by norm_num⟩
  | 4 => ⟨((58707987/1073741824), (-224392507/1073741824)), (145/4294967296), by norm_num⟩
  | 5 => ⟨((-298523429/8589934592), (570505173/4294967296)), (93/4294967296), by norm_num⟩
  | 6 => ⟨((39530147/2147483648), (-1208730767/17179869184)), (199/17179869184), by norm_num⟩
  | 7 => ⟨((-71787963/8589934592), (1097546127/34359738368)), (183/34359738368), by norm_num⟩
  | 8 => ⟨((228146011/68719476736), (-13625237/1073741824)), (147/68719476736), by norm_num⟩
  | 9 => ⟨((-5035141/4294967296), (615846921/137438953472)), (209/274877906944), by norm_num⟩
  | 10 => ⟨((204824949/549755813888), (-1565755733/1099511627776)), (67/274877906944), by norm_num⟩
  | 11 => ⟨((-236707169/2199023255552), (904737455/2199023255552)), (157/2199023255552), by norm_num⟩
  | 12 => ⟨((125378021/4398046511104), (-479217389/4398046511104)), (21/1099511627776), by norm_num⟩
  | 13 => ⟨((-245204985/35184372088832), (234304409/8796093022208)), (83/17592186044416), by norm_num⟩
  | 14 => ⟨((445299795/281474976710656), (-212752007/35184372088832)), (19/17592186044416), by norm_num⟩
  | 15 => ⟨((-377383125/1125899906842624), (1442426305/1125899906842624)), (65/281474976710656), by norm_num⟩
  | 16 => ⟨((299835971/4503599627370496), (-1146027111/4503599627370496)), (209/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (-856402911511/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777373102596155/633825300114114700748351602688), (-2023989771719/633825300114114700748351602688)), (5775/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888171998941527/39614081257132168796771975168), (-71137694471/1237940039285380274899124224)), (103963/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887849294883465/2475880078570760549798248448), (-1208973405881/1237940039285380274899124224)), (27619/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769515924939337/154742504910672534362390528), (-2417120607039/154742504910672534362390528)), (27623/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1547983739829367/9671406556917033397649408), (-2265173100455/9671406556917033397649408)), (103605/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314353903232469/151115727451828646838272), (-990574707515/302231454903657293676544)), (5667/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((235695195338645/9444732965739290427392), (-1608862114175/37778931862957161709568)), (147375/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((161983406744763/590295810358705651712), (-602963984931/1180591620717411303424)), (3455/147573952589676412928), by norm_num⟩
  | 9 => ⟨((809574957997055/295147905179352825856), (-828492022353/147573952589676412928)), (38017/147573952589676412928), by norm_num⟩
  | 8 => ⟨((56893858809527/2305843009213693952), (-2069481148333/36893488147419103232)), (47539/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819429066535133/9223372036854775808), (-4651527839301/9223372036854775808)), (26753/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1590680317540887/1152921504606846976), (-1161382257097/288230376151711744)), (214147/1152921504606846976), by norm_num⟩
  | 5 => ⟨((297922874645645/36028797018963968), (-2029049507595/72057594037927936)), (187517/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487309672698949/36028797018963968), (-6073695161931/36028797018963968)), (281553/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483858803071867/9007199254740992), (-3784315196047/4503599627370496)), (352429/9007199254740992), by norm_num⟩
  | 2 => ⟨((2217182636346059/4503599627370496), (-15067013899571/4503599627370496)), (706325/4503599627370496), by norm_num⟩
  | 1 => ⟨((1100018102024663/1125899906842624), (-11212833615903/1125899906842624)), (531585/1125899906842624), by norm_num⟩
  | 0 => ⟨((2148919635252543/2251799813685248), (-44156484055291/2251799813685248)), (133823/140737488355328), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2148919635252543/2251799813685248), (-44156484055291/2251799813685248)), (510494232714605287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((256234245137865/281474976710656), (-84278127241549/2251799813685248)), (1042665/562949953421312), by norm_num⟩
  | 2 => ⟨((1862901146088639/2251799813685248), (-76720646956727/1125899906842624)), (494095/140737488355328), by norm_num⟩
  | 3 => ⟨((1530711757089755/2251799813685248), (-253882215063237/2251799813685248)), (7078887/1125899906842624), by norm_num⟩
  | 4 => ⟨((1011911578604425/2251799813685248), (-345164334015357/2251799813685248)), (22440609/2251799813685248), by norm_num⟩
  | 5 => ⟨((401823741141809/2251799813685248), (-620438431495929/4503599627370496)), (1690515/140737488355328), by norm_num⟩
  | 6 => ⟨((231730571179573/18014398509481984), (-885716004332871/18014398509481984)), (34211761/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-1519921767/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-50628539/16777216), (-1539445111/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-564299027550901/36028797018963968), (-208689532379199/4503599627370496)), (311071269/36028797018963968), by norm_num⟩
  | 1 => ⟨((433065533/8589934592), (1281253225/8589934592)), (15/536870912), by norm_num⟩
  | 2 => ⟨((-87124011/1073741824), (-515524379/2147483648)), (195/4294967296), by norm_num⟩
  | 3 => ⟨((186960915/2147483648), (1106272641/4294967296)), (211/4294967296), by norm_num⟩
  | 4 => ⟨((-300901985/4294967296), (-890238565/4294967296)), (171/4294967296), by norm_num⟩
  | 5 => ⟨((193713225/4294967296), (573113479/4294967296)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((-415692545/17179869184), (-614927041/8589934592)), (15/1073741824), by norm_num⟩
  | 7 => ⟨((47787953/4294967296), (1131070735/34359738368)), (111/17179869184), by norm_num⟩
  | 8 => ⟨((-307646973/68719476736), (-910194061/68719476736)), (181/68719476736), by norm_num⟩
  | 9 => ⟨((440123291/274877906944), (1302134071/274877906944)), (261/274877906944), by norm_num⟩
  | 10 => ⟨((-70835111/137438953472), (-838281577/549755813888)), (85/274877906944), by norm_num⟩
  | 11 => ⟨((331650075/2199023255552), (981208837/2199023255552)), (201/2199023255552), by norm_num⟩
  | 12 => ⟨((-355846803/8796093022208), (-263199117/2199023255552)), (217/8796093022208), by norm_num⟩
  | 13 => ⟨((5506859/549755813888), (1042714185/35184372088832)), (217/35184372088832), by norm_num⟩
  | 14 => ⟨((-324130657/140737488355328), (-479481069/70368744177664)), (201/140737488355328), by norm_num⟩
  | 15 => ⟨((278223023/562949953421312), (823141345/562949953421312)), (87/281474976710656), by norm_num⟩
  | 16 => ⟨((-447782681/4503599627370496), (-165599361/562949953421312)), (141/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (-38604979343/158456325028528675187087900672)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55540994328029/19807040628566084398385987584), (-1459708084101/316912650057057350374175801344)), (11561/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888102943988763/39614081257132168796771975168), (-3283488942699/39614081257132168796771975168)), (26017/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1887775771627795/2475880078570760549798248448), (-1743816521295/1237940039285380274899124224)), (110593/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769442230528607/154742504910672534362390528), (-3486425419033/154742504910672534362390528)), (55309/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((386978617412373/2417851639229258349412352), (-1633620622551/4835703278458516698824704)), (51865/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628677410029085/302231454903657293676544), (-1428777041675/302231454903657293676544)), (45395/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885462434483351/75557863725914323419136), (-4641122854093/75557863725914323419136)), (147581/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((80987038180719/295147905179352825856), (-1739370577579/2361183241434822606848)), (13841/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809523400067949/295147905179352825856), (-4779857291133/590295810358705651712)), (152319/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820473866046515/73786976294838206464), (-2984853973859/36893488147419103232)), (95251/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909641129792933/4611686018427387904), (-838612086693/1152921504606846976)), (214455/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590532277672919/1152921504606846976), (-3350062782889/576460752303423488)), (26829/144115188075855872), by norm_num⟩
  | 5 => ⟨((595780290711131/72057594037927936), (-1463188955543/36028797018963968)), (188003/144115188075855872), by norm_num⟩
  | 4 => ⟨((743555272136221/18014398509481984), (-8759459274231/36028797018963968)), (282405/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483605101957489/9007199254740992), (-5457484680581/4503599627370496)), (353707/9007199254740992), by norm_num⟩
  | 2 => ⟨((554165242114901/1125899906842624), (-21727176259627/4503599627370496)), (709521/4503599627370496), by norm_num⟩
  | 1 => ⟨((549804601905249/562949953421312), (-8083727950693/562949953421312)), (1069573/2251799813685248), by norm_num⟩
  | 0 => ⟨((2147145067280401/2251799813685248), (-15913178691395/562949953421312)), (540107/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2147145067280401/2251799813685248), (-15913178691395/562949953421312)), (2060344698192405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((511388739338151/562949953421312), (-121388776832917/2251799813685248)), (1060545/562949953421312), by norm_num⟩
  | 2 => ⟨((1851656538502421/2251799813685248), (-220541286759561/2251799813685248)), (8164639/2251799813685248), by norm_num⟩
  | 3 => ⟨((375254658170699/562949953421312), (-362702504153559/2251799813685248)), (15026867/2251799813685248), by norm_num⟩
  | 4 => ⟨((471068479588703/1125899906842624), (-483544952394511/2251799813685248)), (6218557/562949953421312), by norm_num⟩
  | 5 => ⟨((580696671958449/4503599627370496), (-404623508986777/2251799813685248)), (62994477/4503599627370496), by norm_num⟩
  | 6 => ⟨((-564299027550901/36028797018963968), (-208689532379199/4503599627370496)), (311071269/36028797018963968), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-1539445111/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-102490855/33554432), (-1558202633/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-82162308928811/2251799813685248), (-67237847165729/2251799813685248)), (9801409/1125899906842624), by norm_num⟩
  | 1 => ⟨((510583371/4294967296), (835675801/8589934592)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((-831764957/4294967296), (-680678109/4294967296)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((903323509/4294967296), (369619165/2147483648)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-735778799/4294967296), (-602127461/4294967296)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((958895343/8589934592), (784715759/8589934592)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((-1041391199/17179869184), (-426113283/8589934592)), (261/17179869184), by norm_num⟩
  | 7 => ⟨((121176895/4294967296), (793324693/34359738368)), (245/34359738368), by norm_num⟩
  | 8 => ⟨((-197403011/17179869184), (-646182109/68719476736)), (201/68719476736), by norm_num⟩
  | 9 => ⟨((1143392119/274877906944), (935699419/274877906944)), (293/274877906944), by norm_num⟩
  | 10 => ⟨((-745056381/549755813888), (-1190859/1073741824)), (193/549755813888), by norm_num⟩
  | 11 => ⟨((882714769/2199023255552), (722373089/2199023255552)), (231/2199023255552), by norm_num⟩
  | 12 => ⟨((-239664161/2199023255552), (-196130105/2199023255552)), (253/8796093022208), by norm_num⟩
  | 13 => ⟨((480522445/17592186044416), (786474851/35184372088832)), (1/137438953472), by norm_num⟩
  | 14 => ⟨((-111827751/17592186044416), (-366058713/70368744177664)), (241/140737488355328), by norm_num⟩
  | 15 => ⟨((777270631/562949953421312), (636082467/562949953421312)), (211/562949953421312), by norm_num⟩
  | 16 => ⟨((-79138211/281474976710656), (-518104521/2251799813685248)), (173/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (-3198901670089/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444313032638291/158456325028528675187087900672), (-3779611876205/633825300114114700748351602688)), (23143/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888035646284243/39614081257132168796771975168), (-2125468804377/19807040628566084398385987584)), (104169/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((471926015601833/618970019642690137449562112), (-4515213082841/2475880078570760549798248448)), (110707/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884685145281203/77371252455336267181195264), (-2256814788119/77371252455336267181195264)), (110739/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547846781010077/9671406556917033397649408), (-4229845870843/9671406556917033397649408)), (103851/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628647673927403/302231454903657293676544), (-924858493979/151115727451828646838272)), (45451/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885365334034249/75557863725914323419136), (-187763422251/2361183241434822606848)), (73889/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((647859692644485/2361183241434822606848), (-4503566750253/4722366482869645213696)), (110889/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1618945465602191/590295810358705651712), (-6187929552659/590295810358705651712)), (9535/36893488147419103232), by norm_num⟩
  | 8 => ⟨((56885819556547/2305843009213693952), (-966025586545/9223372036854775808)), (95417/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819137330847773/9223372036854775808), (-542813480095/576460752303423488)), (214871/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795192843387519/576460752303423488), (-8673509232053/1152921504606846976)), (53775/288230376151711744), by norm_num⟩
  | 5 => ⟨((74464403179949/9007199254740992), (-7576392032871/144115188075855872)), (188471/144115188075855872), by norm_num⟩
  | 4 => ⟨((371727909365685/9007199254740992), (-11338771452829/36028797018963968)), (283223/36028797018963968), by norm_num⟩
  | 3 => ⟨((741675005074765/4503599627370496), (-7064188147235/4503599627370496)), (44367/1125899906842624), by norm_num⟩
  | 2 => ⟨((2216131553244581/4503599627370496), (-219701970063/35184372088832)), (356299/2251799813685248), by norm_num⟩
  | 1 => ⟨((2198376705092577/2251799813685248), (-41846797946819/2251799813685248)), (1075739/2251799813685248), by norm_num⟩
  | 0 => ⟨((2145274321460243/2251799813685248), (-10294660384293/281474976710656)), (1089495/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2145274321460243/2251799813685248), (-10294660384293/281474976710656)), (4156093601707076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((510194019503065/562949953421312), (-156922443541261/2251799813685248)), (4311207/2251799813685248), by norm_num⟩
  | 2 => ⟨((1838592543679303/2251799813685248), (-35554178366119/281474976710656)), (8415255/2251799813685248), by norm_num⟩
  | 3 => ⟨((183160162998607/281474976710656), (-232239639930009/1125899906842624)), (1983503/281474976710656), by norm_num⟩
  | 4 => ⟨((428836588106663/1125899906842624), (-302243920943953/1125899906842624)), (27197345/2251799813685248), by norm_num⟩
  | 5 => ⟨((328801631437831/4503599627370496), (-460478772742991/2251799813685248)), (35320101/2251799813685248), by norm_num⟩
  | 6 => ⟨((-82162308928811/2251799813685248), (-67237847165729/2251799813685248)), (9801409/1125899906842624), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-1558202633/33554432)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-103678063/33554432), (-1576252153/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-810863745200913/18014398509481984), (-241642645316913/36028797018963968)), (280577269/36028797018963968), by norm_num⟩
  | 1 => ⟨((1274335205/8589934592), (94940035/4294967296)), (223/8589934592), by norm_num⟩
  | 2 => ⟨((-1050000237/4294967296), (-78226717/2147483648)), (185/4294967296), by norm_num⟩
  | 3 => ⟨((1153543163/4294967296), (171881665/4294967296)), (205/4294967296), by norm_num⟩
  | 4 => ⟨((-950472521/4294967296), (-70811741/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((626520475/4294967296), (186707157/8589934592)), (113/4294967296), by norm_num⟩
  | 6 => ⟨((-688303093/8589934592), (-205118777/17179869184)), (125/8589934592), by norm_num⟩
  | 7 => ⟨((324076387/8589934592), (96576861/17179869184)), (237/34359738368), by norm_num⟩
  | 8 => ⟨((-133512863/8589934592), (-159150789/68719476736)), (197/68719476736), by norm_num⟩
  | 9 => ⟨((782287317/137438953472), (233126683/274877906944)), (291/274877906944), by norm_num⟩
  | 10 => ⟨((-128914569/68719476736), (-153669503/549755813888)), (97/274877906944), by norm_num⟩
  | 11 => ⟨((618009293/1099511627776), (11510673/137438953472)), (235/2199023255552), by norm_num⟩
  | 12 => ⟨((-169738151/1099511627776), (-202332269/8796093022208)), (65/2199023255552), by norm_num⟩
  | 13 => ⟨((1377056629/35184372088832), (205185893/35184372088832)), (133/17592186044416), by norm_num⟩
  | 14 => ⟨((-324182429/35184372088832), (-193216923/140737488355328)), (63/35184372088832), by norm_num⟩
  | 15 => ⟨((1139682561/562949953421312), (169816389/562949953421312)), (223/562949953421312), by norm_num⟩
  | 16 => ⟨((-469525975/1125899906842624), (-139921779/2251799813685248)), (185/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (-974899855279/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888596974088263/316912650057057350374175801344), (-575905098203/79228162514264337593543950336)), (46327/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1887970008643281/39614081257132168796771975168), (-1295437056225/9903520314283042199192993792)), (52133/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1887634070191491/2475880078570760549798248448), (-5503869982055/2475880078570760549798248448)), (3463/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442325003750549/38685626227668133590597632), (-5501915882047/154742504910672534362390528)), (110855/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547780596924131/9671406556917033397649408), (-2577985293725/4835703278458516698824704)), (103967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257237136374667/604462909807314587353088), (-4509399475109/604462909807314587353088)), (91011/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885270177848773/75557863725914323419136), (-7323885539255/75557863725914323419136)), (147969/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((647823763332149/2361183241434822606848), (-5489513243909/4722366482869645213696)), (27761/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404711465673425/147573952589676412928), (-942819658803/73786976294838206464)), (19099/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455055132152453/18446744073709551616), (-36796549793/288230376151711744)), (191153/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1818994284218783/9223372036854775808), (-10586030201229/9223372036854775808)), (215271/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590240599345395/1152921504606846976), (-10571822988951/1152921504606846976)), (107775/576460752303423488), by norm_num⟩
  | 5 => ⟨((595650605718423/72057594037927936), (-144287184703/2251799813685248)), (188921/144115188075855872), by norm_num⟩
  | 4 => ⟨((185839152784241/4503599627370496), (-13819683682927/36028797018963968)), (71003/9007199254740992), by norm_num⟩
  | 3 => ⟨((1483094062686361/9007199254740992), (-17218904210011/9007199254740992)), (44515/1125899906842624), by norm_num⟩
  | 2 => ⟨((1107798025297377/2251799813685248), (-34271107882407/4503599627370496)), (178891/1125899906842624), by norm_num⟩
  | 1 => ⟨((549378762816949/562949953421312), (-1593478505299/70368744177664)), (540843/1125899906842624), by norm_num⟩
  | 0 => ⟨((133957569440095/140737488355328), (-25082407810943/562949953421312)), (2196905/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((133957569440095/140737488355328), (-25082407810943/562949953421312)), (8380527504927825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2035598067942399/2251799813685248), (-23874082345253/281474976710656)), (2188955/1125899906842624), by norm_num⟩
  | 2 => ⟨((1823954897566189/2251799813685248), (-172654906890183/1125899906842624)), (8657799/2251799813685248), by norm_num⟩
  | 3 => ⟨((1424448381853807/2251799813685248), (-559400993103025/2251799813685248)), (16680931/2251799813685248), by norm_num⟩
  | 4 => ⟨((381056013738785/1125899906842624), (-707734172984879/2251799813685248)), (29392005/2251799813685248), by norm_num⟩
  | 5 => ⟨((70989510106207/4503599627370496), (-239529607476937/1125899906842624)), (153483369/9007199254740992), by norm_num⟩
  | 6 => ⟨((-810863745200913/18014398509481984), (-241642645316913/36028797018963968)), (280577269/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-1576252153/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile000Terms3
