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
namespace Reinmann.XiBand97.Tile011Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25029/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25029/1280))
  have he : value ((69/80), (25029/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-2028095447/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-457498999940789/9007199254740992), (427654282048423/9007199254740992)), (230047197/18014398509481984), by norm_num⟩
  | 1 => ⟨((337159355/2147483648), (-630329867/4294967296)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((-130271735/536870912), (974188189/4294967296)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((268450309/1073741824), (-501876175/2147483648)), (69/1073741824), by norm_num⟩
  | 4 => ⟨((-414895651/2147483648), (387830141/2147483648)), (215/4294967296), by norm_num⟩
  | 5 => ⟨((1025968057/8589934592), (-119879943/1073741824)), (67/2147483648), by norm_num⟩
  | 6 => ⟨((-1057103607/17179869184), (494071991/8589934592)), (279/17179869184), by norm_num⟩
  | 7 => ⟨((466793161/17179869184), (-872684285/34359738368)), (31/4294967296), by norm_num⟩
  | 8 => ⟨((-721438739/68719476736), (674376043/68719476736)), (97/34359738368), by norm_num⟩
  | 9 => ⟨((123888765/34359738368), (-463227773/137438953472)), (67/68719476736), by norm_num⟩
  | 10 => ⟨((-612712691/549755813888), (572742685/549755813888)), (21/68719476736), by norm_num⟩
  | 11 => ⟨((172174631/549755813888), (-160942905/549755813888)), (191/2199023255552), by norm_num⟩
  | 12 => ⟨((-88699849/1099511627776), (663308469/8796093022208)), (199/8796093022208), by norm_num⟩
  | 13 => ⟨((674892305/35184372088832), (-315433021/17592186044416)), (191/35184372088832), by norm_num⟩
  | 14 => ⟨((-596034505/140737488355328), (557152491/140737488355328)), (85/70368744177664), by norm_num⟩
  | 15 => ⟨((982596245/1125899906842624), (-229624267/281474976710656)), (141/562949953421312), by norm_num⟩
  | 16 => ⟨((-759311677/4503599627370496), (354889179/2251799813685248)), (55/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (778277481467/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777850570939689/633825300114114700748351602688), (3680607829651/633825300114114700748351602688)), (92563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236088592548281/4951760157141521099596496896), (258732313693/2475880078570760549798248448)), (104157/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888419045290581/2475880078570760549798248448), (2198625990939/1237940039285380274899124224)), (110693/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770085071333619/154742504910672534362390528), (4395905364337/154742504910672534362390528)), (27681/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548516673240579/9671406556917033397649408), (4119730927189/9671406556917033397649408)), (25959/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257881288815361/604462909807314587353088), (112604209123/18889465931478580854784)), (90889/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886317085458671/75557863725914323419136), (731592361821/9444732965739290427392)), (147755/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648216423276881/2361183241434822606848), (4387210213613/4722366482869645213696)), (55435/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809962951177475/295147905179352825856), (1507151758665/147573952589676412928)), (152531/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821570913034077/73786976294838206464), (7530051641753/73786976294838206464)), (190793/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910256961631849/4611686018427387904), (2115866556361/2305843009213693952)), (53705/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795880401669851/576460752303423488), (8453672076421/1152921504606846976)), (215043/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192632017598967/144115188075855872), (461622244189/9007199254740992)), (94207/72057594037927936), by norm_num⟩
  | 4 => ⟨((744355333578229/18014398509481984), (2764236918351/9007199254740992)), (283123/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485592987002975/9007199254740992), (6891386014759/4503599627370496)), (354785/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110300039017637/2251799813685248), (13725279633785/2251799813685248)), (89027/562949953421312), by norm_num⟩
  | 1 => ⟨((2205035927571175/2251799813685248), (40889261306461/2251799813685248)), (1074963/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079209280600619/1125899906842624), (80637512501287/2251799813685248)), (2176603/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079209280600619/1125899906842624), (80637512501287/2251799813685248)), (8303081521041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066022143105973/2251799813685248), (38646753289101/562949953421312)), (2164285/1125899906842624), by norm_num⟩
  | 2 => ⟨((115048767799/137438953472), (283666594407479/2251799813685248)), (8537227/2251799813685248), by norm_num⟩
  | 3 => ⟨((771072925220883/1125899906842624), (118727228809145/562949953421312)), (4110945/562949953421312), by norm_num⟩
  | 4 => ⟨((238994973396475/562949953421312), (162620764181363/562949953421312)), (29459107/2251799813685248), by norm_num⟩
  | 5 => ⟨((435890745590247/4503599627370496), (1104625232791229/4503599627370496)), (84066025/4503599627370496), by norm_num⟩
  | 6 => ⟨((-457498999940789/9007199254740992), (427654282048423/9007199254740992)), (230047197/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-2028095447/33554432)), (1/16777216), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1028630573/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((60368854885157/18014398509481984), (300970670815245/4503599627370496)), (96425917/4503599627370496), by norm_num⟩
  | 1 => ⟨((-90258691/8589934592), (-1799949259/8589934592)), (579/8589934592), by norm_num⟩
  | 2 => ⟨((70751401/4294967296), (705466311/2147483648)), (57/536870912), by norm_num⟩
  | 3 => ⟨((-36973435/2147483648), (-1474657025/4294967296)), (479/4294967296), by norm_num⟩
  | 4 => ⟨((14491249/1073741824), (1155944643/4294967296)), (377/4294967296), by norm_num⟩
  | 5 => ⟨((-18174891/2147483648), (-1449783097/8589934592)), (475/8589934592), by norm_num⟩
  | 6 => ⟨((75983021/17179869184), (1515262171/17179869184)), (499/17179869184), by norm_num⟩
  | 7 => ⟨((-68069807/34359738368), (-1357455935/34359738368)), (449/34359738368), by norm_num⟩
  | 8 => ⟨((26679061/34359738368), (66504613/4294967296)), (177/34359738368), by norm_num⟩
  | 9 => ⟨((-37178685/137438953472), (-1482843231/274877906944)), (495/274877906944), by norm_num⟩
  | 10 => ⟨((93258841/1099511627776), (1859778549/1099511627776)), (623/1099511627776), by norm_num⟩
  | 11 => ⟨((-53165919/2199023255552), (-132530111/274877906944)), (357/2199023255552), by norm_num⟩
  | 12 => ⟨((6945893/1099511627776), (554063195/4398046511104)), (375/8796093022208), by norm_num⟩
  | 13 => ⟨((-13402343/8796093022208), (-1069084273/35184372088832)), (91/8796093022208), by norm_num⟩
  | 14 => ⟨((24013125/70368744177664), (1915490031/281474976710656)), (655/281474976710656), by norm_num⟩
  | 15 => ⟨((-80312549/1125899906842624), (-800801055/562949953421312)), (549/1125899906842624), by norm_num⟩
  | 16 => ⟨((62954883/4503599627370496), (627726769/2251799813685248)), (27/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (1980872631113/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888897925536267/316912650057057350374175801344), (2341823358503/633825300114114700748351602688)), (184861/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944323716339831/19807040628566084398385987584), (82310450859/1237940039285380274899124224)), (207999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888354242043225/2475880078570760549798248448), (1398891660849/1237940039285380274899124224)), (221033/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885010322948701/77371252455336267181195264), (1398457598345/77371252455336267181195264)), (13817/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548456675502261/9671406556917033397649408), (2621185955587/9671406556917033397649408)), (3239/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1257829191546639/604462909807314587353088), (2292616054063/604462909807314587353088)), (181425/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886233178051933/75557863725914323419136), (3723773796987/75557863725914323419136)), (294893/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324092643016673/1180591620717411303424), (1395659891999/2361183241434822606848)), (110619/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404960334907773/147573952589676412928), (3835611565649/590295810358705651712)), (304311/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455366701049961/18446744073709551616), (2395418712337/36893488147419103232)), (190277/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113774936834075/576460752303423488), (5384640524795/9223372036854775808)), (214175/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49739018720535/36028797018963968), (5378332559297/1152921504606846976)), (214317/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192536901435257/144115188075855872), (2349476733245/72057594037927936)), (375375/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488574097473415/36028797018963968), (7034277473385/36028797018963968)), (563703/36028797018963968), by norm_num⟩
  | 3 => ⟨((742716455813241/4503599627370496), (68501013415/70368744177664)), (705751/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110155826475525/2251799813685248), (17462308285645/4503599627370496)), (44215/140737488355328), by norm_num⟩
  | 1 => ⟨((1102340980317757/1125899906842624), (26009283724017/2251799813685248)), (1065397/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158021467686037/2251799813685248), (12821508670969/562949953421312)), (4295655/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158021467686037/2251799813685248), (12821508670969/562949953421312)), (16386623391158293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033490270616655/1125899906842624), (98300357933829/2251799813685248)), (4214595/1125899906842624), by norm_num⟩
  | 2 => ⟨((946519662085527/1125899906842624), (22558058426269/281474976710656)), (8105323/1125899906842624), by norm_num⟩
  | 3 => ⟨((1576974310628807/2251799813685248), (303425136947591/2251799813685248)), (29854197/2251799813685248), by norm_num⟩
  | 4 => ⟨((1063496474285735/2251799813685248), (424987730487717/2251799813685248)), (49860397/2251799813685248), by norm_num⟩
  | 5 => ⟨((422066905760005/2251799813685248), (401432623132421/2251799813685248)), (131834837/4503599627370496), by norm_num⟩
  | 6 => ⟨((60368854885157/18014398509481984), (300970670815245/4503599627370496)), (96425917/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1028630573/16777216)), (1/8388608), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1042592685/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((897268039111973/18014398509481984), (369133696484693/9007199254740992)), (125838025/9007199254740992), by norm_num⟩
  | 1 => ⟨((-84983293/536870912), (-559390429/4294967296)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((1080325919/4294967296), (55555403/268435456)), (309/4294967296), by norm_num⟩
  | 3 => ⟨((-1144444641/4294967296), (-941642993/4294967296)), (165/2147483648), by norm_num⟩
  | 4 => ⟨((909276669/4294967296), (374074015/2147483648)), (33/536870912), by norm_num⟩
  | 5 => ⟨((-72243255/536870912), (-951061885/8589934592)), (169/4294967296), by norm_num⟩
  | 6 => ⟨((612247875/8589934592), (503754311/8589934592)), (45/2147483648), by norm_num⟩
  | 7 => ⟨((-555930487/17179869184), (-228708331/8589934592)), (329/34359738368), by norm_num⟩
  | 8 => ⟨((883388507/68719476736), (726847387/68719476736)), (263/68719476736), by norm_num⟩
  | 9 => ⟨((-311939581/68719476736), (-64165559/17179869184)), (47/34359738368), by norm_num⟩
  | 10 => ⟨((49568039/34359738368), (326274561/274877906944)), (241/549755813888), by norm_num⟩
  | 11 => ⟨((-458268789/1099511627776), (-188530567/549755813888)), (35/274877906944), by norm_num⟩
  | 12 => ⟨((970935253/8796093022208), (798880387/8796093022208)), (299/8796093022208), by norm_num⟩
  | 13 => ⟨((-118680173/4398046511104), (-390597673/17592186044416)), (295/35184372088832), by norm_num⟩
  | 14 => ⟨((862107379/140737488355328), (709337389/140737488355328)), (269/140737488355328), by norm_num⟩
  | 15 => ⟨((-365309821/281474976710656), (-601149975/562949953421312)), (229/562949953421312), by norm_num⟩
  | 16 => ⟨((290243569/1125899906842624), (477621745/2251799813685248)), (183/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (448415227019/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444435415700251/158456325028528675187087900672), (530092421625/316912650057057350374175801344)), (184609/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888586613457255/39614081257132168796771975168), (149053342393/4951760157141521099596496896)), (207699/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944144905863801/1237940039285380274899124224), (1266599356969/2475880078570760549798248448)), (27587/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769956429212299/154742504910672534362390528), (1266201255009/154742504910672534362390528)), (220713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548396699164199/9671406556917033397649408), (1186640866655/9671406556917033397649408)), (103469/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314444234713593/151115727451828646838272), (1037888143601/604462909807314587353088)), (181089/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943074345941249/37778931862957161709568), (26340253833/1180591620717411303424)), (294305/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296307578412411/4722366482869645213696), (315909902191/1180591620717411303424)), (220759/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619755325389713/590295810358705651712), (434094950907/147573952589676412928)), (151797/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455340047013467/18446744073709551616), (2168789124383/73786976294838206464)), (379567/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820280283695055/9223372036854775808), (1218786113699/4611686018427387904)), (427117/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591531436910785/1152921504606846976), (2434681107903/1152921504606846976)), (427247/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596218058173825/72057594037927936), (2127097995181/144115188075855872)), (373987/144115188075855872), by norm_num⟩
  | 4 => ⟨((372106592954791/9007199254740992), (3184162365425/36028797018963968)), (561273/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485254269478033/9007199254740992), (3968880285133/9007199254740992)), (351053/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109986154793657/2251799813685248), (7903894028955/4503599627370496)), (21965/70368744177664), by norm_num⟩
  | 1 => ⟨((551054359012799/562949953421312), (11771528809847/2251799813685248)), (2112537/2251799813685248), by norm_num⟩
  | 0 => ⟨((269658527652179/281474976710656), (11603962561091/1125899906842624)), (4240807/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269658527652179/281474976710656), (11603962561091/1125899906842624)), (16177394875533293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066465918598113/2251799813685248), (21712544673/1099511627776)), (1026621/281474976710656), by norm_num⟩
  | 2 => ⟨((1895507774170051/2251799813685248), (20403710356183/562949953421312)), (7699187/1125899906842624), by norm_num⟩
  | 3 => ⟨((796316066331197/1125899906842624), (137402592777601/2251799813685248)), (13520063/1125899906842624), by norm_num⟩
  | 4 => ⟨((1118037945551879/2251799813685248), (48590417105195/562949953421312)), (41549305/2251799813685248), by norm_num⟩
  | 5 => ⟨((1076678648053215/4503599627370496), (193004475028861/2251799813685248)), (96863483/4503599627370496), by norm_num⟩
  | 6 => ⟨((897268039111973/18014398509481984), (369133696484693/9007199254740992)), (125838025/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1042592685/16777216)), (1/8388608), by norm_num⟩, -10, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1055984753/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1115002961429979/18014398509481984), (-122857399904077/18014398509481984)), (19411621/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1711395301/8589934592), (188571317/8589934592)), (15/536870912), by norm_num⟩
  | 2 => ⟨((1377192241/4294967296), (-151746913/4294967296)), (195/4294967296), by norm_num⟩
  | 3 => ⟨((-738835135/2147483648), (162818157/4294967296)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((594554639/2147483648), (-131022857/4294967296)), (173/4294967296), by norm_num⟩
  | 5 => ⟨((-1531038043/8589934592), (168698523/8589934592)), (225/8589934592), by norm_num⟩
  | 6 => ⟨((51335639/536870912), (-45251633/4294967296)), (61/4294967296), by norm_num⟩
  | 7 => ⟨((-188849197/4294967296), (166467871/34359738368)), (113/17179869184), by norm_num⟩
  | 8 => ⟨((607882115/34359738368), (-133959851/68719476736)), (23/8589934592), by norm_num⟩
  | 9 => ⟨((-869643131/137438953472), (47911125/68719476736)), (265/274877906944), by norm_num⟩
  | 10 => ⟨((279927325/137438953472), (-61687985/274877906944)), (173/549755813888), by norm_num⟩
  | 11 => ⟨((-163827509/274877906944), (72205805/1099511627776)), (51/549755813888), by norm_num⟩
  | 12 => ⟨((1406241089/8796093022208), (-4842115/274877906944)), (221/8796093022208), by norm_num⟩
  | 13 => ⟨((-1392773983/35184372088832), (153463797/35184372088832)), (221/35184372088832), by norm_num⟩
  | 14 => ⟨((1280904715/140737488355328), (-70568701/70368744177664)), (205/140737488355328), by norm_num⟩
  | 15 => ⟨((-68717887/35184372088832), (15143459/70368744177664)), (89/281474976710656), by norm_num⟩
  | 16 => ⟨((884777381/2251799813685248), (-24372457/562949953421312)), (289/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-35738133779/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111105502155685/39614081257132168796771975168), (-168980986385/633825300114114700748351602688)), (184433/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944263164032937/19807040628566084398385987584), (-190058313613/39614081257132168796771975168)), (207491/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236028227471191/309485009821345068724781056), (-201879810085/2475880078570760549798248448)), (220461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769892506111721/154742504910672534362390528), (-6306736055/4835703278458516698824704)), (13779/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((193542105545779/1208925819614629174706176), (-94566919119/4835703278458516698824704)), (206689/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157215579869513/75557863725914323419136), (-165423897615/604462909807314587353088)), (22607/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886063841391473/75557863725914323419136), (-33585750933/9444732965739290427392)), (36737/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324061015039363/1180591620717411303424), (-50350681709/1180591620717411303424)), (55107/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619668181926829/590295810358705651712), (-138373619215/295147905179352825856)), (37887/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455312887380715/18446744073709551616), (-43207751007/9223372036854775808)), (189441/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820158464530731/9223372036854775808), (-194248035879/4611686018427387904)), (106565/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49731566116605/36028797018963968), (-194014756759/576460752303423488)), (426283/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74520657449031/9007199254740992), (-42375212849/18014398509481984)), (11657/4503599627370496), by norm_num⟩
  | 4 => ⟨((372067272602283/9007199254740992), (-507456199353/36028797018963968)), (279793/18014398509481984), by norm_num⟩
  | 3 => ⟨((92816225635305/562949953421312), (-632493368597/9007199254740992)), (699575/9007199254740992), by norm_num⟩
  | 2 => ⟨((34681074810399/70368744177664), (-1259523016147/4503599627370496)), (1399433/4503599627370496), by norm_num⟩
  | 1 => ⟨((275457067454179/281474976710656), (-234460532663/281474976710656)), (262485/281474976710656), by norm_num⟩
  | 0 => ⟨((2156203340099577/2251799813685248), (-462165031321/281474976710656)), (4202817/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156203340099577/2251799813685248), (-462165031321/281474976710656)), (16032474526412200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032329593737455/1125899906842624), (-3540356573991/1125899906842624)), (8062589/2251799813685248), by norm_num⟩
  | 2 => ⟨((1893049017065827/2251799813685248), (-1623063844975/281474976710656)), (14835767/2251799813685248), by norm_num⟩
  | 3 => ⟨((1591378577134527/2251799813685248), (-21831705626347/2251799813685248)), (25115439/2251799813685248), by norm_num⟩
  | 4 => ⟨((1124437943818959/2251799813685248), (-3857193302101/281474976710656)), (8996467/562949953421312), by norm_num⟩
  | 5 => ⟨((280533041536511/1125899906842624), (-30817478386259/2251799813685248)), (36925407/2251799813685248), by norm_num⟩
  | 6 => ⟨((1115002961429979/18014398509481984), (-122857399904077/18014398509481984)), (19411621/2251799813685248), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1055984753/16777216)), (1/8388608), by norm_num⟩, -10, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1068851505/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((346869269745145/9007199254740992), (-833507953607767/18014398509481984)), (263017559/18014398509481984), by norm_num⟩
  | 1 => ⟨((-538889679/4294967296), (323730633/2147483648)), (103/2147483648), by norm_num⟩
  | 2 => ⟨((877877299/4294967296), (-1054745655/4294967296)), (169/2147483648), by norm_num⟩
  | 3 => ⟨((-238350749/1073741824), (1145487723/4294967296)), (185/2147483648), by norm_num⟩
  | 4 => ⟨((388284875/2147483648), (-233256849/1073741824)), (303/4294967296), by norm_num⟩
  | 5 => ⟨((-506027843/4294967296), (303989333/2147483648)), (199/4294967296), by norm_num⟩
  | 6 => ⟨((549562521/8589934592), (-165071099/2147483648)), (109/4294967296), by norm_num⟩
  | 7 => ⟨((-127894839/4294967296), (614648659/17179869184)), (205/17179869184), by norm_num⟩
  | 8 => ⟨((104173433/8589934592), (-500646167/34359738368)), (21/4294967296), by norm_num⟩
  | 9 => ⟨((-603390403/137438953472), (724957131/137438953472)), (245/137438953472), by norm_num⟩
  | 10 => ⟨((786361673/549755813888), (-14762377/8589934592)), (161/274877906944), by norm_num⟩
  | 11 => ⟨((-931651725/2199023255552), (139919271/274877906944)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((505901877/4398046511104), (-607827323/4398046511104)), (105/2199023255552), by norm_num⟩
  | 13 => ⟨((-507162201/17592186044416), (4760481/137438953472)), (53/4398046511104), by norm_num⟩
  | 14 => ⟨((236054773/35184372088832), (-283613379/35184372088832)), (397/140737488355328), by norm_num⟩
  | 15 => ⟨((-820361855/562949953421312), (246410605/140737488355328)), (347/562949953421312), by norm_num⟩
  | 16 => ⟨((334102265/1125899906842624), (-802829539/2251799813685248)), (71/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-1141949094517/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444408746480743/158456325028528675187087900672), (-674898485255/316912650057057350374175801344)), (92333/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944233305123459/19807040628566084398385987584), (-1518154830823/39614081257132168796771975168)), (207767/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944081158417375/1237940039285380274899124224), (-806288685489/1237940039285380274899124224)), (55193/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769828943921945/154742504910672534362390528), (-201507217785/19342813113834066795298816)), (110397/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548277191918207/9671406556917033397649408), (-1510752257273/9671406556917033397649408)), (207019/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257672380240327/604462909807314587353088), (-165169575897/75557863725914323419136)), (90583/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885978803335287/75557863725914323419136), (-2146170751361/75557863725914323419136)), (147219/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324045044707247/1180591620717411303424), (-804362046567/2361183241434822606848)), (55217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619580178355863/590295810358705651712), (-2210527702985/590295810358705651712)), (75939/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821141295438053/73786976294838206464), (-2760959536623/73786976294838206464)), (379791/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455008521565031/2305843009213693952), (-1551528633563/4611686018427387904)), (106849/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591285310632879/1152921504606846976), (-1549641935339/576460752303423488)), (427561/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596110418096775/72057594037927936), (-1353817157213/72057594037927936)), (187151/72057594037927936), by norm_num⟩
  | 4 => ⟨((93006475811371/2251799813685248), (-1013247075241/9007199254740992)), (561823/36028797018963968), by norm_num⟩
  | 3 => ⟨((1450049907201/8796093022208), (-1262864614533/2251799813685248)), (175733/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109583419540037/2251799813685248), (-5029360189389/2251799813685248)), (1407827/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101505699342109/1125899906842624), (-14978057610355/2251799813685248)), (2116679/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077432475780353/1125899906842624), (-3689852844195/281474976710656)), (2126631/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077432475780353/1125899906842624), (-3689852844195/281474976710656)), (8112453464988326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2061715952880391/2251799813685248), (-56496209100291/2251799813685248)), (4125925/1125899906842624), by norm_num⟩
  | 2 => ⟨((1886260413960803/2251799813685248), (-25863563641723/562949953421312)), (7762311/1125899906842624), by norm_num⟩
  | 3 => ⟨((787653401720953/1125899906842624), (-2708134619963/35184372088832)), (27435449/2251799813685248), by norm_num⟩
  | 4 => ⟨((544353781862013/1125899906842624), (-121251073649781/1125899906842624)), (42609809/2251799813685248), by norm_num⟩
  | 5 => ⟨((7816503471321/35184372088832), (-234491468006893/2251799813685248)), (50379783/2251799813685248), by norm_num⟩
  | 6 => ⟨((346869269745145/9007199254740992), (-833507953607767/18014398509481984)), (263017559/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1068851505/16777216)), (1/8388608), by norm_num⟩, -10, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1081232601/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-91999909648907/36028797018963968), (-65543728144337/1125899906842624)), (346182665/36028797018963968), by norm_num⟩
  | 1 => ⟨((72292493/8589934592), (1648112759/8589934592)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((-29783033/2147483648), (-678988849/2147483648)), (57/1073741824), by norm_num⟩
  | 3 => ⟨((16360003/1073741824), (1491890987/4294967296)), (63/1073741824), by norm_num⟩
  | 4 => ⟨((-53919901/4294967296), (-1229257329/4294967296)), (209/4294967296), by norm_num⟩
  | 5 => ⟨((71084479/8589934592), (1620572649/8589934592)), (277/8589934592), by norm_num⟩
  | 6 => ⟨((-39047141/8589934592), (-1780381027/17179869184)), (153/8589934592), by norm_num⟩
  | 7 => ⟨((73538861/34359738368), (52391477/1073741824)), (145/17179869184), by norm_num⟩
  | 8 => ⟨((-30296511/34359738368), (-1381390091/68719476736)), (241/68719476736), by norm_num⟩
  | 9 => ⟨((88757651/274877906944), (2023482839/274877906944)), (355/274877906944), by norm_num⟩
  | 10 => ⟨((-14626537/137438953472), (-333453467/137438953472)), (59/137438953472), by norm_num⟩
  | 11 => ⟨((70118807/2199023255552), (1598557425/2199023255552)), (71/549755813888), by norm_num⟩
  | 12 => ⟨((-77033383/8796093022208), (-1756194831/8796093022208)), (157/4398046511104), by norm_num⟩
  | 13 => ⟨((78119835/35184372088832), (890481795/17592186044416)), (5/549755813888), by norm_num⟩
  | 14 => ⟨((-73562923/140737488355328), (-1677075845/140737488355328)), (19/8796093022208), by norm_num⟩
  | 15 => ⟨((64653705/562949953421312), (736982453/281474976710656)), (269/562949953421312), by norm_num⟩
  | 16 => ⟨((-3329501/140737488355328), (-1214486969/2251799813685248)), (223/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-1051619247087/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777582529630653/633825300114114700748351602688), (-2485918386725/633825300114114700748351602688)), (92445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944203741989137/19807040628566084398385987584), (-2795971748027/39614081257132168796771975168)), (104017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118006208824775/154742504910672534362390528), (-742464652091/618970019642690137449562112)), (110537/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769765795296095/154742504910672534362390528), (-2968890016269/154742504910672534362390528)), (110557/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548217806452207/9671406556917033397649408), (-2782305660701/9671406556917033397649408)), (103669/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628810117259871/302231454903657293676544), (-1216744586551/302231454903657293676544)), (22683/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942946861499925/37778931862957161709568), (-1976246418061/37778931862957161709568)), (18435/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648058034193217/2361183241434822606848), (-2962684395071/4722366482869645213696)), (110647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619491539447601/590295810358705651712), (-4070954329639/590295810358705651712)), (152197/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113814360472345/4611686018427387904), (-5084590969453/73786976294838206464)), (95167/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819907616839667/9223372036854775808), (-5714529748431/9223372036854775808)), (107123/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198894699218693/144115188075855872), (-2853746747441/576460752303423488)), (53599/288230376151711744), by norm_num⟩
  | 5 => ⟨((596053842479285/72057594037927936), (-4986151478163/144115188075855872)), (187767/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487931099263983/36028797018963968), (-7463442663881/36028797018963968)), (281991/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484630610623615/9007199254740992), (-9301739012551/9007199254740992)), (353085/9007199254740992), by norm_num⟩
  | 2 => ⟨((554677848167225/1125899906842624), (-18521019237005/4503599627370496)), (707963/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202292429362497/2251799813685248), (-13788099739431/1125899906842624)), (1066447/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153285869017735/2251799813685248), (-13583992800607/562949953421312)), (2151001/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153285869017735/2251799813685248), (-13583992800607/562949953421312)), (8205417641646575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1028885340469399/1125899906842624), (-51958827893347/1125899906842624)), (2108801/1125899906842624), by norm_num⟩
  | 2 => ⟨((1875664644111873/2251799813685248), (-94963461676367/1125899906842624)), (8097649/2251799813685248), by norm_num⟩
  | 3 => ⟨((773169444236351/1125899906842624), (-79100995775165/562949953421312)), (3714015/562949953421312), by norm_num⟩
  | 4 => ⟨((508715842224789/1125899906842624), (-217278543395687/1125899906842624)), (6144645/562949953421312), by norm_num⟩
  | 5 => ⟨((187922426695697/1125899906842624), (-785384466446091/4503599627370496)), (63394309/4503599627370496), by norm_num⟩
  | 6 => ⟨((-91999909648907/36028797018963968), (-65543728144337/1125899906842624)), (346182665/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1081232601/16777216)), (1/16777216), by norm_num⟩, -10, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile011Terms3
