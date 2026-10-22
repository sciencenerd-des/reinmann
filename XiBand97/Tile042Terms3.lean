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
namespace Reinmann.XiBand97.Tile042Terms3
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
  | 0 => ⟨((-22364231/8388608), (-11208387/131072)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-482913911724331/9007199254740992), (199366306795331/4503599627370496)), (57467093/2251799813685248), by norm_num⟩
  | 1 => ⟨((177944589/1073741824), (-587701529/4294967296)), (341/4294967296), by norm_num⟩
  | 2 => ⟨((-550034279/2147483648), (227076297/1073741824)), (529/4294967296), by norm_num⟩
  | 3 => ⟨((1133452871/4294967296), (-467934983/2147483648)), (137/1073741824), by norm_num⟩
  | 4 => ⟨((-109485967/536870912), (723203449/4294967296)), (425/4294967296), by norm_num⟩
  | 5 => ⟨((1082962471/8589934592), (-894181025/8589934592)), (33/536870912), by norm_num⟩
  | 6 => ⟨((-557913829/8589934592), (460658585/8589934592)), (273/8589934592), by norm_num⟩
  | 7 => ⟨((123181095/4294967296), (-813665853/34359738368)), (121/8589934592), by norm_num⟩
  | 8 => ⟨((-190378997/17179869184), (157192231/17179869184)), (47/8589934592), by norm_num⟩
  | 9 => ⟨((523084055/137438953472), (-863800639/274877906944)), (259/137438953472), by norm_num⟩
  | 10 => ⟨((-80843751/68719476736), (534008889/549755813888)), (161/274877906944), by norm_num⟩
  | 11 => ⟨((726956993/2199023255552), (-600234235/2199023255552)), (91/549755813888), by norm_num⟩
  | 12 => ⟨((-749018309/8796093022208), (309224917/4398046511104)), (377/8796093022208), by norm_num⟩
  | 13 => ⟨((712383813/35184372088832), (-147050361/8796093022208)), (45/4398046511104), by norm_num⟩
  | 14 => ⟨((-629145317/140737488355328), (259736519/70368744177664)), (5/2199023255552), by norm_num⟩
  | 15 => ⟨((129647659/140737488355328), (-856380381/1125899906842624)), (265/562949953421312), by norm_num⟩
  | 16 => ⟨((-200373209/1125899906842624), (165444257/1125899906842624)), (103/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (3193206332573/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888925096152141/316912650057057350374175801344), (1887652622267/316912650057057350374175801344)), (23143/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888708293711555/39614081257132168796771975168), (2123112915015/19807040628566084398385987584)), (208335/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888418542952001/2475880078570760549798248448), (1127596670827/618970019642690137449562112)), (221411/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27657570903337/2417851639229258349412352), (4509005286159/154742504910672534362390528)), (110737/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548516139962389/9671406556917033397649408), (4225725153461/9671406556917033397649408)), (103849/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257880789124361/604462909807314587353088), (1848021346351/302231454903657293676544)), (90901/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886316211514601/75557863725914323419136), (6003320126629/75557863725914323419136)), (2309/590295810358705651712), by norm_num⟩
  | 10 => ⟨((81027008559853/295147905179352825856), (4500085534011/4722366482869645213696)), (221773/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809962419403727/295147905179352825856), (6183712132263/590295810358705651712)), (305115/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455392363008229/18446744073709551616), (3861892667349/36893488147419103232)), (190829/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820512099077963/9223372036854775808), (1085151701087/1152921504606846976)), (429731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591758753971437/1152921504606846976), (8671165739565/1152921504606846976)), (430189/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192629971780945/144115188075855872), (7575977505595/144115188075855872)), (188465/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488707094958779/36028797018963968), (5670704778069/18014398509481984)), (566425/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485587644658729/9007199254740992), (1767168929169/1125899906842624)), (354919/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220586777920693/4503599627370496), (3519590757887/562949953421312)), (356277/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102504747090195/1125899906842624), (41941038027721/2251799813685248)), (1075641/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079170046081931/1125899906842624), (82711212440543/2251799813685248)), (544661/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079170046081931/1125899906842624), (82711212440543/2251799813685248)), (2077716828466319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((516430321704067/562949953421312), (158556657476355/2251799813685248)), (2168245/562949953421312), by norm_num⟩
  | 2 => ⟨((1883854948115175/2251799813685248), (290908508407155/2251799813685248)), (4283489/562949953421312), by norm_num⟩
  | 3 => ⟨((1538450125193315/2251799813685248), (121686978940355/562949953421312)), (33095573/2251799813685248), by norm_num⟩
  | 4 => ⟨((472933970698639/1125899906842624), (665101211386291/2251799813685248)), (58135/2199023255552), by norm_num⟩
  | 5 => ⟨((401728908961385/4503599627370496), (558751190768791/2251799813685248)), (170355077/4503599627370496), by norm_num⟩
  | 6 => ⟨((-482913911724331/9007199254740992), (199366306795331/4503599627370496)), (57467093/2251799813685248), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-11208387/131072)), (1/8388608), by norm_num⟩, -14, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1455305335/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((412375626919151/18014398509481984), (1132662463410397/18014398509481984)), (345453583/18014398509481984), by norm_num⟩
  | 1 => ⟨((-308275555/4294967296), (-846733237/4294967296)), (65/1073741824), by norm_num⟩
  | 2 => ⟨((241649055/2147483648), (1327463583/4294967296)), (205/2147483648), by norm_num⟩
  | 3 => ⟨((-505126143/4294967296), (-1387418129/4294967296)), (431/4294967296), by norm_num⟩
  | 4 => ⟨((395955025/4294967296), (1087560379/4294967296)), (85/1073741824), by norm_num⟩
  | 5 => ⟨((-124151469/2147483648), (-1364015711/8589934592)), (107/2147483648), by norm_num⟩
  | 6 => ⟨((519034951/17179869184), (356405281/4294967296)), (225/8589934592), by norm_num⟩
  | 7 => ⟨((-232490155/17179869184), (-1277150511/34359738368)), (405/34359738368), by norm_num⟩
  | 8 => ⟨((45560721/8589934592), (500562255/34359738368)), (319/68719476736), by norm_num⟩
  | 9 => ⟨((-253965115/137438953472), (-1395120049/274877906944)), (223/137438953472), by norm_num⟩
  | 10 => ⟨((79630615/137438953472), (874878169/549755813888)), (141/274877906944), by norm_num⟩
  | 11 => ⟨((-22698303/137438953472), (-997518341/2199023255552)), (323/2199023255552), by norm_num⟩
  | 12 => ⟨((379575455/8796093022208), (260642749/2199023255552)), (339/8796093022208), by norm_num⟩
  | 13 => ⟨((-91550511/8796093022208), (-502919281/17592186044416)), (329/35184372088832), by norm_num⟩
  | 14 => ⟨((20504007/8796093022208), (450542999/70368744177664)), (37/17592186044416), by norm_num⟩
  | 15 => ⟨((-548609667/1125899906842624), (-753426649/562949953421312)), (497/1125899906842624), by norm_num⟩
  | 16 => ⟨((430040609/4503599627370496), (590591225/2251799813685248)), (49/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (1591318286915/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888898447160553/316912650057057350374175801344), (235160648177/79228162514264337593543950336)), (184771/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888648663271745/39614081257132168796771975168), (132246970999/2475880078570760549798248448)), (207891/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888355625982591/2475880078570760549798248448), (2247578463313/2475880078570760549798248448)), (13807/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770022115724359/154742504910672534362390528), (2246881244349/154742504910672534362390528)), (220943/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548458144644965/9671406556917033397649408), (2105710656949/9671406556917033397649408)), (207167/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157228821017659/75557863725914323419136), (920878318251/302231454903657293676544)), (181305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471558896410015/18889465931478580854784), (2991467363639/75557863725914323419136)), (147341/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324093131717805/1180591620717411303424), (35037303601/73786976294838206464)), (110533/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101240266841137/36893488147419103232), (192582045005/36893488147419103232)), (152027/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821470828848385/73786976294838206464), (1924344070035/36893488147419103232)), (380199/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820404014366025/9223372036854775808), (4325717741827/9223372036854775808)), (427907/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795827122126905/576460752303423488), (1080163165259/288230376151711744)), (428135/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298135634176555/36028797018963968), (471860041603/18014398509481984)), (93719/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488583936903015/36028797018963968), (2825478829669/18014398509481984)), (562829/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485447626277311/9007199254740992), (7043854002399/9007199254740992)), (88055/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110174142140003/2251799813685248), (3507086511409/1125899906842624)), (1411599/4503599627370496), by norm_num⟩
  | 1 => ⟨((275594344889065/281474976710656), (5223674514409/562949953421312)), (2124223/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079118777084935/1125899906842624), (41201603345639/2251799813685248)), (66811/35184372088832), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1079118777084935/1125899906842624), (41201603345639/2251799813685248)), (254863739147889603/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2067808932131717/2251799813685248), (39489677142765/1125899906842624)), (2088239/562949953421312), by norm_num⟩
  | 2 => ⟨((948040766202219/1125899906842624), (145052160723237/2251799813685248)), (7963421/1125899906842624), by norm_num⟩
  | 3 => ⟨((1587212604989699/2251799813685248), (30534544135673/281474976710656)), (7218407/562949953421312), by norm_num⟩
  | 4 => ⟨((136533724146653/281474976710656), (344363210585317/2251799813685248)), (23484207/1125899906842624), by norm_num⟩
  | 5 => ⟨((954318651013297/4503599627370496), (334077239474421/2251799813685248)), (119862121/4503599627370496), by norm_num⟩
  | 6 => ⟨((412375626919151/18014398509481984), (1132662463410397/18014398509481984)), (345453583/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1455305335/16777216)), (1/8388608), by norm_num⟩, -14, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1475058915/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((145101739930705/2251799813685248), (12844556130035/4503599627370496)), (75532015/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1759113847/8589934592), (-77859289/8589934592)), (231/8589934592), by norm_num⟩
  | 2 => ⟨((1397639625/4294967296), (61860253/4294967296)), (185/4294967296), by norm_num⟩
  | 3 => ⟨((-1480591321/4294967296), (-32765869/2147483648)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((588174865/2147483648), (6508231/536870912)), (79/2147483648), by norm_num⟩
  | 5 => ⟨((-747700553/4294967296), (-66187227/8589934592)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((1584155071/17179869184), (70115523/17179869184)), (27/2147483648), by norm_num⟩
  | 7 => ⟨((-1438437169/34359738368), (-63665973/34359738368)), (99/17179869184), by norm_num⟩
  | 8 => ⟨((142857211/8589934592), (3161467/4294967296)), (159/68719476736), by norm_num⟩
  | 9 => ⟨((-807125167/137438953472), (-35723777/137438953472)), (227/274877906944), by norm_num⟩
  | 10 => ⟨((2052069783/1099511627776), (90825669/1099511627776)), (291/1099511627776), by norm_num⟩
  | 11 => ⟨((-1185743315/2199023255552), (-13120403/549755813888)), (85/1099511627776), by norm_num⟩
  | 12 => ⟨((628059347/4398046511104), (55596463/8796093022208)), (91/4398046511104), by norm_num⟩
  | 13 => ⟨((-1228311639/35184372088832), (-13591427/8796093022208)), (45/8796093022208), by norm_num⟩
  | 14 => ⟨((278831465/35184372088832), (49364899/140737488355328)), (165/140737488355328), by norm_num⟩
  | 15 => ⟨((-945217499/562949953421312), (-41835815/562949953421312)), (141/562949953421312), by norm_num⟩
  | 16 => ⟨((750988023/2251799813685248), (16619559/1125899906842624)), (113/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (7202082691/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777742263296243/633825300114114700748351602688), (8513915729/79228162514264337593543950336)), (92207/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472146830430771/9903520314283042199192993792), (19151800315/9903520314283042199192993792)), (207467/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888290608250811/2475880078570760549798248448), (20343102057/618970019642690137449562112)), (220435/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769957275163389/154742504910672534362390528), (81346836061/154742504910672534362390528)), (55109/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548397544716419/9671406556917033397649408), (38117749877/4835703278458516698824704)), (51665/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628888865568007/302231454903657293676544), (33339458017/302231454903657293676544)), (90415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886150077528769/75557863725914323419136), (108302366529/75557863725914323419136)), (146925/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296308703456877/4722366482869645213696), (81182289047/4722366482869645213696)), (220389/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619757011569553/590295810358705651712), (55776704425/295147905179352825856)), (303039/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821362504299597/73786976294838206464), (139333492209/73786976294838206464)), (378805/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910141587814277/4611686018427387904), (156601453601/9223372036854775808)), (426163/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795767342851565/576460752303423488), (19551970469/144115188075855872)), (426173/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192439359357849/144115188075855872), (136655189603/144115188075855872)), (186457/72057594037927936), by norm_num⟩
  | 4 => ⟨((372108008525409/9007199254740992), (204566319385/36028797018963968)), (559395/36028797018963968), by norm_num⟩
  | 3 => ⟨((5801807566375/35184372088832), (127490376273/4503599627370496)), (87411/1125899906842624), by norm_num⟩
  | 2 => ⟨((2219993387962053/4503599627370496), (507786717601/4503599627370496)), (699357/2251799813685248), by norm_num⟩
  | 1 => ⟨((275532415332829/281474976710656), (756266320601/2251799813685248)), (262305/281474976710656), by norm_num⟩
  | 0 => ⟨((2157392537980375/2251799813685248), (745508164427/1125899906842624)), (524811/281474976710656), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157392537980375/2251799813685248), (745508164427/1125899906842624)), (2001995087743663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1033471161938351/1125899906842624), (1428505092827/1125899906842624)), (8050491/2251799813685248), by norm_num⟩
  | 2 => ⟨((118578547195925/140737488355328), (5244938059401/2251799813685248)), (7399815/1125899906842624), by norm_num⟩
  | 3 => ⟨((399630960049511/562949953421312), (8838258270549/2251799813685248)), (12503919/1125899906842624), by norm_num⟩
  | 4 => ⟨((283684226428909/562949953421312), (6274166320397/1125899906842624)), (35701799/2251799813685248), by norm_num⟩
  | 5 => ⟨((571751705776183/2251799813685248), (12646822391731/2251799813685248)), (72759839/4503599627370496), by norm_num⟩
  | 6 => ⟨((145101739930705/2251799813685248), (12844556130035/4503599627370496)), (75532015/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1475058915/16777216)), (1/8388608), by norm_num⟩, -14, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1494005997/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((523658217037641/18014398509481984), (-15500343497625/281474976710656)), (75682181/4503599627370496), by norm_num⟩
  | 1 => ⟨((-200938079/2147483648), (761317153/4294967296)), (117/2147483648), by norm_num⟩
  | 2 => ⟨((646794725/4294967296), (-612646345/2147483648)), (379/4294967296), by norm_num⟩
  | 3 => ⟨((-21686999/134217728), (328672085/1073741824)), (409/4294967296), by norm_num⟩
  | 4 => ⟨((279231027/2147483648), (-1057954629/4294967296)), (331/4294967296), by norm_num⟩
  | 5 => ⟨((-359524001/4294967296), (170271229/1073741824)), (107/2147483648), by norm_num⟩
  | 6 => ⟨((96438593/2147483648), (-182693981/2147483648)), (231/8589934592), by norm_num⟩
  | 7 => ⟨((-709540241/34359738368), (336039565/8589934592)), (427/34359738368), by norm_num⟩
  | 8 => ⟨((285490241/34359738368), (-528159/33554432)), (345/68719476736), by norm_num⟩
  | 9 => ⟨((-25526601/8589934592), (773724495/137438953472)), (249/137438953472), by norm_num⟩
  | 10 => ⟨((525868537/549755813888), (-996209229/549755813888)), (161/274877906944), by norm_num⟩
  | 11 => ⟨((-9617645/34359738368), (583031601/1099511627776)), (379/2199023255552), by norm_num⟩
  | 12 => ⟨((10319335/137438953472), (-1251137551/8796093022208)), (409/8796093022208), by norm_num⟩
  | 13 => ⟨((-654112649/35184372088832), (1239155821/35184372088832)), (407/35184372088832), by norm_num⟩
  | 14 => ⟨((601573541/140737488355328), (-1139625347/140737488355328)), (47/17592186044416), by norm_num⟩
  | 15 => ⟨((-64546351/70368744177664), (978216661/562949953421312)), (325/562949953421312), by norm_num⟩
  | 16 => ⟨((207766689/1125899906842624), (-787189491/2251799813685248)), (33/281474976710656), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-1413467084291/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444421638000537/158456325028528675187087900672), (-1670827746645/633825300114114700748351602688)), (184729/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888524579668431/39614081257132168796771975168), (-469807942893/9903520314283042199192993792)), (103921/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888223853512329/2475880078570760549798248448), (-499029629071/618970019642690137449562112)), (220857/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27654537778917/2417851639229258349412352), (-1995482941025/154742504910672534362390528)), (220885/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1512045661233/9444732965739290427392), (-935045115245/4835703278458516698824704)), (207109/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257722683205587/604462909807314587353088), (-1635654231069/604462909807314587353088)), (181249/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886060420945043/75557863725914323419136), (-2656673674497/75557863725914323419136)), (294585/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324060320756999/1180591620717411303424), (-1991399511039/4722366482869645213696)), (220987/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619664019700577/590295810358705651712), (-2736378709883/590295810358705651712)), (4749/9223372036854775808), by norm_num⟩
  | 8 => ⟨((910622916045963/36893488147419103232), (-3417782089817/73786976294838206464)), (190019/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910075663089085/4611686018427387904), (-1920653886935/4611686018427387904)), (427705/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198925262083693/144115188075855872), (-3836691607663/1152921504606846976)), (106977/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192322514581485/144115188075855872), (-418989885529/18014398509481984)), (374649/144115188075855872), by norm_num⟩
  | 4 => ⟨((744127557412585/18014398509481984), (-1254381060663/9007199254740992)), (562431/36028797018963968), by norm_num⟩
  | 3 => ⟨((371259677894835/2251799813685248), (-6253825025931/9007199254740992)), (175961/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109768383742345/2251799813685248), (-6226784226491/2251799813685248)), (352527/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203553174394917/2251799813685248), (-18545704457995/2251799813685248)), (2121243/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077948301494519/1125899906842624), (-36556138389221/2251799813685248)), (2133483/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077948301494519/1125899906842624), (-36556138389221/2251799813685248)), (8138591770652389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2063484410686263/2251799813685248), (-69998455540093/2251799813685248)), (4154509/1125899906842624), by norm_num⟩
  | 2 => ⟨((472185416252295/562949953421312), (-16036141501263/281474976710656)), (15744871/2251799813685248), by norm_num⟩
  | 3 => ⟨((788455295663791/1125899906842624), (-53802524390211/562949953421312)), (28206673/2251799813685248), by norm_num⟩
  | 4 => ⟨((135465617997985/281474976710656), (-301418518770491/2251799813685248)), (44897209/2251799813685248), by norm_num⟩
  | 5 => ⟨((962436024880613/4503599627370496), (-580255430140849/4503599627370496)), (110469993/4503599627370496), by norm_num⟩
  | 6 => ⟨((523658217037641/18014398509481984), (-15500343497625/281474976710656)), (75682181/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1494005997/16777216)), (1/8388608), by norm_num⟩, -14, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-756104931/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-611730573314477/18014398509481984), (-55964357224805/1125899906842624)), (395646759/18014398509481984), by norm_num⟩
  | 1 => ⟨((475186649/4294967296), (347780759/2147483648)), (309/4294967296), by norm_num⟩
  | 2 => ⟨((-193525497/1073741824), (-1133103287/4294967296)), (505/4294967296), by norm_num⟩
  | 3 => ⟨((840699669/4294967296), (153823329/536870912)), (551/4294967296), by norm_num⟩
  | 4 => ⟨((-342385085/2147483648), (-62646407/268435456)), (451/4294967296), by norm_num⟩
  | 5 => ⟨((55776183/536870912), (326572867/2147483648)), (295/4294967296), by norm_num⟩
  | 6 => ⟨((-484597837/8589934592), (-709337285/8589934592)), (161/4294967296), by norm_num⟩
  | 7 => ⟨((112776181/4294967296), (165077811/4294967296)), (151/8589934592), by norm_num⟩
  | 8 => ⟨((-367435685/34359738368), (-1075678889/68719476736)), (247/34359738368), by norm_num⟩
  | 9 => ⟨((532062637/137438953472), (6084489/1073741824)), (359/137438953472), by norm_num⟩
  | 10 => ⟨((-346702287/274877906944), (-1014981251/549755813888)), (235/274877906944), by norm_num⟩
  | 11 => ⟨((205379913/549755813888), (75156975/137438953472)), (559/2199023255552), by norm_num⟩
  | 12 => ⟨((-446098389/4398046511104), (-652983147/4398046511104)), (305/4398046511104), by norm_num⟩
  | 13 => ⟨((1746913/68719476736), (327304943/8796093022208)), (77/4398046511104), by norm_num⟩
  | 14 => ⟨((-416300705/70368744177664), (-76170793/8796093022208)), (9/2199023255552), by norm_num⟩
  | 15 => ⟨((723385539/562949953421312), (529433167/281474976710656)), (251/281474976710656), by norm_num⟩
  | 16 => ⟨((-147303745/562949953421312), (-107809023/281474976710656)), (411/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-1413423097629/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777629972698319/633825300114114700748351602688), (-1670682366131/316912650057057350374175801344)), (92529/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888460698315211/39614081257132168796771975168), (-1879058399103/19807040628566084398385987584)), (208233/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888155668290783/2475880078570760549798248448), (-3991853886833/2475880078570760549798248448)), (221297/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769821882882813/154742504910672534362390528), (-3990566012255/154742504910672534362390528)), (27669/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548270134295561/9671406556917033397649408), (-1869893871169/4835703278458516698824704)), (207577/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157208220918409/75557863725914323419136), (-3270946911823/604462909807314587353088)), (22711/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((235745904753081/9444732965739290427392), (-5312726055565/75557863725914323419136)), (295353/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296170788808637/4722366482869645213696), (-497787916079/590295810358705651712)), (55403/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101222881575437/36893488147419103232), (-5472027220991/590295810358705651712)), (38109/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227640245518695/9223372036854775808), (-6834577942645/73786976294838206464)), (381325/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910004975528747/4611686018427387904), (-7681404080445/9223372036854775808)), (429315/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198907274778951/144115188075855872), (-1918010739713/288230376151711744)), (429719/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149024221668659/18014398509481984), (-3351259353563/72057594037927936)), (376461/144115188075855872), by norm_num⟩
  | 4 => ⟨((744028182157547/18014398509481984), (-5016385610767/18014398509481984)), (141401/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484780454114101/9007199254740992), (-3126067892325/2251799813685248)), (708607/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109495493631595/2251799813685248), (-3112342932769/562949953421312)), (711013/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202662012429379/2251799813685248), (-9268646594015/562949953421312)), (1072557/1125899906842624), by norm_num⟩
  | 0 => ⟨((538457079884511/562949953421312), (-36530433604759/1125899906842624)), (542345/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538457079884511/562949953421312), (-36530433604759/1125899906842624)), (2068881989599132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1028874438919007/1125899906842624), (-69882128903961/1125899906842624)), (4290763/1125899906842624), by norm_num⟩
  | 2 => ⟨((935872800696515/1125899906842624), (-255439886723709/2251799813685248)), (4187321/562949953421312), by norm_num⟩
  | 3 => ⟨((1526859554614617/2251799813685248), (-424654519899757/2251799813685248)), (31644763/2251799813685248), by norm_num⟩
  | 4 => ⟨((477610981485611/1125899906842624), (-287942030716349/1125899906842624)), (27424819/1125899906842624), by norm_num⟩
  | 5 => ⟨((16120620014725/140737488355328), (-977168752324043/4503599627370496)), (9323721/281474976710656), by norm_num⟩
  | 6 => ⟨((-611730573314477/18014398509481984), (-55964357224805/1125899906842624)), (395646759/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-756104931/8388608)), (1/8388608), by norm_num⟩, -14, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-764863311/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1046940966945167/18014398509481984), (76167999414319/18014398509481984)), (700268545/36028797018963968), by norm_num⟩
  | 1 => ⟨((411337213/2147483648), (-119703913/8589934592)), (69/1073741824), by norm_num⟩
  | 2 => ⟨((-1355700351/4294967296), (49315571/2147483648)), (457/4294967296), by norm_num⟩
  | 3 => ⟨((1489389065/4294967296), (-108357385/4294967296)), (63/536870912), by norm_num⟩
  | 4 => ⟨((-1227195847/4294967296), (44641033/2147483648)), (417/4294967296), by norm_num⟩
  | 5 => ⟨((808927463/4294967296), (-58851825/4294967296)), (69/1073741824), by norm_num⟩
  | 6 => ⟨((-1777395303/17179869184), (32327669/4294967296)), (19/536870912), by norm_num⟩
  | 7 => ⟨((209214463/4294967296), (-30441921/8589934592)), (575/34359738368), by norm_num⟩
  | 8 => ⟨((-172384185/8589934592), (50165803/34359738368)), (119/17179869184), by norm_num⟩
  | 9 => ⟨((1010044715/137438953472), (-36741845/68719476736)), (175/68719476736), by norm_num⟩
  | 10 => ⟨((-1331577043/549755813888), (48438051/274877906944)), (463/549755813888), by norm_num⟩
  | 11 => ⟨((1595876621/2199023255552), (-116104665/2199023255552)), (557/2199023255552), by norm_num⟩
  | 12 => ⟨((-1753249667/8796093022208), (31888503/2199023255552)), (307/4398046511104), by norm_num⟩
  | 13 => ⟨((1777976889/35184372088832), (-129352989/35184372088832)), (625/35184372088832), by norm_num⟩
  | 14 => ⟨((-1674263365/140737488355328), (121807529/140737488355328)), (591/140737488355328), by norm_num⟩
  | 15 => ⟨((735746523/281474976710656), (-107055399/562949953421312)), (521/562949953421312), by norm_num⟩
  | 16 => ⟨((-1212450257/2251799813685248), (88209283/2251799813685248)), (431/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (3997673081177/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777573864812957/633825300114114700748351602688), (1181260356843/158456325028528675187087900672)), (185331/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944198633334379/19807040628566084398385987584), (2657170455279/19807040628566084398385987584)), (104279/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888087850932015/2475880078570760549798248448), (5644847026807/2475880078570760549798248448)), (110831/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769753592208737/154742504910672534362390528), (5643002199477/154742504910672534362390528)), (55435/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548205609345423/9671406556917033397649408), (5288354959633/9671406556917033397649408)), (51991/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257608806083707/604462909807314587353088), (2312675789329/302231454903657293676544)), (45513/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471468433983419/18889465931478580854784), (3756262213239/37778931862957161709568)), (147995/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296099840791847/4722366482869645213696), (703897709269/590295810358705651712)), (222129/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809733609430805/295147905179352825856), (7737658235045/590295810358705651712)), (19103/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1820996360536423/73786976294838206464), (2416063017419/18446744073709551616)), (382393/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819865908696647/9223372036854775808), (10861536789447/9223372036854775808)), (215325/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795555370819335/576460752303423488), (10848113366167/1152921504606846976)), (431223/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74503807479939/9007199254740992), (9477011685165/144115188075855872)), (377965/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487849455103389/36028797018963968), (7092688561497/18014398509481984)), (568239/36028797018963968), by norm_num⟩
  | 3 => ⟨((371127133452693/2251799813685248), (17679053616945/9007199254740992)), (356281/4503599627370496), by norm_num⟩
  | 2 => ⟨((554601890089137/1125899906842624), (8800103934463/1125899906842624)), (357983/1125899906842624), by norm_num⟩
  | 1 => ⟨((1100844415398899/1125899906842624), (26203743589975/1125899906842624)), (541243/562949953421312), by norm_num⟩
  | 0 => ⟨((67234228501841/70368744177664), (51624494347393/1125899906842624)), (137455/70368744177664), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((67234228501841/70368744177664), (51624494347393/1125899906842624)), (524349212914919831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1025462320424215/1125899906842624), (98649850578017/1125899906842624)), (550539/140737488355328), by norm_num⟩
  | 2 => ⟨((462670425345535/562949953421312), (359398571998907/2251799813685248)), (4397319/562949953421312), by norm_num⟩
  | 3 => ⟨((1463653832034879/2251799813685248), (590756209019049/2251799813685248)), (34526793/2251799813685248), by norm_num⟩
  | 4 => ⟨((199095144985487/562949953421312), (23999207874579/70368744177664)), (31500221/1125899906842624), by norm_num⟩
  | 5 => ⟨((39467950698619/4503599627370496), (2172840036712909/9007199254740992)), (350137957/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1046940966945167/18014398509481984), (76167999414319/18014398509481984)), (700268545/36028797018963968), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-764863311/8388608)), (1/8388608), by norm_num⟩, -15, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile042Terms3
