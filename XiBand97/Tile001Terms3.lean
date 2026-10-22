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
namespace Reinmann.XiBand97.Tile001Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (3717/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (3717/256))
  have he : value ((69/80), (3717/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-752969633/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((780345120857475/18014398509481984), (-489855992093229/9007199254740992)), (153355199/18014398509481984), by norm_num⟩
  | 1 => ⟨((-287542331/2147483648), (361005227/2147483648)), (115/4294967296), by norm_num⟩
  | 2 => ⟨((55550347/268435456), (-1115882483/4294967296)), (45/1073741824), by norm_num⟩
  | 3 => ⟨((-915778565/4294967296), (1149746709/4294967296)), (47/1073741824), by norm_num⟩
  | 4 => ⟨((353838803/2147483648), (-222119743/1073741824)), (147/4294967296), by norm_num⟩
  | 5 => ⟨((-874984609/8589934592), (1098530489/8589934592)), (23/1073741824), by norm_num⟩
  | 6 => ⟨((901538191/17179869184), (-565934063/8589934592)), (3/268435456), by norm_num⟩
  | 7 => ⟨((-796197949/34359738368), (249903745/8589934592)), (171/34359738368), by norm_num⟩
  | 8 => ⟨((615270415/68719476736), (-772463085/68719476736)), (67/34359738368), by norm_num⟩
  | 9 => ⟨((-52828527/17179869184), (1061207195/274877906944)), (187/274877906944), by norm_num⟩
  | 10 => ⟨((522544703/549755813888), (-328023649/274877906944)), (117/549755813888), by norm_num⟩
  | 11 => ⟨((-587348313/2199023255552), (737407291/2199023255552)), (133/2199023255552), by norm_num⟩
  | 12 => ⟨((605172857/8796093022208), (-759785747/8796093022208)), (139/8796093022208), by norm_num⟩
  | 13 => ⟨((-143893461/8796093022208), (722624615/35184372088832)), (67/17592186044416), by norm_num⟩
  | 14 => ⟨((508320911/140737488355328), (-159547383/35184372088832)), (15/17592186044416), by norm_num⟩
  | 15 => ⟨((-837995475/1125899906842624), (526045583/562949953421312)), (25/140737488355328), by norm_num⟩
  | 16 => ⟨((647569897/4503599627370496), (-813014615/4503599627370496)), (39/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-584996608063/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777856810335033/633825300114114700748351602688), (-345818674449/158456325028528675187087900672)), (92337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59022378154209/1237940039285380274899124224), (-1555826161565/39614081257132168796771975168)), (6493/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888427323076703/2475880078570760549798248448), (-826307963015/1237940039285380274899124224)), (110391/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770093862890707/154742504910672534362390528), (-103256914485/9671406556917033397649408)), (55201/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548525460760407/9671406556917033397649408), (-387079263151/2417851639229258349412352)), (51757/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628944761413795/302231454903657293676544), (-1354240993253/604462909807314587353088)), (90587/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886331486409307/75557863725914323419136), (-549909078777/18889465931478580854784)), (147227/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81027783705987/295147905179352825856), (-412212025659/1180591620717411303424)), (110441/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619943427424319/590295810358705651712), (-1132869245571/295147905179352825856)), (9493/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821594987201207/73786976294838206464), (-2830033286727/73786976294838206464)), (47477/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820543981798723/9223372036854775808), (-49700747821/144115188075855872)), (106857/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591794572252835/1152921504606846976), (-1588588692941/576460752303423488)), (106899/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192665727914059/144115188075855872), (-693976608697/36028797018963968)), (187169/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488769528569477/36028797018963968), (-4155625842613/36028797018963968)), (280943/36028797018963968), by norm_num⟩
  | 3 => ⟨((371420254090773/2251799813685248), (-2590077006331/4503599627370496)), (351511/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220819234102319/4503599627370496), (-10317296395047/4503599627370496)), (352013/2251799813685248), by norm_num⟩
  | 1 => ⟨((2205471496986973/2251799813685248), (-15368845680985/2251799813685248)), (1058559/2251799813685248), by norm_num⟩
  | 0 => ⟨((67490988145979/70368744177664), (-30311867274075/2251799813685248)), (265909/281474976710656), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((67490988145979/70368744177664), (-30311867274075/2251799813685248)), (1014362336278819949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2070981375352835/2251799813685248), (-29072252159453/1125899906842624)), (4137825/2251799813685248), by norm_num⟩
  | 2 => ⟨((1903181200935501/2251799813685248), (-13368882170581/281474976710656)), (7824809/2251799813685248), by norm_num⟩
  | 3 => ⟨((801727607618403/1125899906842624), (-180786267553199/2251799813685248)), (13970071/2251799813685248), by norm_num⟩
  | 4 => ⟨((563634683977531/1125899906842624), (-128733771887545/1125899906842624)), (22138719/2251799813685248), by norm_num⟩
  | 5 => ⟨((1069763559364591/4503599627370496), (-515561416385935/4503599627370496)), (13614133/1125899906842624), by norm_num⟩
  | 6 => ⟨((780345120857475/18014398509481984), (-489855992093229/9007199254740992)), (153355199/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-752969633/16777216)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1527595925/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((32767337776231/18014398509481984), (-1204949880812841/18014398509481984)), (24278721/2251799813685248), by norm_num⟩
  | 1 => ⟨((-48991107/8589934592), (112596553/536870912)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((38402833/4294967296), (-706091681/2147483648)), (231/4294967296), by norm_num⟩
  | 3 => ⟨((-40137287/4294967296), (737982127/2147483648)), (243/4294967296), by norm_num⟩
  | 4 => ⟨((15731279/2147483648), (-1156969345/4294967296)), (3/67108864), by norm_num⟩
  | 5 => ⟨((-39460267/8589934592), (1451068275/8589934592)), (243/8589934592), by norm_num⟩
  | 6 => ⟨((2577655/1073741824), (-758302697/8589934592)), (1/67108864), by norm_num⟩
  | 7 => ⟨((-18473651/17179869184), (1358659269/34359738368)), (231/34359738368), by norm_num⟩
  | 8 => ⟨((28962013/68719476736), (-532508535/34359738368)), (183/68719476736), by norm_num⟩
  | 9 => ⟨((-10090025/68719476736), (1484157717/274877906944)), (257/274877906944), by norm_num⟩
  | 10 => ⟨((6327443/137438953472), (-1861427175/1099511627776)), (81/274877906944), by norm_num⟩
  | 11 => ⟨((-28857689/2199023255552), (1061180753/2199023255552)), (187/2199023255552), by norm_num⟩
  | 12 => ⟨((30161039/8796093022208), (-34659647/274877906944)), (197/8796093022208), by norm_num⟩
  | 13 => ⟨((-29098389/35184372088832), (1070031977/35184372088832)), (3/549755813888), by norm_num⟩
  | 14 => ⟨((52135903/281474976710656), (-958594021/140737488355328)), (173/140737488355328), by norm_num⟩
  | 15 => ⟨((-21796243/562949953421312), (1603021871/1125899906842624)), (291/1125899906842624), by norm_num⟩
  | 16 => ⟨((34170997/4503599627370496), (-1256566451/4503599627370496)), (115/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-2010723177701/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777795761745291/633825300114114700748351602688), (-148569575823/39614081257132168796771975168)), (92435/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888647327311295/39614081257132168796771975168), (-1336813041883/19807040628566084398385987584)), (26001/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888354123544707/2475880078570760549798248448), (-2839944057399/2475880078570760549798248448)), (55261/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770020520044849/154742504910672534362390528), (-2839062830545/154742504910672534362390528)), (110541/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548456549708307/9671406556917033397649408), (-2660685445553/9671406556917033397649408)), (51827/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257829073677039/604462909807314587353088), (-2327164195433/604462909807314587353088)), (45359/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943116485952263/37778931862957161709568), (-1889944225229/37778931862957161709568)), (147455/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296370404688469/4722366482869645213696), (-2833382966777/4722366482869645213696)), (55313/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809920544383783/295147905179352825856), (-1946705698847/295147905179352825856)), (76083/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821466459593411/73786976294838206464), (-2431515839579/36893488147419103232)), (190291/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820398559083049/9223372036854775808), (-2732891374895/4611686018427387904)), (214193/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591648115693271/1152921504606846976), (-5459379470331/1152921504606846976)), (214337/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192536418921577/144115188075855872), (-4769762388781/144115188075855872)), (187707/144115188075855872), by norm_num⟩
  | 4 => ⟨((744286627492073/18014398509481984), (-3570138432707/18014398509481984)), (281885/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485431651703909/9007199254740992), (-4450127526667/4503599627370496)), (176463/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110154258224141/2251799813685248), (-17725439570733/4503599627370496)), (353783/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204675727397333/2251799813685248), (-3300148789465/281474976710656)), (1065649/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158002965805707/2251799813685248), (-13014683825309/562949953421312)), (2148585/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158002965805707/2251799813685248), (-13014683825309/562949953421312)), (8196201333052825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066909616129681/2251799813685248), (-24945135995971/562949953421312)), (4217521/2251799813685248), by norm_num⟩
  | 2 => ⟨((118298682080565/140737488355328), (-183175577695263/2251799813685248)), (4058115/1125899906842624), by norm_num⟩
  | 3 => ⟨((1576098683709957/2251799813685248), (-76985278350235/562949953421312)), (3741213/562949953421312), by norm_num⟩
  | 4 => ⟨((1061044288639245/2251799813685248), (-431073473353827/2251799813685248)), (12520819/1125899906842624), by norm_num⟩
  | 5 => ⟨((834879403854519/4503599627370496), (-812484385345797/4503599627370496)), (8296713/562949953421312), by norm_num⟩
  | 6 => ⟨((32767337776231/18014398509481984), (-1204949880812841/18014398509481984)), (24278721/2251799813685248), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1527595925/33554432)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-1548330741/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-647195966962273/18014398509481984), (-1884807092937/35184372088832)), (211578069/18014398509481984), by norm_num⟩
  | 1 => ⟨((490384965/4294967296), (365601709/2147483648)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((-194808727/1073741824), (-1161901911/4294967296)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((825483495/4294967296), (1230862273/4294967296)), (139/2147483648), by norm_num⟩
  | 4 => ⟨((-327928873/2147483648), (-3820065/16777216)), (223/4294967296), by norm_num⟩
  | 5 => ⟨((833740489/8589934592), (621587057/4294967296)), (143/4294967296), by norm_num⟩
  | 6 => ⟨((-220806013/4294967296), (-329239521/4294967296)), (153/8589934592), by norm_num⟩
  | 7 => ⟨((801981023/34359738368), (1195818195/34359738368)), (35/4294967296), by norm_num⟩
  | 8 => ⟨((-637184715/68719476736), (-950093649/68719476736)), (225/68719476736), by norm_num⟩
  | 9 => ⟨((112500407/34359738368), (670988613/137438953472)), (161/137438953472), by norm_num⟩
  | 10 => ⟨((-572051759/549755813888), (-852975173/549755813888)), (207/549755813888), by norm_num⟩
  | 11 => ⟨((165273753/549755813888), (30804557/68719476736)), (241/2199023255552), by norm_num⟩
  | 12 => ⟨((-700331845/8796093022208), (-1044251097/8796093022208)), (257/8796093022208), by norm_num⟩
  | 13 => ⟨((684828401/35184372088832), (1021134215/35184372088832)), (253/35184372088832), by norm_num⟩
  | 14 => ⟨((-621834721/140737488355328), (-231801393/35184372088832)), (29/17592186044416), by norm_num⟩
  | 15 => ⟨((131748281/140737488355328), (785789125/562949953421312)), (99/281474976710656), by norm_num⟩
  | 16 => ⟨((-418703129/2251799813685248), (-1248640069/4503599627370496)), (79/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (-2815666408277/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777736322167699/633825300114114700748351602688), (-832132438221/158456325028528675187087900672)), (92529/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472145078586395/9903520314283042199192993792), (-1871850910121/19807040628566084398385987584)), (26029/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888282727707283/2475880078570760549798248448), (-3976570318437/2475880078570760549798248448)), (110647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442487226400615/38685626227668133590597632), (-1987659397987/77371252455336267181195264)), (110675/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387097294777169/2417851639229258349412352), (-3725532071921/9671406556917033397649408)), (103787/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257769892576479/604462909807314587353088), (-3258511762113/604462909807314587353088)), (90843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943068184219745/37778931862957161709568), (-5292591170901/75557863725914323419136)), (73837/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162037196585205/590295810358705651712), (-495908162455/590295810358705651712)), (27701/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809870164575077/295147905179352825856), (-5451452393727/590295810358705651712)), (152433/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821339588285485/73786976294838206464), (-6809012873473/73786976294838206464)), (95329/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227531820505557/1152921504606846976), (-7652854020155/9223372036854775808)), (214651/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795751271792859/576460752303423488), (-955469455603/144115188075855872)), (214853/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192407274550367/144115188075855872), (-3339031066137/72057594037927936)), (2941/2251799813685248), by norm_num⟩
  | 4 => ⟨((1488376014409193/36028797018963968), (-2499168525217/9007199254740992)), (282789/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485178964333721/9007199254740992), (-12460174431913/9007199254740992)), (354283/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219784852895599/4503599627370496), (-12406802442939/2251799813685248)), (710963/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203844932334091/2251799813685248), (-4619307267715/281474976710656)), (1072455/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156162696948527/2251799813685248), (-9106321650417/281474976710656)), (1084531/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2156162696948527/2251799813685248), (-9106321650417/281474976710656)), (4137157444480514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2062230550635165/2251799813685248), (-139513013046467/2251799813685248)), (2147113/1125899906842624), by norm_num⟩
  | 2 => ⟨((1879976602465177/2251799813685248), (-255536034746117/2251799813685248)), (8397537/2251799813685248), by norm_num⟩
  | 3 => ⟨((385137850585109/562949953421312), (-426682481710675/2251799813685248)), (7963873/1125899906842624), by norm_num⟩
  | 4 => ⟨((973106343528897/2251799813685248), (-583823030412025/2251799813685248)), (13914915/1125899906842624), by norm_num⟩
  | 5 => ⟨((538313060773187/4503599627370496), (-1009187212716621/4503599627370496)), (76967909/4503599627370496), by norm_num⟩
  | 6 => ⟨((-647195966962273/18014398509481984), (-1884807092937/35184372088832)), (211578069/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-1548330741/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1568218997/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-519328139773969/9007199254740992), (-423696445187331/18014398509481984)), (3138109/281474976710656), by norm_num⟩
  | 1 => ⟨((99638271/536870912), (325161515/4294967296)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((-1282892887/4294967296), (-261663635/2147483648)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((1376490967/4294967296), (561508499/4294967296)), (137/2147483648), by norm_num⟩
  | 4 => ⟨((-553844187/2147483648), (-451856533/4294967296)), (223/4294967296), by norm_num⟩
  | 5 => ⟨((356551133/2147483648), (145447007/2147483648)), (289/8589934592), by norm_num⟩
  | 6 => ⟨((-765129215/8589934592), (-78029309/2147483648)), (157/8589934592), by norm_num⟩
  | 7 => ⟨((175918281/4294967296), (574095215/34359738368)), (291/34359738368), by norm_num⟩
  | 8 => ⟨((-283129551/17179869184), (-230992651/34359738368)), (59/17179869184), by norm_num⟩
  | 9 => ⟨((810096771/137438953472), (165230369/68719476736)), (85/68719476736), by norm_num⟩
  | 10 => ⟨((-1043040365/549755813888), (-13296401/17179869184)), (221/549755813888), by norm_num⟩
  | 11 => ⟨((305219765/549755813888), (124507531/549755813888)), (261/2199023255552), by norm_num⟩
  | 12 => ⟨((-1309952697/8796093022208), (-534365709/8796093022208)), (141/4398046511104), by norm_num⟩
  | 13 => ⟨((1297407713/35184372088832), (529248265/35184372088832)), (141/17592186044416), by norm_num⟩
  | 14 => ⟨((-596599189/70368744177664), (-486738413/140737488355328)), (261/140737488355328), by norm_num⟩
  | 15 => ⟨((1024201977/562949953421312), (52225017/70368744177664)), (113/281474976710656), by norm_num⟩
  | 16 => ⟨((-412097373/1125899906842624), (-336211689/2251799813685248)), (183/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-3587745458083/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444419599947171/158456325028528675187087900672), (-2120496729597/316912650057057350374175801344)), (46309/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118032185326379/2475880078570760549798248448), (-298122181919/2475880078570760549798248448)), (104223/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888213041112947/2475880078570760549798248448), (-5066639861477/2475880078570760549798248448)), (110767/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769878934561851/154742504910672534362390528), (-2532511697621/77371252455336267181195264)), (55401/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548323279307015/9671406556917033397649408), (-4746742431367/9671406556917033397649408)), (103915/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157213991075767/75557863725914323419136), (-2075841590227/302231454903657293676544)), (90963/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886041612057765/75557863725914323419136), (-6743268008803/75557863725914323419136)), (36971/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296226011733563/4722366482869645213696), (-5054637170745/4722366482869645213696)), (55487/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619641131867437/590295810358705651712), (-6945555836411/590295810358705651712)), (9543/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1821214392348635/73786976294838206464), (-4337546626339/36893488147419103232)), (95505/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455028018249477/2305843009213693952), (-9750065321837/9223372036854775808)), (53773/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99459875044335/72057594037927936), (-9738306513087/1152921504606846976)), (215349/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74517406147089/9007199254740992), (-8507802498489/144115188075855872)), (188719/144115188075855872), by norm_num⟩
  | 4 => ⟨((744089132771011/18014398509481984), (-12735304743015/36028797018963968)), (141829/18014398509481984), by norm_num⟩
  | 3 => ⟨((742461897591991/4503599627370496), (-15873005555529/9007199254740992)), (88897/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219250724691695/4503599627370496), (-7901981624413/1125899906842624)), (178557/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202984820786233/2251799813685248), (-47067698324723/2251799813685248)), (1078999/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154210113972561/2251799813685248), (-5797796891631/140737488355328)), (2188767/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154210113972561/2251799813685248), (-5797796891631/140737488355328)), (8349483498580168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1028514144130131/1125899906842624), (-177488924218639/2251799813685248)), (4368155/2251799813685248), by norm_num⟩
  | 2 => ⟨((1865113868008207/2251799813685248), (-324273708303677/2251799813685248)), (2167315/562949953421312), by norm_num⟩
  | 3 => ⟨((374533326878925/562949953421312), (-537176872217447/2251799813685248)), (4214489/562949953421312), by norm_num⟩
  | 4 => ⟨((868569400865931/2251799813685248), (-714772742590297/2251799813685248)), (30474441/2251799813685248), by norm_num⟩
  | 5 => ⟨((216282752215011/4503599627370496), (-1102815141939133/4503599627370496)), (85711825/4503599627370496), by norm_num⟩
  | 6 => ⟨((-519328139773969/9007199254740992), (-423696445187331/18014398509481984)), (3138109/281474976710656), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1568218997/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-94291587/33554432), (-793663559/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1066499927330697/18014398509481984), (196434479686305/18014398509481984)), (186404275/18014398509481984), by norm_num⟩
  | 1 => ⟨((1656894551/8589934592), (-305176973/8589934592)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-168697575/536870912), (124287005/2147483648)), (15/268435456), by norm_num⟩
  | 3 => ⟨((183210995/536870912), (-134979687/2147483648)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((-1193838217/4294967296), (219888425/4294967296)), (27/536870912), by norm_num⟩
  | 5 => ⟨((1555856065/8589934592), (-286567087/8589934592)), (71/2147483648), by norm_num⟩
  | 6 => ⟨((-1689709753/17179869184), (155610539/8589934592)), (155/8589934592), by norm_num⟩
  | 7 => ⟨((1572924999/34359738368), (-72427737/8589934592)), (291/34359738368), by norm_num⟩
  | 8 => ⟨((-640592687/34359738368), (235976559/68719476736)), (239/68719476736), by norm_num⟩
  | 9 => ⟨((14493839/2147483648), (-170852091/137438953472)), (87/68719476736), by norm_num⟩
  | 10 => ⟨((-1208891563/549755813888), (222661043/549755813888)), (229/549755813888), by norm_num⟩
  | 11 => ⟨((716124621/1099511627776), (-263800427/2199023255552)), (137/1099511627776), by norm_num⟩
  | 12 => ⟨((-777734383/4398046511104), (286495753/8796093022208)), (75/2199023255552), by norm_num⟩
  | 13 => ⟨((194917977/4398046511104), (-287209483/35184372088832)), (303/35184372088832), by norm_num⟩
  | 14 => ⟨((-362892335/35184372088832), (267358921/140737488355328)), (71/35184372088832), by norm_num⟩
  | 15 => ⟨((1261160811/562949953421312), (-232288313/562949953421312)), (249/562949953421312), by norm_num⟩
  | 16 => ⟨((-513622959/1125899906842624), (189204437/2251799813685248)), (51/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643663995/5070602400912917605986812821504), (3855011381651/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777624822202209/633825300114114700748351602688), (4556667813795/633825300114114700748351602688)), (92649/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888454624506275/39614081257132168796771975168), (5124983798523/39614081257132168796771975168)), (104259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888148837742543/2475880078570760549798248448), (5443731847357/2475880078570760549798248448)), (110809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769814628555133/154742504910672534362390528), (1360493343543/38685626227668133590597632)), (110847/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387065720871765/2417851639229258349412352), (5099982171497/9671406556917033397649408)), (103959/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628829486725727/302231454903657293676544), (4460617107131/604462909807314587353088)), (22751/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885955356176995/75557863725914323419136), (7245002844417/75557863725914323419136)), (147957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296161141806181/4722366482869645213696), (1357672723167/1180591620717411303424)), (55517/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50610988966957/18446744073709551616), (7462227748551/590295810358705651712)), (152777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821102103909413/73786976294838206464), (4660165172729/36893488147419103232)), (47783/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909992577770409/4611686018427387904), (10475128426761/9223372036854775808)), (53811/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99451896511591/72057594037927936), (5231167086227/576460752303423488)), (6735/36028797018963968), by norm_num⟩
  | 5 => ⟨((1192165970378561/144115188075855872), (9140162288173/144115188075855872)), (188891/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488007823867621/36028797018963968), (855094798313/2251799813685248)), (283959/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484707872529417/9007199254740992), (8525849928751/4503599627370496)), (44505/1125899906842624), by norm_num⟩
  | 2 => ⟨((554702583312681/1125899906842624), (16976556835623/2251799813685248)), (357681/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101151548447637/1125899906842624), (25277506918383/1125899906842624)), (135159/281474976710656), by norm_num⟩
  | 0 => ⟨((1076381742099695/1125899906842624), (24904438778347/562949953421312)), (68613/70368744177664), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076381742099695/1125899906842624), (24904438778347/562949953421312)), (261737823754763581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1026837930632955/1125899906842624), (190472940163405/2251799813685248)), (4392367/2251799813685248), by norm_num⟩
  | 2 => ⟨((928436128469331/1125899906842624), (173714233858893/1125899906842624)), (4377443/1125899906842624), by norm_num⟩
  | 3 => ⟨((738801917067933/1125899906842624), (71623849404275/281474976710656)), (17140425/2251799813685248), by norm_num⟩
  | 4 => ⟨((102972887951463/281474976710656), (375989637629909/1125899906842624)), (3902219/281474976710656), by norm_num⟩
  | 5 => ⟨((50246816208177/2251799813685248), (550197950510889/2251799813685248)), (10922765/562949953421312), by norm_num⟩
  | 6 => ⟨((-1066499927330697/18014398509481984), (196434479686305/18014398509481984)), (186404275/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94291587/33554432), (-793663559/16777216)), (1/16777216), by norm_num⟩, -8, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1605714003/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-782133944708701/18014398509481984), (700109594947323/18014398509481984)), (48329981/4503599627370496), by norm_num⟩
  | 1 => ⟨((614592049/4294967296), (-275069119/2147483648)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((-506398783/2147483648), (906582943/4294967296)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((278167963/1073741824), (-497991581/2147483648)), (281/4294967296), by norm_num⟩
  | 4 => ⟨((-916796227/4294967296), (410324753/2147483648)), (117/2147483648), by norm_num⟩
  | 5 => ⟨((604322161/4294967296), (-540945379/4294967296)), (39/1073741824), by norm_num⟩
  | 6 => ⟨((-82989469/1073741824), (594289241/8589934592)), (173/8589934592), by norm_num⟩
  | 7 => ⟨((625188003/17179869184), (-69952871/2147483648)), (165/17179869184), by norm_num⟩
  | 8 => ⟨((-515129417/34359738368), (230553251/17179869184)), (137/34359738368), by norm_num⟩
  | 9 => ⟨((377285005/68719476736), (-675436359/137438953472)), (203/137438953472), by norm_num⟩
  | 10 => ⟨((-994775863/549755813888), (890451221/549755813888)), (269/549755813888), by norm_num⟩
  | 11 => ⟨((596112539/1099511627776), (-33349795/68719476736)), (163/1099511627776), by norm_num⟩
  | 12 => ⟨((-654896561/4398046511104), (293107957/2199023255552)), (181/4398046511104), by norm_num⟩
  | 13 => ⟨((332066497/8796093022208), (-594483699/17592186044416)), (93/8796093022208), by norm_num⟩
  | 14 => ⟨((-625392573/70368744177664), (559806083/70368744177664)), (177/70368744177664), by norm_num⟩
  | 15 => ⟨((1099302345/562949953421312), (-984015747/562949953421312)), (157/281474976710656), by norm_num⟩
  | 16 => ⟨((-905780299/2251799813685248), (202697211/562949953421312)), (65/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (3141216833769/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777578448563261/633825300114114700748351602688), (3712754737701/633825300114114700748351602688)), (92567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944201335849149/19807040628566084398385987584), (2087907132809/19807040628566084398385987584)), (104161/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888093929349727/2475880078570760549798248448), (4435515088311/2475880078570760549798248448)), (55349/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884880023856223/77371252455336267181195264), (554258384361/19342813113834066795298816)), (13841/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548212061683319/9671406556917033397649408), (4155399879059/9671406556917033397649408)), (103841/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628807425894079/302231454903657293676544), (3634437464553/604462909807314587353088)), (45447/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885884309194841/75557863725914323419136), (368942463681/4722366482869645213696)), (73881/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296108425268241/4722366482869645213696), (4424789505035/4722366482869645213696)), (27719/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404870021140153/147573952589676412928), (379999547423/36893488147419103232)), (152541/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821014032984289/73786976294838206464), (1898463932681/18446744073709551616)), (190807/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909943986222607/4611686018427387904), (8534658267441/9223372036854775808)), (214837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795567763262319/576460752303423488), (2131032804591/288230376151711744)), (107531/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192085658577509/144115188075855872), (3723392634363/72057594037927936)), (188433/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487892644845433/36028797018963968), (11146552245091/36028797018963968)), (70789/9007199254740992), by norm_num⟩
  | 3 => ⟨((371143278029249/2251799813685248), (6945960290489/4503599627370496)), (177417/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218568285639675/4503599627370496), (27660332407421/4503599627370496)), (712343/4503599627370496), by norm_num⟩
  | 1 => ⟨((275251015785081/281474976710656), (20591388462183/1125899906842624)), (1075223/2251799813685248), by norm_num⟩
  | 0 => ⟨((269055308452199/281474976710656), (40570479028059/1125899906842624)), (2177407/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((269055308452199/281474976710656), (40570479028059/1125899906842624)), (8306148537642668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2054545298925989/2251799813685248), (77560732939815/1125899906842624)), (2159793/1125899906842624), by norm_num⟩
  | 2 => ⟨((931942016038575/1125899906842624), (141533042390619/1125899906842624)), (8477527/2251799813685248), by norm_num⟩
  | 3 => ⟨((11775085339695/17592186044416), (14643907071575/70368744177664)), (1010349/140737488355328), by norm_num⟩
  | 4 => ⟨((911312846161617/2251799813685248), (156827132263387/562949953421312)), (14184307/1125899906842624), by norm_num⟩
  | 5 => ⟨((97027966318355/1125899906842624), (1015497590076901/4503599627370496)), (77535413/4503599627370496), by norm_num⟩
  | 6 => ⟨((-782133944708701/18014398509481984), (700109594947323/18014398509481984)), (48329981/4503599627370496), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1605714003/33554432)), (1/16777216), by norm_num⟩, -8, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile001Terms3
