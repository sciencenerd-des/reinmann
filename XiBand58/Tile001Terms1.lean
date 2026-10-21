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
namespace Reinmann.XiBand58.Tile001Terms1
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
  | 0 => ⟨((15/16), (4659/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4659/320))
  have he : value ((15/16), (4659/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-69118709/33554432), (-1073413547/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((15061512535767/140737488355328), (-155925899317219/2251799813685248)), (114069927/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1009934251/4294967296), (653465687/4294967296)), (61/2147483648), by norm_num⟩
  | 2 => ⟨((1109526179/4294967296), (-358952717/2147483648)), (17/536870912), by norm_num⟩
  | 3 => ⟨((-812626063/4294967296), (525799821/4294967296)), (51/2147483648), by norm_num⟩
  | 4 => ⟨((892760979/8589934592), (-577650145/8589934592)), (57/4294967296), by norm_num⟩
  | 5 => ⟨((-392319273/8589934592), (253845419/8589934592)), (51/8589934592), by norm_num⟩
  | 6 => ⟨((1149351399/68719476736), (-371836929/34359738368)), (19/8589934592), by norm_num⟩
  | 7 => ⟨((-721538041/137438953472), (233431211/68719476736)), (49/68719476736), by norm_num⟩
  | 8 => ⟨((792690559/549755813888), (-256450397/274877906944)), (55/274877906944), by norm_num⟩
  | 9 => ⟨((-774097413/2199023255552), (500870325/2199023255552)), (109/2199023255552), by norm_num⟩
  | 10 => ⟨((680346345/8796093022208), (-440209835/8796093022208)), (49/4398046511104), by norm_num⟩
  | 11 => ⟨((-1087180881/70368744177664), (703447177/70368744177664)), (159/70368744177664), by norm_num⟩
  | 12 => ⟨((99532523/35184372088832), (-128802619/70368744177664)), (119/281474976710656), by norm_num⟩
  | 13 => ⟨((-1076653813/2251799813685248), (696635767/2251799813685248)), (41/562949953421312), by norm_num⟩
  | 14 => ⟨((675900063/9007199254740992), (-437332923/9007199254740992)), (105/9007199254740992), by norm_num⟩
  | 15 => ⟨((-396027795/36028797018963968), (512489945/72057594037927936)), (125/72057594037927936), by norm_num⟩
  | 16 => ⟨((870162005/576460752303423488), (-70378469/72057594037927936)), (35/144115188075855872), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (-748076906185/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889395680037203/316912650057057350374175801344), (-885331634377/633825300114114700748351602688)), (721/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((944883643382953/19807040628566084398385987584), (-248954707295/9903520314283042199192993792)), (103829/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944771991748903/1237940039285380274899124224), (-1057835213761/2475880078570760549798248448)), (110325/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110700641924119/9671406556917033397649408), (-264396306303/38685626227668133590597632)), (27583/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549571824919977/9671406556917033397649408), (-123902577163/1208925819614629174706176)), (103445/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629402411649963/302231454903657293676544), (-867052600515/604462909807314587353088)), (45261/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887818347022299/75557863725914323419136), (-1408462971333/75557863725914323419136)), (18389/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297559245091877/4722366482869645213696), (-65994506673/295147905179352825856)), (110347/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621475433738683/590295810358705651712), (-181396554861/73786976294838206464)), (151747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823508924382983/73786976294838206464), (-1812906124929/73786976294838206464)), (47429/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822695689747839/9223372036854775808), (-509515929839/2305843009213693952)), (213473/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398486110561809/288230376151711744), (-2036245683719/1152921504606846976)), (106763/576460752303423488), by norm_num⟩
  | 5 => ⟨((298636199551659/36028797018963968), (-889835908523/72057594037927936)), (11681/9007199254740992), by norm_num⟩
  | 4 => ⟨((1491584006467315/36028797018963968), (-666356685489/9007199254740992)), (280465/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489191900351287/9007199254740992), (-3324653679713/9007199254740992)), (175397/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227819401145393/4503599627370496), (-6627965929607/4503599627370496)), (702227/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107958941170725/1125899906842624), (-2472190575711/562949953421312)), (263737/562949953421312), by norm_num⟩
  | 0 => ⟨((2180389752129797/2251799813685248), (-4891444308137/562949953421312)), (1058183/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2180389752129797/2251799813685248), (-4891444308137/562949953421312)), (4036647800925826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527768567909917/562949953421312), (-18945298738827/1125899906842624)), (4135281/2251799813685248), by norm_num⟩
  | 2 => ⟨((1978505751677125/2251799813685248), (-35522636153531/1125899906842624)), (61663/17592186044416), by norm_num⟩
  | 3 => ⟨((868069522642019/1125899906842624), (-124845449435353/2251799813685248)), (7183955/1125899906842624), by norm_num⟩
  | 4 => ⟨((1331642528830137/2251799813685248), (-192511837041165/2251799813685248)), (11874261/1125899906842624), by norm_num⟩
  | 5 => ⟨((1542065157512125/4503599627370496), (-455381420584957/4503599627370496)), (16074437/1125899906842624), by norm_num⟩
  | 6 => ⟨((15061512535767/140737488355328), (-155925899317219/2251799813685248)), (114069927/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-1073413547/33554432)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-9054133/4194304), (-281221371/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-266259172448831/4503599627370496), (-893479338353699/9007199254740992)), (93352677/9007199254740992), by norm_num⟩
  | 1 => ⟨((584682847/4294967296), (490501453/2147483648)), (105/4294967296), by norm_num⟩
  | 2 => ⟨((-168285251/1073741824), (-564710667/2147483648)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((258327407/2147483648), (866862909/4294967296)), (3/134217728), by norm_num⟩
  | 4 => ⟨((-594820837/8589934592), (-499006403/4294967296)), (113/8589934592), by norm_num⟩
  | 5 => ⟨((547850237/17179869184), (229800941/4294967296)), (53/8589934592), by norm_num⟩
  | 6 => ⟨((-105122649/8589934592), (-352757481/17179869184)), (21/8589934592), by norm_num⟩
  | 7 => ⟨((276632965/68719476736), (232072605/34359738368)), (113/137438953472), by norm_num⟩
  | 8 => ⟨((-318485471/274877906944), (-534366921/274877906944)), (133/549755813888), by norm_num⟩
  | 9 => ⟨((651857687/2199023255552), (136713923/274877906944)), (69/1099511627776), by norm_num⟩
  | 10 => ⟨((-600383117/8796093022208), (-251836353/2199023255552)), (129/8796093022208), by norm_num⟩
  | 11 => ⟨((502702987/35184372088832), (843454011/35184372088832)), (55/17592186044416), by norm_num⟩
  | 12 => ⟨((-771677603/281474976710656), (-1294749755/281474976710656)), (171/281474976710656), by norm_num⟩
  | 13 => ⟨((273362053/562949953421312), (917314303/1125899906842624)), (123/1125899906842624), by norm_num⟩
  | 14 => ⟨((-719359301/9007199254740992), (-1206968137/9007199254740992)), (41/2251799813685248), by norm_num⟩
  | 15 => ⟨((220851467/18014398509481984), (23159557/1125899906842624)), (51/18014398509481984), by norm_num⟩
  | 16 => ⟨((-31783081/18014398509481984), (-853229611/288230376151711744)), (15/36028797018963968), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (-343282671621/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444658466134313/158456325028528675187087900672), (-3249606705169/633825300114114700748351602688)), (46261/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944794920919981/19807040628566084398385987584), (-456888606015/4951760157141521099596496896)), (52053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889355102933739/2475880078570760549798248448), (-970674228269/618970019642690137449562112)), (55319/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885510501038773/77371252455336267181195264), (-1940866922309/77371252455336267181195264)), (13833/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549393973392819/9671406556917033397649408), (-3638102450817/9671406556917033397649408)), (3243/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314662197856791/151115727451828646838272), (-3182316876443/604462909807314587353088)), (5677/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((117972751488935/4722366482869645213696), (-5169347787705/75557863725914323419136)), (18457/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((20271372318831/73786976294838206464), (-1937666949917/2361183241434822606848)), (27697/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405302785344131/147573952589676412928), (-5325860121011/590295810358705651712)), (76205/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823176919574269/73786976294838206464), (-3326620490195/36893488147419103232)), (95313/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911159966955145/4611686018427387904), (-7479283318839/9223372036854775808)), (107305/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796782939449549/576460752303423488), (-7472271764685/1152921504606846976)), (26851/288230376151711744), by norm_num⟩
  | 5 => ⟨((597105202206689/72057594037927936), (-408147242555/9007199254740992)), (94089/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491076132985057/36028797018963968), (-611236575397/2251799813685248)), (70677/18014398509481984), by norm_num⟩
  | 3 => ⟨((372136526533553/2251799813685248), (-6098602826625/4503599627370496)), (177079/9007199254740992), by norm_num⟩
  | 2 => ⟨((139155945331429/281474976710656), (-12155985303273/2251799813685248)), (355323/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213850342131371/2251799813685248), (-36262333083507/2251799813685248)), (535903/2251799813685248), by norm_num⟩
  | 0 => ⟨((1087966851917143/1125899906842624), (-17926261893585/562949953421312)), (1083521/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1087966851917143/1125899906842624), (-17926261893585/562949953421312)), (4133304604537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((525085072048887/562949953421312), (-69289209815103/1125899906842624)), (2163039/2251799813685248), by norm_num⟩
  | 2 => ⟨((1950539884201309/2251799813685248), (-64628710788337/562949953421312)), (1075333/562949953421312), by norm_num⟩
  | 3 => ⟨((207488244126611/281474976710656), (-111964551458821/562949953421312)), (2109841/562949953421312), by norm_num⟩
  | 4 => ⟨((1134519500706699/2251799813685248), (-165068514850577/562949953421312)), (15799087/2251799813685248), by norm_num⟩
  | 5 => ⟨((755993191571647/4503599627370496), (-1330657888236949/4503599627370496)), (50370553/4503599627370496), by norm_num⟩
  | 6 => ⟨((-266259172448831/4503599627370496), (-893479338353699/9007199254740992)), (93352677/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-281221371/8388608)), (1/33554432), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-75431263/33554432), (-1171447515/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-892133485620301/9007199254740992), (165023088099279/4503599627370496)), (167998379/9007199254740992), by norm_num⟩
  | 1 => ⟨((510035197/2147483648), (-377376635/4294967296)), (195/4294967296), by norm_num⟩
  | 2 => ⟨((-305752747/1073741824), (452454825/4294967296)), (59/1073741824), by norm_num⟩
  | 3 => ⟨((244387689/1073741824), (-361646429/4294967296)), (191/4294967296), by norm_num⟩
  | 4 => ⟨((-146504021/1073741824), (433595131/8589934592)), (231/8589934592), by norm_num⟩
  | 5 => ⟨((562082079/8589934592), (-207943143/8589934592)), (223/17179869184), by norm_num⟩
  | 6 => ⟨((-56158915/2147483648), (332417253/34359738368)), (45/8589934592), by norm_num⟩
  | 7 => ⟨((1231206371/137438953472), (-1779245/536870912)), (249/137438953472), by norm_num⟩
  | 8 => ⟨((-46129749/17179869184), (273052363/274877906944)), (301/549755813888), by norm_num⟩
  | 9 => ⟨((196647657/274877906944), (-291000431/1099511627776)), (81/549755813888), by norm_num⟩
  | 10 => ⟨((-1508929559/8796093022208), (279115423/4398046511104)), (313/8796093022208), by norm_num⟩
  | 11 => ⟨((1315729111/35184372088832), (-486756039/35184372088832)), (275/35184372088832), by norm_num⟩
  | 12 => ⟨((-1051660205/140737488355328), (389063335/140737488355328)), (111/70368744177664), by norm_num⟩
  | 13 => ⟨((775929549/562949953421312), (-574112697/1125899906842624)), (165/562949953421312), by norm_num⟩
  | 14 => ⟨((-1063198741/4503599627370496), (393332035/4503599627370496)), (57/1125899906842624), by norm_num⟩
  | 15 => ⟨((1359700925/36028797018963968), (-503023481/36028797018963968)), (147/18014398509481984), by norm_num⟩
  | 16 => ⟨((-815105105/144115188075855872), (301549407/144115188075855872)), (89/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (3630711280045/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889245960396811/316912650057057350374175801344), (4295528363167/633825300114114700748351602688)), (92623/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118089371867005/2475880078570760549798248448), (2415749336823/19807040628566084398385987584)), (26057/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889184944451553/2475880078570760549798248448), (2566143740345/1237940039285380274899124224)), (55387/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885425268231629/77371252455336267181195264), (5130960260015/154742504910672534362390528)), (55405/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193654229475849/1208925819614629174706176), (4808865311737/9671406556917033397649408)), (51961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629254172626861/302231454903657293676544), (2103173742573/302231454903657293676544)), (90969/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235916898569063/9444732965739290427392), (6832672118703/75557863725914323419136)), (147895/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297195668602753/4722366482869645213696), (2561096217763/2361183241434822606848)), (110983/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810486778048335/295147905179352825856), (7039259237093/590295810358705651712)), (76351/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822878641643579/73786976294838206464), (4396721443315/36893488147419103232)), (191029/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227747824003115/1152921504606846976), (1235610433127/1152921504606846976)), (107557/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796613158927509/576460752303423488), (9875213334595/1152921504606846976)), (107687/576460752303423488), by norm_num⟩
  | 5 => ⟨((298477699654689/36028797018963968), (8629939099819/144115188075855872)), (23593/18014398509481984), by norm_num⟩
  | 4 => ⟨((372655440297653/9007199254740992), (6461589678387/18014398509481984)), (141851/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487969493386305/9007199254740992), (8057991818745/4503599627370496)), (355653/9007199254740992), by norm_num⟩
  | 2 => ⟨((139082256574557/281474976710656), (16059069351355/2251799813685248)), (178597/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106008923496067/1125899906842624), (23946569382735/1125899906842624)), (134913/281474976710656), by norm_num⟩
  | 0 => ⟨((1086007986148673/1125899906842624), (11831627924983/281474976710656)), (273703/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1086007986148673/1125899906842624), (11831627924983/281474976710656)), (1044094086767101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((522770070463091/562949953421312), (91299358584757/1125899906842624)), (551021/281474976710656), by norm_num⟩
  | 2 => ⟨((963512481719733/1125899906842624), (169565951042431/1125899906842624)), (556375/140737488355328), by norm_num⟩
  | 3 => ⟨((199752146085429/281474976710656), (36277405591547/140737488355328)), (4479379/562949953421312), by norm_num⟩
  | 4 => ⟨((492217384929747/1125899906842624), (823830489630729/2251799813685248)), (17333919/1125899906842624), by norm_num⟩
  | 5 => ⟨((257940460513513/4503599627370496), (720319251768285/2251799813685248)), (111357409/4503599627370496), by norm_num⟩
  | 6 => ⟨((-892133485620301/9007199254740992), (165023088099279/4503599627370496)), (167998379/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-1171447515/33554432)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-19542101/8388608), (-606977659/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((88286621122991/18014398509481984), (875600782480093/9007199254740992)), (69712133/4503599627370496), by norm_num⟩
  | 1 => ⟨((-6538153/536870912), (-32421741/134217728)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((64986799/4294967296), (1289039997/4294967296)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((-26914355/2147483648), (-1067714687/4294967296)), (11/268435456), by norm_num⟩
  | 4 => ⟨((16719915/2147483648), (1326585663/8589934592)), (221/8589934592), by norm_num⟩
  | 5 => ⟨((-66475885/17179869184), (-659288307/8589934592)), (111/8589934592), by norm_num⟩
  | 6 => ⟨((55062123/34359738368), (273044983/8589934592)), (185/34359738368), by norm_num⟩
  | 7 => ⟨((-78185277/137438953472), (-1550837243/137438953472)), (265/137438953472), by norm_num⟩
  | 8 => ⟨((97141557/549755813888), (240855361/68719476736)), (83/137438953472), by norm_num⟩
  | 9 => ⟨((-53641711/1099511627776), (-532002745/549755813888)), (185/1099511627776), by norm_num⟩
  | 10 => ⟨((26658929/2199023255552), (1057581727/4398046511104)), (93/2199023255552), by norm_num⟩
  | 11 => ⟨((-96356291/35184372088832), (-1911266811/35184372088832)), (339/35184372088832), by norm_num⟩
  | 12 => ⟨((79812129/140737488355328), (197888317/17592186044416)), (283/140737488355328), by norm_num⟩
  | 13 => ⟨((-61023289/562949953421312), (-1210422141/562949953421312)), (109/281474976710656), by norm_num⟩
  | 14 => ⟨((86649815/4503599627370496), (214841859/562949953421312)), (39/562949953421312), by norm_num⟩
  | 15 => ⟨((-57417787/18014398509481984), (-1138905523/18014398509481984)), (13/1125899906842624), by norm_num⟩
  | 16 => ⟨((8917365/18014398509481984), (1415036953/144115188075855872)), (261/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (1980522135781/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111148322258443/39614081257132168796771975168), (2342858660613/633825300114114700748351602688)), (92431/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472324189144391/9903520314283042199192993792), (2635179167275/39614081257132168796771975168)), (1625/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889043971354781/2475880078570760549798248448), (1399606148391/1237940039285380274899124224)), (110517/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770710175754161/154742504910672534362390528), (2798463788659/154742504910672534362390528)), (13817/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774551448937299/4835703278458516698824704), (655691188869/2417851639229258349412352)), (103649/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629197212156431/302231454903657293676544), (35845693571/9444732965739290427392)), (90713/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887151284279067/75557863725914323419136), (1863231257393/37778931862957161709568)), (147447/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648529402235643/2361183241434822606848), (698386013299/1180591620717411303424)), (110619/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620787095114905/590295810358705651712), (3839007059801/590295810358705651712)), (38039/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822648152856001/73786976294838206464), (2397793355771/36893488147419103232)), (47569/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821726844414349/9223372036854775808), (2695338245857/4611686018427387904)), (214175/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592975002414943/1152921504606846976), (2692616467841/576460752303423488)), (53579/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193695872573247/144115188075855872), (4705961196799/144115188075855872)), (93843/72057594037927936), by norm_num⟩
  | 4 => ⟨((186288661752325/4503599627370496), (13763129851/70368744177664)), (35231/4503599627370496), by norm_num⟩
  | 3 => ⟨((371899052440691/2251799813685248), (2196763779593/2251799813685248)), (176435/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224621187547267/4503599627370496), (17510209318537/4503599627370496)), (353711/2251799813685248), by norm_num⟩
  | 1 => ⟨((552775929182211/562949953421312), (13053030724309/1125899906842624)), (1065353/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085347723628669/1125899906842624), (12894526094571/562949953421312)), (2147653/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1085347723628669/1125899906842624), (12894526094571/562949953421312)), (8192646035201262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1045665426223081/1125899906842624), (99440772373875/2251799813685248)), (2119493/1125899906842624), by norm_num⟩
  | 2 => ⟨((484476488613925/562949953421312), (11544296366437/140737488355328)), (8248203/2251799813685248), by norm_num⟩
  | 3 => ⟨((1652616785194571/2251799813685248), (158960920291801/1125899906842624)), (15550013/2251799813685248), by norm_num⟩
  | 4 => ⟨((1167984794208887/2251799813685248), (233325789857203/1125899906842624)), (27215477/2251799813685248), by norm_num⟩
  | 5 => ⟨((1018229751762001/4503599627370496), (968188994399069/4503599627370496)), (79025515/4503599627370496), by norm_num⟩
  | 6 => ⟨((88286621122991/18014398509481984), (875600782480093/9007199254740992)), (69712133/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-606977659/16777216)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-40343165/16777216), (-1253058707/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1525206290558245/18014398509481984), (282746253653463/9007199254740992)), (138208587/18014398509481984), by norm_num⟩
  | 1 => ⟨((-932711815/4294967296), (-345816527/4294967296)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((1196179285/4294967296), (443500939/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((-127839137/536870912), (-47398227/536870912)), (99/4294967296), by norm_num⟩
  | 4 => ⟨((1311603649/8589934592), (30393513/536870912)), (65/4294967296), by norm_num⟩
  | 5 => ⟨((-1345678775/17179869184), (-498930059/17179869184)), (17/2147483648), by norm_num⟩
  | 6 => ⟨((1150532637/34359738368), (213288389/17179869184)), (59/17179869184), by norm_num⟩
  | 7 => ⟨((-421579707/34359738368), (-312613667/68719476736)), (11/8589934592), by norm_num⟩
  | 8 => ⟨((1081330599/274877906944), (50114889/34359738368)), (115/274877906944), by norm_num⟩
  | 9 => ⟨((-1232692545/1099511627776), (-114259691/274877906944)), (133/1099511627776), by norm_num⟩
  | 10 => ⟨((1264717581/4398046511104), (234456257/2199023255552)), (139/4398046511104), by norm_num⟩
  | 11 => ⟨((-589806645/8796093022208), (-437358855/17592186044416)), (33/4398046511104), by norm_num⟩
  | 12 => ⟨((504274725/35184372088832), (186967219/35184372088832)), (115/70368744177664), by norm_num⟩
  | 13 => ⟨((-795962543/281474976710656), (-295114737/281474976710656)), (93/281474976710656), by norm_num⟩
  | 14 => ⟨((291657659/562949953421312), (216272673/1125899906842624)), (69/1125899906842624), by norm_num⟩
  | 15 => ⟨((-49872475/562949953421312), (-295855175/9007199254740992)), (3/281474976710656), by norm_num⟩
  | 16 => ⟨((511681491/36028797018963968), (379426771/72057594037927936)), (125/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (462495244771/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444565078139607/158456325028528675187087900672), (547040965325/633825300114114700748351602688)), (46127/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944584994529869/19807040628566084398385987584), (38455807685/2475880078570760549798248448)), (51895/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944454759139431/1237940039285380274899124224), (653588443303/2475880078570760549798248448)), (110281/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770575989526899/154742504910672534362390528), (326704100711/77371252455336267181195264)), (110285/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548977381625177/9671406556917033397649408), (38273671981/604462909807314587353088)), (103397/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258284880721557/604462909807314587353088), (66955006153/75557863725914323419136)), (45239/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943486903178315/37778931862957161709568), (870056449781/75557863725914323419136)), (73517/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296926159691969/4722366482869645213696), (652228702813/4722366482869645213696)), (27571/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810302730576641/295147905179352825856), (896305123031/590295810358705651712)), (151653/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822422237847393/73786976294838206464), (559808967865/36893488147419103232)), (94793/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910737118937899/4611686018427387904), (1258521297183/9223372036854775808)), (213311/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592724327105743/1152921504606846976), (314302881845/288230376151711744)), (213345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74592418712369/9007199254740992), (1098588423283/144115188075855872)), (93357/72057594037927936), by norm_num⟩
  | 4 => ⟨((186248482179505/4503599627370496), (1644943872071/36028797018963968)), (70037/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487201952076071/9007199254740992), (1025523628047/4503599627370496)), (350319/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223855176503799/4503599627370496), (2043368840013/2251799813685248)), (701041/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210010578065679/2251799813685248), (1522964320249/562949953421312)), (526291/1125899906842624), by norm_num⟩
  | 0 => ⟨((2168730394839105/2251799813685248), (12031571637549/2251799813685248)), (1054647/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2168730394839105/2251799813685248), (12031571637549/2251799813685248)), (4023159031394576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2088661140390485/2251799813685248), (1448465520195/140737488355328)), (4085505/2251799813685248), by norm_num⟩
  | 2 => ⟨((968551518536987/1125899906842624), (42992861114425/2251799813685248)), (7663133/2251799813685248), by norm_num⟩
  | 3 => ⟨((1665565370127813/2251799813685248), (36984460754953/1125899906842624)), (3369247/562949953421312), by norm_num⟩
  | 4 => ⟨((614760820209983/1125899906842624), (6838977946877/140737488355328)), (10411087/1125899906842624), by norm_num⟩
  | 5 => ⟨((1332045522511107/4503599627370496), (238988814772943/4503599627370496)), (49524389/4503599627370496), by norm_num⟩
  | 6 => ⟨((1525206290558245/18014398509481984), (282746253653463/9007199254740992)), (138208587/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-1253058707/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-83017565/33554432), (-644631395/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1136930215002361/18014398509481984), (-1005064133397431/18014398509481984)), (167328193/18014398509481984), by norm_num⟩
  | 1 => ⟨((-715356831/4294967296), (632386653/4294967296)), (107/4294967296), by norm_num⟩
  | 2 => ⟨((235983461/1073741824), (-208613079/1073741824)), (143/4294967296), by norm_num⟩
  | 3 => ⟨((-103795647/536870912), (734055833/4294967296)), (1/33554432), by norm_num⟩
  | 4 => ⟨((273922663/2147483648), (-968607713/8589934592)), (171/8589934592), by norm_num⟩
  | 5 => ⟨((-578318089/8589934592), (511242257/8589934592)), (23/2147483648), by norm_num⟩
  | 6 => ⟨((508738197/17179869184), (-899465083/34359738368)), (41/8589934592), by norm_num⟩
  | 7 => ⟨((-767193867/68719476736), (339105703/34359738368)), (63/34359738368), by norm_num⟩
  | 8 => ⟨((1012334299/274877906944), (-894919391/274877906944)), (169/274877906944), by norm_num⟩
  | 9 => ⟨((-296845361/274877906944), (262415953/274877906944)), (101/549755813888), by norm_num⟩
  | 10 => ⟨((156678385/549755813888), (-554024595/2199023255552)), (109/2199023255552), by norm_num⟩
  | 11 => ⟨((-75178771/1099511627776), (531673697/8796093022208)), (107/8796093022208), by norm_num⟩
  | 12 => ⟨((132267391/8796093022208), (-467705789/35184372088832)), (191/70368744177664), by norm_num⟩
  | 13 => ⟨((-859227637/281474976710656), (379785351/140737488355328)), (157/281474976710656), by norm_num⟩
  | 14 => ⟨((20245991/35184372088832), (-572728751/1125899906842624)), (15/140737488355328), by norm_num⟩
  | 15 => ⟨((-56992353/562949953421312), (806114137/9007199254740992)), (171/9007199254740992), by norm_num⟩
  | 16 => ⟨((150406087/9007199254740992), (-531845355/36028797018963968)), (115/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (-942978116077/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444538192021759/158456325028528675187087900672), (-557614899519/316912650057057350374175801344)), (46155/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889048998997613/39614081257132168796771975168), (-1254364772443/39614081257132168796771975168)), (6491/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236097620127743/309485009821345068724781056), (-1332426333863/2475880078570760549798248448)), (27589/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770447426318555/154742504910672534362390528), (-333012059619/38685626227668133590597632)), (110365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193607105914209/1208925819614629174706176), (-1248393644811/9671406556917033397649408)), (103477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157272425864689/75557863725914323419136), (-68246439159/37778931862957161709568)), (11319/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471700599923607/18889465931478580854784), (-886827561085/37778931862957161709568)), (147165/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324199398619527/1180591620717411303424), (-664791717627/2361183241434822606848)), (55195/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620428667469447/590295810358705651712), (-1827108786333/590295810358705651712)), (37953/147573952589676412928), by norm_num⟩
  | 8 => ⟨((113887576320285/4611686018427387904), (-2282284482655/73786976294838206464)), (189805/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113826597528929/576460752303423488), (-641342464059/2305843009213693952)), (213585/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592475608067529/1152921504606846976), (-640655608585/288230376151711744)), (53413/288230376151711744), by norm_num⟩
  | 5 => ⟨((149157627990589/18014398509481984), (-1119603821013/72057594037927936)), (187023/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489661252877621/36028797018963968), (-1676323564135/18014398509481984)), (140343/18014398509481984), by norm_num⟩
  | 3 => ⟨((743396769695379/4503599627370496), (-522505372791/1125899906842624)), (351127/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223037891616877/4503599627370496), (-8327874637089/4503599627370496)), (703063/4503599627370496), by norm_num⟩
  | 1 => ⟨((552195885449769/562949953421312), (-12411585448887/2251799813685248)), (1056627/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083136062027277/1125899906842624), (-6126017368903/562949953421312)), (2121449/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1083136062027277/1125899906842624), (-6126017368903/562949953421312)), (8092685708052825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32558223242683/35184372088832), (-47146715536885/2251799813685248)), (4127917/2251799813685248), by norm_num⟩
  | 2 => ⟨((963605290796815/1125899906842624), (-87255403378161/2251799813685248)), (3906239/1125899906842624), by norm_num⟩
  | 3 => ⟨((823014350090417/1125899906842624), (-74677835778131/1125899906842624)), (873633/140737488355328), by norm_num⟩
  | 4 => ⟨((298328402558499/562949953421312), (-3411767006639/35184372088832)), (22289827/2251799813685248), by norm_num⟩
  | 5 => ⟨((1222417101893749/4503599627370496), (-462854132362011/4503599627370496)), (27947251/2251799813685248), by norm_num⟩
  | 6 => ⟨((1136930215002361/18014398509481984), (-1005064133397431/18014398509481984)), (167328193/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-644631395/16777216)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-85187893/33554432), (-1322967985/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-223264190029351/18014398509481984), (-175601247234019/2251799813685248)), (240470035/18014398509481984), by norm_num⟩
  | 1 => ⟨((288300817/8589934592), (907014833/4294967296)), (313/8589934592), by norm_num⟩
  | 2 => ⟨((-195183271/4294967296), (-614060425/2147483648)), (107/2147483648), by norm_num⟩
  | 3 => ⟨((176188699/4294967296), (1108604305/4294967296)), (195/4294967296), by norm_num⟩
  | 4 => ⟨((-238563921/8589934592), (-1501078055/8589934592)), (133/4294967296), by norm_num⟩
  | 5 => ⟨((129208615/8589934592), (1625997891/17179869184)), (291/17179869184), by norm_num⟩
  | 6 => ⟨((-14579309/2147483648), (-1467761305/34359738368)), (265/34359738368), by norm_num⟩
  | 7 => ⟨((45121715/17179869184), (567824471/34359738368)), (207/68719476736), by norm_num⟩
  | 8 => ⟨((-244383739/274877906944), (-1537697173/274877906944)), (283/274877906944), by norm_num⟩
  | 9 => ⟨((294134859/1099511627776), (462684571/274877906944)), (343/1099511627776), by norm_num⟩
  | 10 => ⟨((-159306393/2199023255552), (-250594609/549755813888)), (47/549755813888), by norm_num⟩
  | 11 => ⟨((78438129/4398046511104), (493543841/4398046511104)), (187/8796093022208), by norm_num⟩
  | 12 => ⟨((-70804797/17592186044416), (-891027665/35184372088832)), (85/17592186044416), by norm_num⟩
  | 13 => ⟨((235991317/281474976710656), (371222715/70368744177664)), (143/140737488355328), by norm_num⟩
  | 14 => ⟨((-91296619/562949953421312), (-1148902569/1125899906842624)), (223/1125899906842624), by norm_num⟩
  | 15 => ⟨((32964777/1125899906842624), (414838111/2251799813685248)), (81/2251799813685248), by norm_num⟩
  | 16 => ⟨((-89270271/18014398509481984), (-561701215/18014398509481984)), (221/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (-562860628705/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778049995373479/633825300114114700748351602688), (-332803001317/79228162514264337593543950336)), (92463/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888933231544531/39614081257132168796771975168), (-748641091795/9903520314283042199192993792)), (104037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472164439696061/618970019642690137449562112), (-3180900378141/2475880078570760549798248448)), (110559/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770324000113821/154742504910672534362390528), (-3179973426735/154742504910672534362390528)), (110581/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548740897482457/9671406556917033397649408), (-93132516425/302231454903657293676544)), (103693/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629038856638443/302231454903657293676544), (-2606726262267/604462909807314587353088)), (22689/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886636702623895/75557863725914323419136), (-4234085579573/75557863725914323419136)), (147521/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296672932863189/4722366482869645213696), (-3173950936307/4722366482869645213696)), (110679/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620256626827503/590295810358705651712), (-2180781229411/295147905179352825856)), (76123/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821985225509997/73786976294838206464), (-1362006372979/18446744073709551616)), (2975/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1820981268827951/9223372036854775808), (-1530908093217/2305843009213693952)), (214329/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796114849769367/576460752303423488), (-6116893165707/1152921504606846976)), (214491/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193044040195629/144115188075855872), (-5344708395725/144115188075855872)), (46965/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489332162822805/36028797018963968), (-1000242191875/4503599627370496)), (141077/18014398509481984), by norm_num⟩
  | 3 => ⟨((743187940426737/4503599627370496), (-4988000344971/4503599627370496)), (176665/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111091901813155/2251799813685248), (-9936463960065/2251799813685248)), (708573/4503599627370496), by norm_num⟩
  | 1 => ⟨((551863972589933/562949953421312), (-29612372817823/2251799813685248)), (533831/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163433177383685/2251799813685248), (-913135113495/35184372088832)), (538655/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2163433177383685/2251799813685248), (-913135113495/35184372088832)), (2054805757762718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2077017581814941/2251799813685248), (-56147280246509/1125899906842624)), (1062993/562949953421312), by norm_num⟩
  | 2 => ⟨((477550439953685/562949953421312), (-103578379866933/1125899906842624)), (1033495/281474976710656), by norm_num⟩
  | 3 => ⟨((1601366523871615/2251799813685248), (-351462154491911/2251799813685248)), (7774331/1125899906842624), by norm_num⟩
  | 4 => ⟨((1083954747177069/2251799813685248), (-62485542141737/281474976710656)), (13484269/1125899906842624), by norm_num⟩
  | 5 => ⟨((821630357897537/4503599627370496), (-962522506632533/4503599627370496)), (18968749/1125899906842624), by norm_num⟩
  | 6 => ⟨((-223264190029351/18014398509481984), (-175601247234019/2251799813685248)), (240470035/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-1322967985/33554432)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile001Terms1
