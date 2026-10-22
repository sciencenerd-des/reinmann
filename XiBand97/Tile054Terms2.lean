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
namespace Reinmann.XiBand97.Tile054Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨54,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15489/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15489/512))
  have he : value ((69/80), (15489/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-320962607/134217728), (-11257676227/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-120396286978415/2251799813685248), (-668874340254083/9007199254740992)), (9352961/4503599627370496), by norm_num⟩
  | 1 => ⟨((10187054061/68719476736), (1768601849/8589934592)), (199/34359738368), by norm_num⟩
  | 2 => ⟨((-14122255601/68719476736), (-19614422163/68719476736)), (277/34359738368), by norm_num⟩
  | 3 => ⟨((6525867769/34359738368), (4531893807/17179869184)), (257/34359738368), by norm_num⟩
  | 4 => ⟨((-4523386845/34359738368), (-3141269415/17179869184)), (179/34359738368), by norm_num⟩
  | 5 => ⟨((5016596541/68719476736), (6967558523/68719476736)), (399/137438953472), by norm_num⟩
  | 6 => ⟨((-9272639329/274877906944), (-12878782789/274877906944)), (371/274877906944), by norm_num⟩
  | 7 => ⟨((3672745033/274877906944), (5101081131/274877906944)), (37/68719476736), by norm_num⟩
  | 8 => ⟨((-5091505729/1099511627776), (-14143200015/2199023255552)), (413/2199023255552), by norm_num⟩
  | 9 => ⟨((6274067273/4398046511104), (2178515381/1099511627776)), (511/8796093022208), by norm_num⟩
  | 10 => ⟨((-13916326531/35184372088832), (-19328406965/35184372088832)), (569/35184372088832), by norm_num⟩
  | 11 => ⟨((7015318181/70368744177664), (9743586031/70368744177664)), (9/2199023255552), by norm_num⟩
  | 12 => ⟨((-12967061381/562949953421312), (-18009971163/562949953421312)), (535/562949953421312), by norm_num⟩
  | 13 => ⟨((5531127407/1125899906842624), (7682191221/1125899906842624)), (459/2251799813685248), by norm_num⟩
  | 14 => ⟨((-4381583277/4503599627370496), (-12171175281/9007199254740992)), (365/9007199254740992), by norm_num⟩
  | 15 => ⟨((6479108469/36028797018963968), (17997687105/72057594037927936)), (271/36028797018963968), by norm_num⟩
  | 16 => ⟨((-561371971/18014398509481984), (-6237523037/144115188075855872)), (189/144115188075855872), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-1429495840527/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778274809658711/633825300114114700748351602688), (-422712419459/79228162514264337593543950336)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944592981174491/19807040628566084398385987584), (-1901805418851/19807040628566084398385987584)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236115755759361/309485009821345068724781056), (-2020174817315/1237940039285380274899124224)), (13833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885296009253929/77371252455336267181195264), (-2019619839133/77371252455336267181195264)), (3459/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774495939594989/4835703278458516698824704), (-3785608181493/9671406556917033397649408)), (12975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629148518460257/302231454903657293676544), (-3311228492393/604462909807314587353088)), (11357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943496284454339/37778931862957161709568), (-5378537045277/75557863725914323419136)), (9231/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324234841291489/1180591620717411303424), (-4031970430525/4722366482869645213696)), (3463/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810311106221431/295147905179352825856), (-5540820663515/590295810358705651712)), (19057/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911220535312375/36893488147419103232), (-6921320254087/73786976294838206464)), (23835/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821492533444349/9223372036854775808), (-7780019087921/9223372036854775808)), (26835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796369507944475/576460752303423488), (-3885971145691/576460752303423488)), (26861/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596743752268643/72057594037927936), (-3395685644581/72057594037927936)), (5883/36028797018963968), by norm_num⟩
  | 4 => ⟨((744996497614079/18014398509481984), (-5084460473247/18014398509481984)), (35355/36028797018963968), by norm_num⟩
  | 3 => ⟨((371798577120997/2251799813685248), (-3169864796861/2251799813685248)), (44295/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223797917308301/4503599627370496), (-3158003278329/562949953421312)), (22223/1125899906842624), by norm_num⟩
  | 1 => ⟨((552455136432015/562949953421312), (-37659452000605/2251799813685248)), (67049/1125899906842624), by norm_num⟩
  | 0 => ⟨((541984613305505/562949953421312), (-37188204785403/1125899906842624)), (67813/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((541984613305505/562949953421312), (-37188204785403/1125899906842624)), (258686067821311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2084743616252123/2251799813685248), (-71606488881111/1125899906842624)), (135055/562949953421312), by norm_num⟩
  | 2 => ⟨((1920972709126037/2251799813685248), (-265176628348351/2251799813685248)), (133625/281474976710656), by norm_num⟩
  | 3 => ⟨((1607521895590137/2251799813685248), (-452435481217641/2251799813685248)), (518917/562949953421312), by norm_num⟩
  | 4 => ⟨((1056678646865569/2251799813685248), (-322986056744065/1125899906842624)), (3797663/2251799813685248), by norm_num⟩
  | 5 => ⟨((621094101782419/4503599627370496), (-1212514424497487/4503599627370496)), (11486091/4503599627370496), by norm_num⟩
  | 6 => ⟨((-120396286978415/2251799813685248), (-668874340254083/9007199254740992)), (9352961/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-11257676227/134217728)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-5751916657/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-988031126860635/18014398509481984), (606475864825911/9007199254740992)), (35667623/18014398509481984), by norm_num⟩
  | 1 => ⟨((10678493397/68719476736), (-13109401803/68719476736)), (387/68719476736), by norm_num⟩
  | 2 => ⟨((-7563612497/34359738368), (18570866061/68719476736)), (551/68719476736), by norm_num⟩
  | 3 => ⟨((14286218571/68719476736), (-274037633/1073741824)), (523/68719476736), by norm_num⟩
  | 4 => ⟨((-10118976273/68719476736), (6211256629/34359738368)), (93/17179869184), by norm_num⟩
  | 5 => ⟨((5733843721/68719476736), (-3519563033/34359738368)), (423/137438953472), by norm_num⟩
  | 6 => ⟨((-10830135029/274877906944), (6647781967/137438953472)), (401/274877906944), by norm_num⟩
  | 7 => ⟨((8766880881/549755813888), (-10762619759/549755813888)), (327/549755813888), by norm_num⟩
  | 8 => ⟨((-12419221949/2199023255552), (15246398959/2199023255552)), (465/2199023255552), by norm_num⟩
  | 9 => ⟨((3909589483/2199023255552), (-2399794499/1099511627776)), (295/4398046511104), by norm_num⟩
  | 10 => ⟨((-8861360875/17592186044416), (2719651919/4398046511104)), (21/1099511627776), by norm_num⟩
  | 11 => ⟨((9129500319/70368744177664), (-5603893897/35184372088832)), (87/17592186044416), by norm_num⟩
  | 12 => ⟨((-4310970355/140737488355328), (10584684645/281474976710656)), (331/281474976710656), by norm_num⟩
  | 13 => ⟨((58720667/8796093022208), (-9227283009/1125899906842624)), (579/2251799813685248), by norm_num⟩
  | 14 => ⟨((-12168643827/9007199254740992), (14938777915/9007199254740992)), (471/9007199254740992), by norm_num⟩
  | 15 => ⟨((9193697085/36028797018963968), (-11286598649/36028797018963968)), (179/18014398509481984), by norm_num⟩
  | 16 => ⟨((-13023852631/288230376151711744), (15988670951/288230376151711744)), (509/288230376151711744), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (2936551720095/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778193911368593/633825300114114700748351602688), (1736569874471/316912650057057350374175801344)), (11569/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944547476511627/19807040628566084398385987584), (3906442190365/39614081257132168796771975168)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472207336946803/618970019642690137449562112), (4149559088695/2475880078570760549798248448)), (6917/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885247659630647/77371252455336267181195264), (4148394185581/154742504910672534362390528)), (6919/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548901222647677/9671406556917033397649408), (3887882172479/9671406556917033397649408)), (12977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629108855735033/302231454903657293676544), (1700329949405/302231454903657293676544)), (11359/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886863663270043/75557863725914323419136), (5523753752115/75557863725914323419136)), (577/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((324210671106549/1180591620717411303424), (4140787348975/4722366482869645213696)), (6927/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810244637030435/295147905179352825856), (5690288652719/590295810358705651712)), (4765/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822274894257655/73786976294838206464), (7107922496873/73786976294838206464)), (745/2305843009213693952), by norm_num⟩
  | 7 => ⟨((113831598789149/576460752303423488), (3994813429715/4611686018427387904)), (26841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592552057947615/1152921504606846976), (7981150779785/1152921504606846976)), (26867/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193323911100063/144115188075855872), (6973980081773/144115188075855872)), (11769/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489747595904749/36028797018963968), (10441938262537/36028797018963968)), (17683/18014398509481984), by norm_num⟩
  | 3 => ⟨((743443773111573/4503599627370496), (6509583098303/4503599627370496)), (44311/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111592182582373/2251799813685248), (6484689725013/1125899906842624)), (88933/4503599627370496), by norm_num⟩
  | 1 => ⟨((138056261823841/140737488355328), (38659891600803/2251799813685248)), (67091/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083048934697891/1125899906842624), (76330914702635/2251799813685248)), (271501/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083048934697891/1125899906842624), (76330914702635/2251799813685248)), (1035694130904387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2081070236697615/2251799813685248), (146851625709851/2251799813685248)), (540743/2251799813685248), by norm_num⟩
  | 2 => ⟨((1913708271892319/2251799813685248), (271434916743577/2251799813685248)), (1070019/2251799813685248), by norm_num⟩
  | 3 => ⟨((796829810108311/1125899906842624), (461361833583661/2251799813685248)), (2076691/2251799813685248), by norm_num⟩
  | 4 => ⟨((516674757116433/1125899906842624), (653036491097387/2251799813685248)), (3790431/2251799813685248), by norm_num⟩
  | 5 => ⟨((569637279444379/4503599627370496), (599356067755803/2251799813685248)), (11354705/4503599627370496), by norm_num⟩
  | 6 => ⟨((-988031126860635/18014398509481984), (606475864825911/9007199254740992)), (35667623/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-5751916657/67108864)), (1/134217728), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-11735916389/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((80529462126169/1125899906842624), (373329244475717/9007199254740992)), (17994733/18014398509481984), by norm_num⟩
  | 1 => ⟨((-14206548035/68719476736), (-8232576787/68719476736)), (25/8589934592), by norm_num⟩
  | 2 => ⟨((20531102609/68719476736), (1487200465/8589934592)), (291/68719476736), by norm_num⟩
  | 3 => ⟨((-19780839713/68719476736), (-11462832593/68719476736)), (141/34359738368), by norm_num⟩
  | 4 => ⟨((7146747557/34359738368), (4141480949/34359738368)), (103/34359738368), by norm_num⟩
  | 5 => ⟨((-1032837865/8589934592), (-9576335657/137438953472)), (15/8589934592), by norm_num⟩
  | 6 => ⟨((15921522109/274877906944), (4613195021/137438953472)), (233/274877906944), by norm_num⟩
  | 7 => ⟨((-13148319385/549755813888), (-7619342059/549755813888)), (97/274877906944), by norm_num⟩
  | 8 => ⟨((19001765507/2199023255552), (11011365551/2199023255552)), (283/2199023255552), by norm_num⟩
  | 9 => ⟨((-3051231465/1099511627776), (-3536326667/2199023255552)), (23/549755813888), by norm_num⟩
  | 10 => ⟨((14110709205/17592186044416), (2044259745/4398046511104)), (107/8796093022208), by norm_num⟩
  | 11 => ⟨((-14830980135/70368744177664), (-8594430011/70368744177664)), (227/70368744177664), by norm_num⟩
  | 12 => ⟨((14289015375/281474976710656), (4140182963/140737488355328)), (221/281474976710656), by norm_num⟩
  | 13 => ⟨((-3176966653/281474976710656), (-7364103329/1125899906842624)), (199/1125899906842624), by norm_num⟩
  | 14 => ⟨((2623604197/1125899906842624), (3040713755/2251799813685248)), (331/9007199254740992), by norm_num⟩
  | 15 => ⟨((-16177475147/36028797018963968), (-9374712705/36028797018963968)), (129/18014398509481984), by norm_num⟩
  | 16 => ⟨((1461216165/18014398509481984), (3387050605/72057594037927936)), (47/36028797018963968), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (342068011419/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778124076516163/633825300114114700748351602688), (202270111313/158456325028528675187087900672)), (721/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472254186362063/9903520314283042199192993792), (56876205793/2475880078570760549798248448)), (6489/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944373361782189/1237940039285380274899124224), (60415608129/154742504910672534362390528)), (13791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442603306189879/38685626227668133590597632), (966373369709/154742504910672534362390528)), (13791/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774412410734753/4835703278458516698824704), (452840755717/4835703278458516698824704)), (6465/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258151422393431/604462909807314587353088), (792177923873/604462909807314587353088)), (11315/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886756996201547/75557863725914323419136), (1286739267305/75557863725914323419136)), (4597/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324190901059555/1180591620717411303424), (482286793583/2361183241434822606848)), (13793/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810191016072977/295147905179352825856), (1325507772847/590295810358705651712)), (18967/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911071539330529/36893488147419103232), (25870534603/1152921504606846976)), (741/2305843009213693952), by norm_num⟩
  | 7 => ⟨((910580179226013/4611686018427387904), (1861070452773/9223372036854775808)), (3335/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796205332955791/576460752303423488), (929531251875/576460752303423488)), (26687/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193204491228627/144115188075855872), (406105907835/36028797018963968)), (11679/72057594037927936), by norm_num⟩
  | 4 => ⟨((744788517800705/18014398509481984), (1216065263133/18014398509481984)), (17525/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486689282269111/9007199254740992), (3032295715197/9007199254740992)), (43837/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111416203178233/2251799813685248), (6041053641639/4503599627370496)), (21937/1125899906842624), by norm_num⟩
  | 1 => ⟨((2208482836025683/2251799813685248), (4501480634529/1125899906842624)), (4119/70368744177664), by norm_num⟩
  | 0 => ⟨((1082850250237403/1125899906842624), (17772792579663/2251799813685248)), (132183/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082850250237403/1125899906842624), (17772792579663/2251799813685248)), (504238132957076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082752985899437/2251799813685248), (34186472128371/2251799813685248)), (256345/1125899906842624), by norm_num⟩
  | 2 => ⟨((481469451573839/562949953421312), (31620029662497/1125899906842624)), (963971/2251799813685248), by norm_num⟩
  | 3 => ⟨((205669149471043/281474976710656), (108173582733791/2251799813685248)), (1703041/2251799813685248), by norm_num⟩
  | 4 => ⟨((149629509606155/281474976710656), (158081325850605/2251799813685248)), (2652393/2251799813685248), by norm_num⟩
  | 5 => ⟨((1250471427468311/4503599627370496), (336138317392693/4503599627370496)), (6384767/4503599627370496), by norm_num⟩
  | 6 => ⟨((80529462126169/1125899906842624), (373329244475717/9007199254740992)), (17994733/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-11735916389/134217728)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-681712945/268435456), (-11955448145/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((315727920371933/9007199254740992), (-159169779897001/2251799813685248)), (12084871/9007199254740992), by norm_num⟩
  | 1 => ⟨((-7092602505/68719476736), (14302542243/68719476736)), (273/68719476736), by norm_num⟩
  | 2 => ⟨((1305233455/8589934592), (-21056481441/68719476736)), (101/17179869184), by norm_num⟩
  | 3 => ⟨((-5124240349/34359738368), (1291656765/4294967296)), (399/68719476736), by norm_num⟩
  | 4 => ⟨((7544006511/68719476736), (-7606409053/34359738368)), (295/68719476736), by norm_num⟩
  | 5 => ⟨((-2221286683/34359738368), (8958642923/68719476736)), (349/137438953472), by norm_num⟩
  | 6 => ⟨((8720590791/274877906944), (-17585451615/274877906944)), (43/34359738368), by norm_num⟩
  | 7 => ⟨((-7336356413/549755813888), (14794082629/549755813888)), (291/549755813888), by norm_num⟩
  | 8 => ⟨((5400363447/1099511627776), (-21780136777/2199023255552)), (431/2199023255552), by norm_num⟩
  | 9 => ⟨((-7067129171/4398046511104), (14251174155/4398046511104)), (283/4398046511104), by norm_num⟩
  | 10 => ⟨((8323492241/17592186044416), (-1049042817/1099511627776)), (335/17592186044416), by norm_num⟩
  | 11 => ⟨((-8912005453/70368744177664), (17971447629/70368744177664)), (361/70368744177664), by norm_num⟩
  | 12 => ⟨((8746952079/281474976710656), (-137801643/2199023255552)), (357/281474976710656), by norm_num⟩
  | 13 => ⟨((-3962287177/562949953421312), (15980249759/1125899906842624)), (325/1125899906842624), by norm_num⟩
  | 14 => ⟨((6666693035/4503599627370496), (-13443677225/4503599627370496)), (275/4503599627370496), by norm_num⟩
  | 15 => ⟨((-5234578889/18014398509481984), (21111513197/36028797018963968)), (217/18014398509481984), by norm_num⟩
  | 16 => ⟨((1926612265/36028797018963968), (-242818603/2251799813685248)), (321/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (-1446466448975/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778051023091153/633825300114114700748351602688), (-1710504268961/633825300114114700748351602688)), (11547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236116813863269/4951760157141521099596496896), (-1923893876941/39614081257132168796771975168)), (203/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((118041205131681/154742504910672534362390528), (-15965685967/19342813113834066795298816)), (13805/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770325707738729/154742504910672534362390528), (-1021506222783/77371252455336267181195264)), (13807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24199104594527/151115727451828646838272), (-957345914821/4835703278458516698824704)), (6473/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78629967548175/37778931862957161709568), (-104670204481/37778931862957161709568)), (5665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886639940995509/75557863725914323419136), (-680060179427/18889465931478580854784)), (9207/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296675681698031/4722366482869645213696), (-2039144563833/4722366482869645213696)), (6907/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620260925885439/590295810358705651712), (-2802141346519/590295810358705651712)), (9499/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821991377256585/73786976294838206464), (-3500154840865/73786976294838206464)), (23755/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455247314313921/2305843009213693952), (-1967104793501/4611686018427387904)), (26735/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398059754928019/288230376151711744), (-3929883208185/1152921504606846976)), (6687/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193053689586319/144115188075855872), (-1716893325267/72057594037927936)), (23419/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489349615469081/36028797018963968), (-5140972692643/36028797018963968)), (35157/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486402886879417/9007199254740992), (-6409261886491/9007199254740992)), (21999/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222253297546235/4503599627370496), (-12767796642709/4503599627370496)), (88149/4503599627370496), by norm_num⟩
  | 1 => ⟨((275949815792359/281474976710656), (-2378168476229/281474976710656)), (66305/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163870181735979/2251799813685248), (-586689403253/35184372088832)), (266777/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163870181735979/2251799813685248), (-586689403253/35184372088832)), (1017673501021575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519686993655763/562949953421312), (-18040960094931/562949953421312)), (521617/2251799813685248), by norm_num⟩
  | 2 => ⟨((1916682600251947/2251799813685248), (-133236032900161/2251799813685248)), (996495/2251799813685248), by norm_num⟩
  | 3 => ⟨((405888694837219/562949953421312), (-226815176406289/2251799813685248)), (1814313/2251799813685248), by norm_num⟩
  | 4 => ⟨((1147741900319571/2251799813685248), (-327068917445751/2251799813685248)), (2981749/2251799813685248), by norm_num⟩
  | 5 => ⟨((1074995553009867/4503599627370496), (-666827838892649/4503599627370496)), (3905779/2251799813685248), by norm_num⟩
  | 6 => ⟨((315727920371933/9007199254740992), (-159169779897001/2251799813685248)), (12084871/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-11955448145/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-693588655/268435456), (-24327433583/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-603254083968997/9007199254740992), (-627254504213231/18014398509481984)), (3839071/2251799813685248), by norm_num⟩
  | 1 => ⟨((13787748173/68719476736), (3584073185/34359738368)), (353/68719476736), by norm_num⟩
  | 2 => ⟨((-20652201091/68719476736), (-10736923711/68719476736)), (531/68719476736), by norm_num⟩
  | 3 => ⟨((1288926361/4294967296), (10721649627/68719476736)), (133/17179869184), by norm_num⟩
  | 4 => ⟨((-1930639149/8589934592), (-8029797953/68719476736)), (401/68719476736), by norm_num⟩
  | 5 => ⟨((18507769623/137438953472), (9622049951/137438953472)), (241/68719476736), by norm_num⟩
  | 6 => ⟨((-4620360231/68719476736), (-9608361859/274877906944)), (121/68719476736), by norm_num⟩
  | 7 => ⟨((15818699725/549755813888), (1028002847/68719476736)), (13/17179869184), by norm_num⟩
  | 8 => ⟨((-11847147323/1099511627776), (-1539810653/274877906944)), (313/1099511627776), by norm_num⟩
  | 9 => ⟨((15773725149/4398046511104), (8200640833/4398046511104)), (419/4398046511104), by norm_num⟩
  | 10 => ⟨((-18901543001/17592186044416), (-9826769763/17592186044416)), (63/2199023255552), by norm_num⟩
  | 11 => ⟨((10295265889/35184372088832), (2676215575/17592186044416)), (69/8796093022208), by norm_num⟩
  | 12 => ⟨((-160634689/2199023255552), (-10689633825/281474976710656)), (277/140737488355328), by norm_num⟩
  | 13 => ⟨((2369075801/140737488355328), (2463329311/281474976710656)), (513/1125899906842624), by norm_num⟩
  | 14 => ⟨((-8110990669/2251799813685248), (-1054210731/562949953421312)), (441/4503599627370496), by norm_num⟩
  | 15 => ⟨((3239780869/4503599627370496), (6737350635/18014398509481984)), (177/9007199254740992), by norm_num⟩
  | 16 => ⟨((-19411032217/144115188075855872), (-1261456171/18014398509481984)), (133/36028797018963968), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (-866939510761/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888987715604151/316912650057057350374175801344), (-4100462560055/633825300114114700748351602688)), (1447/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944424539063133/19807040628566084398385987584), (-4611969421061/39614081257132168796771975168)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888567985199209/2475880078570760549798248448), (-4898924036637/2475880078570760549798248448)), (3461/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110639613832713/9671406556917033397649408), (-4897469200113/154742504910672534362390528)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387163981173177/2417851639229258349412352), (-2294916004595/4835703278458516698824704)), (3247/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78625183269607/37778931862957161709568), (-4014558089161/604462909807314587353088)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58953574330901/2361183241434822606848), (-6520761121983/75557863725914323419136)), (9241/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296580486340503/4722366482869645213696), (-4888037990239/4722366482869645213696)), (13869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810064185636979/295147905179352825856), (-3358469067361/295147905179352825856)), (9541/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821823196482661/73786976294838206464), (-4195002316647/36893488147419103232)), (11935/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820796640024403/9223372036854775808), (-294696225961/288230376151711744)), (26879/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592042144840487/1152921504606846976), (-2354922963517/288230376151711744)), (13455/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192876647526193/144115188075855872), (-8230330025099/144115188075855872)), (23581/144115188075855872), by norm_num⟩
  | 4 => ⟨((744537266234833/18014398509481984), (-12321720474895/36028797018963968)), (35441/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486042447795091/9007199254740992), (-15360603912441/9007199254740992)), (5553/1125899906842624), by norm_num⟩
  | 2 => ⟨((555370740147143/1125899906842624), (-7649200757895/1125899906842624)), (697/35184372088832), by norm_num⟩
  | 1 => ⟨((137895025659679/140737488355328), (-22792508046649/1125899906842624)), (67373/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160829699529093/2251799813685248), (-89934220701235/2251799813685248)), (136601/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2160829699529093/2251799813685248), (-89934220701235/2251799813685248)), (521091465476607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2069942806632353/2251799813685248), (-172601963917203/2251799813685248)), (546153/2251799813685248), by norm_num⟩
  | 2 => ⟨((1889542648916697/2251799813685248), (-79331251261701/562949953421312)), (543909/1125899906842624), by norm_num⟩
  | 3 => ⟨((1540845790180955/2251799813685248), (-66568876034139/281474976710656)), (8329/8796093022208), by norm_num⟩
  | 4 => ⟨((928410758363213/2251799813685248), (-364410270472181/1125899906842624)), (1963295/1125899906842624), by norm_num⟩
  | 5 => ⟨((293780249320473/4503599627370496), (-600981336810273/2251799813685248)), (11559231/4503599627370496), by norm_num⟩
  | 6 => ⟨((-603254083968997/9007199254740992), (-627254504213231/18014398509481984)), (3839071/2251799813685248), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-24327433583/268435456)), (1/134217728), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-352442413/134217728), (-24723643715/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-708203884032397/18014398509481984), (1094668805309083/18014398509481984)), (29578101/18014398509481984), by norm_num⟩
  | 1 => ⟨((8225031339/68719476736), (-12713408431/68719476736)), (173/34359738368), by norm_num⟩
  | 2 => ⟨((-12520646231/68719476736), (9676564307/34359738368)), (529/68719476736), by norm_num⟩
  | 3 => ⟨((12706462795/68719476736), (-19640344769/68719476736)), (539/68719476736), by norm_num⟩
  | 4 => ⟨((-9671277771/68719476736), (29197007/134217728)), (103/17179869184), by norm_num⟩
  | 5 => ⟨((5888884435/68719476736), (-18204865111/137438953472)), (63/17179869184), by norm_num⟩
  | 6 => ⟨((-5976280265/137438953472), (9237520051/137438953472)), (257/137438953472), by norm_num⟩
  | 7 => ⟨((5198548389/274877906944), (-16070764037/549755813888)), (449/549755813888), by norm_num⟩
  | 8 => ⟨((-7913548607/1099511627776), (6115975213/549755813888)), (43/137438953472), by norm_num⟩
  | 9 => ⟨((10707989465/4398046511104), (-16551310013/4398046511104)), (467/4398046511104), by norm_num⟩
  | 10 => ⟨((-3260071419/4398046511104), (20156333883/17592186044416)), (571/17592186044416), by norm_num⟩
  | 11 => ⟨((7218444061/35184372088832), (-11157529231/35184372088832)), (159/17592186044416), by norm_num⟩
  | 12 => ⟨((-1831392909/35184372088832), (11323116031/140737488355328)), (81/35184372088832), by norm_num⟩
  | 13 => ⟨((3431210341/281474976710656), (-2651806217/140737488355328)), (305/562949953421312), by norm_num⟩
  | 14 => ⟨((-5969369641/2251799813685248), (4613419159/1125899906842624)), (133/1125899906842624), by norm_num⟩
  | 15 => ⟨((9692735899/18014398509481984), (-7491017677/9007199254740992)), (217/9007199254740992), by norm_num⟩
  | 16 => ⟨((-3688718991/36028797018963968), (2850821425/18014398509481984)), (83/18014398509481984), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (1397070230637/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777913778551489/633825300114114700748351602688), (3303711455723/633825300114114700748351602688)), (11567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888779909681335/39614081257132168796771975168), (3715822602771/39614081257132168796771975168)), (13015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888494746174245/2475880078570760549798248448), (1973501615173/1237940039285380274899124224)), (13831/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770160866035759/154742504910672534362390528), (3945813053105/154742504910672534362390528)), (13835/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548587830358119/9671406556917033397649408), (3697935570261/9671406556917033397649408)), (6487/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257943650767387/604462909807314587353088), (1617214951273/302231454903657293676544)), (2839/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886418609910993/75557863725914323419136), (656697507577/9444732965739290427392)), (18459/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40515911020457/147573952589676412928), (1969056763619/2361183241434822606848)), (13851/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202503885911701/73786976294838206464), (5411541656847/590295810358705651712)), (9527/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821702789517237/73786976294838206464), (6759383509865/73786976294838206464)), (2979/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820662826616405/9223372036854775808), (1899344148277/2305843009213693952)), (26831/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591910382718583/1152921504606846976), (7588721832015/1152921504606846976)), (3357/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192763657531201/144115188075855872), (6630405383781/144115188075855872)), (23527/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488909636634281/36028797018963968), (310193174619/1125899906842624)), (17673/18014398509481984), by norm_num⟩
  | 3 => ⟨((742922163155729/4503599627370496), (12373788973361/9007199254740992)), (22141/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221110581994233/4503599627370496), (24645997049193/4503599627370496)), (88859/4503599627370496), by norm_num⟩
  | 1 => ⟨((551455261995553/562949953421312), (36715858259227/2251799813685248)), (134033/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160065072714063/2251799813685248), (9053006053381/281474976710656)), (135529/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160065072714063/2251799813685248), (9053006053381/281474976710656)), (517002110007857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2069738103380135/2251799813685248), (138947215894641/2251799813685248)), (134367/562949953421312), by norm_num⟩
  | 2 => ⟨((946911324412875/1125899906842624), (255426210933973/2251799813685248)), (1054355/2251799813685248), by norm_num⟩
  | 3 => ⟨((781890480355439/1125899906842624), (214820136510641/1125899906842624)), (2012677/2251799813685248), by norm_num⟩
  | 4 => ⟨((1004005824647451/2251799813685248), (298367232656329/1125899906842624)), (3563473/2251799813685248), by norm_num⟩
  | 5 => ⟨((72379399566505/562949953421312), (1064259576363097/4503599627370496)), (5066343/2251799813685248), by norm_num⟩
  | 6 => ⟨((-708203884032397/18014398509481984), (1094668805309083/18014398509481984)), (29578101/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-24723643715/268435456)), (1/134217728), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨54,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile054Terms2
