/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile039Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (34337/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (34337/1280))
  have he : value ((69/80), (34337/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-20060163/8388608), (-2495673243/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((107600679474283/2251799813685248), (351450788889963/4503599627370496)), (53581845/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2276095813/17179869184), (-3717149711/17179869184)), (285/17179869184), by norm_num⟩
  | 2 => ⟨((3155338791/17179869184), (1288265921/4294967296)), (397/17179869184), by norm_num⟩
  | 3 => ⟨((-2916152249/17179869184), (-4762442085/17179869184)), (369/17179869184), by norm_num⟩
  | 4 => ⟨((1010661355/8589934592), (412634163/2147483648)), (129/8589934592), by norm_num⟩
  | 5 => ⟨((-560429655/8589934592), (-1830503723/17179869184)), (9/1073741824), by norm_num⟩
  | 6 => ⟨((1035893961/34359738368), (3383489319/68719476736)), (67/17179869184), by norm_num⟩
  | 7 => ⟨((-820602261/68719476736), (-2680292665/137438953472)), (107/68719476736), by norm_num⟩
  | 8 => ⟨((1137596287/274877906944), (232229663/34359738368)), (299/549755813888), by norm_num⟩
  | 9 => ⟨((-2803632565/2199023255552), (-1144670835/549755813888)), (371/2199023255552), by norm_num⟩
  | 10 => ⟨((3109328013/8796093022208), (5077922317/8796093022208)), (207/4398046511104), by norm_num⟩
  | 11 => ⟨((-3134868285/35184372088832), (-2559816391/17592186044416)), (105/8796093022208), by norm_num⟩
  | 12 => ⟨((724308371/35184372088832), (4731545371/140737488355328)), (391/140737488355328), by norm_num⟩
  | 13 => ⟨((-1235821059/281474976710656), (-2018250667/281474976710656)), (335/562949953421312), by norm_num⟩
  | 14 => ⟨((1957956303/2251799813685248), (1598794011/1125899906842624)), (267/2251799813685248), by norm_num⟩
  | 15 => ⟨((-361907171/2251799813685248), (-4728318127/18014398509481984)), (397/18014398509481984), by norm_num⟩
  | 16 => ⟨((1003419741/36028797018963968), (3277420379/72057594037927936)), (277/72057594037927936), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (41576315935/316912650057057350374175801344)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222284951314651/79228162514264337593543950336), (98355375945/39614081257132168796771975168)), (23089/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889191629734603/39614081257132168796771975168), (1770028836399/39614081257132168796771975168)), (51955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888932419912625/2475880078570760549798248448), (1880196944133/2475880078570760549798248448)), (6901/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((221324848528873/19342813113834066795298816), (1879681124569/154742504910672534362390528)), (27607/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548998646124891/9671406556917033397649408), (1761653184259/9671406556917033397649408)), (51771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258303377960611/604462909807314587353088), (770449439019/302231454903657293676544)), (45307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887003659808583/75557863725914323419136), (2502934267667/75557863725914323419136)), (18409/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296948370974573/4722366482869645213696), (1876303042493/4722366482869645213696)), (27619/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620635711453017/590295810358705651712), (1289229415787/295147905179352825856)), (75971/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822459616007037/73786976294838206464), (3220888235699/73786976294838206464)), (94991/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910757845777705/4611686018427387904), (3620496866035/9223372036854775808)), (106903/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49773907385019/36028797018963968), (1808373727235/576460752303423488)), (53475/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193513484459793/144115188075855872), (1580220431193/72057594037927936)), (93635/144115188075855872), by norm_num⟩
  | 4 => ⟨((186254796133889/4503599627370496), (2366123638901/18014398509481984)), (8785/2251799813685248), by norm_num⟩
  | 3 => ⟨((1487262187516871/9007199254740992), (5900612215373/9007199254740992)), (175889/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111983490116821/2251799813685248), (5878622084123/2251799813685248)), (352345/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210156773226763/2251799813685248), (8763150519773/1125899906842624)), (132485/562949953421312), by norm_num⟩
  | 0 => ⟨((2168937683275717/2251799813685248), (34616646722521/2251799813685248)), (1065605/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168937683275717/2251799813685248), (34616646722521/2251799813685248)), (4064960488326262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088592570760605/2251799813685248), (2083926074623/70368744177664)), (2085549/2251799813685248), by norm_num⟩
  | 2 => ⟨((1935239503226903/2251799813685248), (61852354597703/1125899906842624)), (998077/562949953421312), by norm_num⟩
  | 3 => ⟨((828192865348141/1125899906842624), (53157087613919/562949953421312)), (3650387/1125899906842624), by norm_num⟩
  | 4 => ⟨((1198331599921667/2251799813685248), (156405806366897/1125899906842624)), (12119417/2251799813685248), by norm_num⟩
  | 5 => ⟨((594256874068979/2251799813685248), (83233873207381/562949953421312)), (32532511/4503599627370496), by norm_num⟩
  | 6 => ⟨((107600679474283/2251799813685248), (351450788889963/4503599627370496)), (53581845/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-2495673243/33554432)), (1/33554432), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-163990341/67108864), (-2550242911/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1286806633730829/18014398509481984), (-889711251885811/18014398509481984)), (79834023/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1738451827/8589934592), (2403966705/17179869184)), (109/8589934592), by norm_num⟩
  | 2 => ⟨((4925404915/17179869184), (-1702737637/8589934592)), (311/17179869184), by norm_num⟩
  | 3 => ⟨((-2325787155/8589934592), (3216145997/17179869184)), (37/2147483648), by norm_num⟩
  | 4 => ⟨((1647362801/8589934592), (-2278006939/17179869184)), (211/17179869184), by norm_num⟩
  | 5 => ⟨((-466733027/4294967296), (2581631863/34359738368)), (241/34359738368), by norm_num⟩
  | 6 => ⟨((1763138987/34359738368), (-2438104615/68719476736)), (229/68719476736), by norm_num⟩
  | 7 => ⟨((-2854485089/137438953472), (1973620151/137438953472)), (187/137438953472), by norm_num⟩
  | 8 => ⟨((4043682623/549755813888), (-1397921737/274877906944)), (267/549755813888), by norm_num⟩
  | 9 => ⟨((-2545914571/1099511627776), (880135671/549755813888)), (85/549755813888), by norm_num⟩
  | 10 => ⟨((1442623827/2199023255552), (-997444851/2199023255552)), (195/4398046511104), by norm_num⟩
  | 11 => ⟨((-2972553511/17592186044416), (2055253863/17592186044416)), (203/17592186044416), by norm_num⟩
  | 12 => ⟨((1403646379/35184372088832), (-970495445/35184372088832)), (193/70368744177664), by norm_num⟩
  | 13 => ⟨((-4894559571/562949953421312), (1692074243/281474976710656)), (339/562949953421312), by norm_num⟩
  | 14 => ⟨((495261839/281474976710656), (-2739432757/2251799813685248)), (69/562949953421312), by norm_num⟩
  | 15 => ⟨((-374181987/1125899906842624), (2069705985/9007199254740992)), (105/4503599627370496), by norm_num⟩
  | 16 => ⟨((4240549595/72057594037927936), (-732989827/18014398509481984)), (75/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644697451/10141204801825835211973625643008), (-787998914655/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778199910735393/633825300114114700748351602688), (-931987791633/633825300114114700748351602688)), (46147/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889102034320819/39614081257132168796771975168), (-524132197773/19807040628566084398385987584)), (25959/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944418655868001/1237940039285380274899124224), (-1113503397741/2475880078570760549798248448)), (27583/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885251888895015/77371252455336267181195264), (-556595662867/77371252455336267181195264)), (27585/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548909677615531/9671406556917033397649408), (-521642706339/4835703278458516698824704)), (25863/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157278204277581/75557863725914323419136), (-228135854355/151115727451828646838272)), (45265/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943438760261853/37778931862957161709568), (-1482262120769/75557863725914323419136)), (36781/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648426968180673/2361183241434822606848), (-1111153564423/4722366482869645213696)), (55179/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810253069787675/295147905179352825856), (-1526954276661/590295810358705651712)), (75881/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822298064223723/73786976294838206464), (-953685491959/36893488147419103232)), (23717/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821334512934829/9223372036854775808), (-66999260589/288230376151711744)), (26687/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796292282690321/576460752303423488), (-2141708627201/1152921504606846976)), (106777/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596678183413539/72057594037927936), (-1871447047207/144115188075855872)), (46731/72057594037927936), by norm_num⟩
  | 4 => ⟨((744902138628515/18014398509481984), (-2802082492101/36028797018963968)), (140257/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486972336331809/9007199254740992), (-1746858389257/4503599627370496)), (175433/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223395530603545/4503599627370496), (-6960845607203/4503599627370496)), (175603/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209320098086185/2251799813685248), (-10375046597271/2251799813685248)), (527661/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167345538776819/2251799813685248), (-10243344563719/1125899906842624)), (529381/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167345538776819/2251799813685248), (-10243344563719/1125899906842624)), (2019428257468795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521468088712715/562949953421312), (-19718331094447/1125899906842624)), (514343/562949953421312), by norm_num⟩
  | 2 => ⟨((30179388366181/35184372088832), (-73061417740133/2251799813685248)), (3883607/2251799813685248), by norm_num⟩
  | 3 => ⟨((1654356795622637/2251799813685248), (-31334208480349/562949953421312)), (6914341/2251799813685248), by norm_num⟩
  | 4 => ⟨((604224911279285/1125899906842624), (-11510339511505/140737488355328)), (10929399/2251799813685248), by norm_num⟩
  | 5 => ⟨((1266927955639021/4503599627370496), (-49417066848417/562949953421312)), (6759237/1125899906842624), by norm_num⟩
  | 6 => ⟨((1286806633730829/18014398509481984), (-889711251885811/18014398509481984)), (79834023/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-163990341/67108864), (-2550242911/33554432)), (1/33554432), by norm_num⟩, -12, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-2601692563/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-800422857476873/18014398509481984), (-627889457141205/9007199254740992)), (134766383/18014398509481984), by norm_num⟩
  | 1 => ⟨((551586061/4294967296), (3461521061/17179869184)), (373/17179869184), by norm_num⟩
  | 2 => ⟨((-1594288773/8589934592), (-5002541357/17179869184)), (541/17179869184), by norm_num⟩
  | 3 => ⟨((1536029081/8589934592), (150616711/536870912)), (131/4294967296), by norm_num⟩
  | 4 => ⟨((-1109923769/8589934592), (-1741353151/8589934592)), (381/17179869184), by norm_num⟩
  | 5 => ⟨((641618463/8589934592), (4026526375/34359738368)), (443/34359738368), by norm_num⟩
  | 6 => ⟨((-2472687847/68719476736), (-3879386039/68719476736)), (429/68719476736), by norm_num⟩
  | 7 => ⟨((63812385/4294967296), (3203676527/137438953472)), (89/34359738368), by norm_num⟩
  | 8 => ⟨((-2951064247/549755813888), (-2314954039/274877906944)), (517/549755813888), by norm_num⟩
  | 9 => ⟨((1895482835/1099511627776), (2973812345/1099511627776)), (167/549755813888), by norm_num⟩
  | 10 => ⟨((-1095730011/2199023255552), (-1719084643/2199023255552)), (97/1099511627776), by norm_num⟩
  | 11 => ⟨((2303321511/17592186044416), (3613668147/17592186044416)), (205/8796093022208), by norm_num⟩
  | 12 => ⟨((-2219151815/70368744177664), (-3481614785/70368744177664)), (99/17592186044416), by norm_num⟩
  | 13 => ⟨((986795959/140737488355328), (3096357245/281474976710656)), (177/140737488355328), by norm_num⟩
  | 14 => ⟨((-1629832669/1125899906842624), (-5114070591/2251799813685248)), (587/2251799813685248), by norm_num⟩
  | 15 => ⟨((2512438569/9007199254740992), (3941750721/9007199254740992)), (227/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1815470371/36028797018963968), (-356035155/4503599627370496)), (165/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-2785318258743/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778118611266897/633825300114114700748351602688), (-3294003621685/633825300114114700748351602688)), (46263/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944505147690239/19807040628566084398385987584), (-231558990063/2475880078570760549798248448)), (6507/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888739469563783/2475880078570760549798248448), (-491937615053/309485009821345068724781056)), (27661/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770405520325725/154742504910672534362390528), (-491796762829/19342813113834066795298816)), (6917/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774408560171757/4835703278458516698824704), (-3687278823249/9671406556917033397649408)), (51891/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157268025762599/75557863725914323419136), (-806293115329/151115727451828646838272)), (11355/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943372187355943/37778931862957161709568), (-1309665655391/18889465931478580854784)), (73833/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296753355857703/4722366482869645213696), (-490879436599/590295810358705651712)), (55399/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620366671082449/590295810358705651712), (-5396487957081/590295810358705651712)), (19053/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911060987942059/36893488147419103232), (-3370416943829/36893488147419103232)), (47661/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227641750998069/1152921504606846976), (-7576875444613/9223372036854775808)), (107317/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592381060101189/1152921504606846976), (-3784339348025/576460752303423488)), (107417/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596587466720411/72057594037927936), (-6613381588325/144115188075855872)), (47051/72057594037927936), by norm_num⟩
  | 4 => ⟨((744762708680325/18014398509481984), (-9901670508039/36028797018963968)), (141377/36028797018963968), by norm_num⟩
  | 3 => ⟨((92913254392311/562949953421312), (-12344935823655/9007199254740992)), (177115/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111320064169923/2251799813685248), (-3074202303649/562949953421312)), (88853/1125899906842624), by norm_num⟩
  | 1 => ⟨((138006283036647/140737488355328), (-4581313360623/281474976710656)), (536085/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164564770170921/2251799813685248), (-36172799338091/1125899906842624)), (1084087/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164564770170921/2251799813685248), (-36172799338091/1125899906842624)), (4135463723189543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519596228112071/562949953421312), (-8692864992909/140737488355328)), (2153839/2251799813685248), by norm_num⟩
  | 2 => ⟨((119358383550031/140737488355328), (-256749209586529/2251799813685248)), (530251/281474976710656), by norm_num⟩
  | 3 => ⟨((1590356431718933/2251799813685248), (-435494067602295/2251799813685248)), (4081287/1125899906842624), by norm_num⟩
  | 4 => ⟨((259745391527953/562949953421312), (-307572097296371/1125899906842624)), (14687057/2251799813685248), by norm_num⟩
  | 5 => ⟨((622684405885643/4503599627370496), (-1135311362579039/4503599627370496)), (43155239/4503599627370496), by norm_num⟩
  | 6 => ⟨((-800422857476873/18014398509481984), (-627889457141205/9007199254740992)), (134766383/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-2601692563/33554432)), (1/33554432), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-42607059/16777216), (-1325179879/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-640822188507959/9007199254740992), (307231748848473/9007199254740992)), (127822679/18014398509481984), by norm_num⟩
  | 1 => ⟨((3598903333/17179869184), (-862717759/8589934592)), (361/17179869184), by norm_num⟩
  | 2 => ⟨((-1324593907/4294967296), (1270109899/8589934592)), (267/8589934592), by norm_num⟩
  | 3 => ⟨((1300061977/4294967296), (-2493174063/17179869184)), (263/8589934592), by norm_num⟩
  | 4 => ⟨((-478494145/2147483648), (1835249723/17179869184)), (389/17179869184), by norm_num⟩
  | 5 => ⟨((2254234899/17179869184), (-270189041/4294967296)), (115/8589934592), by norm_num⟩
  | 6 => ⟨((-4424971403/68719476736), (33148131/1073741824)), (453/68719476736), by norm_num⟩
  | 7 => ⟨((232661755/8589934592), (-1784734153/137438953472)), (383/137438953472), by norm_num⟩
  | 8 => ⟨((-5480466723/549755813888), (656880101/137438953472)), (283/274877906944), by norm_num⟩
  | 9 => ⟨((3585977743/1099511627776), (-1719238555/1099511627776)), (93/274877906944), by norm_num⟩
  | 10 => ⟨((-2111738529/2199023255552), (1012438603/2199023255552)), (55/549755813888), by norm_num⟩
  | 11 => ⟨((4522098355/17592186044416), (-2168046317/17592186044416)), (473/17592186044416), by norm_num⟩
  | 12 => ⟨((-2219173777/35184372088832), (2127893361/70368744177664)), (467/70368744177664), by norm_num⟩
  | 13 => ⟨((4021059551/281474976710656), (-240978929/35184372088832)), (425/281474976710656), by norm_num⟩
  | 14 => ⟨((-3382789851/1125899906842624), (202727929/140737488355328)), (359/1125899906842624), by norm_num⟩
  | 15 => ⟨((5312223091/9007199254740992), (-159178671/562949953421312)), (283/4503599627370496), by norm_num⟩
  | 16 => ⟨((-244398699/2251799813685248), (937383767/18014398509481984)), (419/36028797018963968), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (54842658335/158456325028528675187087900672)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889021677849827/316912650057057350374175801344), (2075316189081/316912650057057350374175801344)), (46305/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888925462925139/39614081257132168796771975168), (2334206892035/19807040628566084398385987584)), (26053/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944324553236211/1237940039285380274899124224), (4958902607413/2475880078570760549798248448)), (27689/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885157450166701/77371252455336267181195264), (2478727489841/77371252455336267181195264)), (55395/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548731891374445/9671406556917033397649408), (1161519078885/2417851639229258349412352)), (51951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629034679143203/302231454903657293676544), (4063779471205/604462909807314587353088)), (11369/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117913889793169/4722366482869645213696), (1650190023261/18889465931478580854784)), (18483/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296661306360795/4722366482869645213696), (4948049614681/4722366482869645213696)), (55479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620239379338215/590295810358705651712), (6799474166669/590295810358705651712)), (19083/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821961777481383/73786976294838206464), (8493204579005/73786976294838206464)), (95487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820952297595879/9223372036854775808), (4773210009795/4611686018427387904)), (26881/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796098747562339/576460752303423488), (9535883300219/1152921504606846976)), (107649/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298253058427227/36028797018963968), (8332053974129/144115188075855872)), (94335/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489277222068159/36028797018963968), (3118604469909/9007199254740992)), (141785/36028797018963968), by norm_num⟩
  | 3 => ⟨((743147302507311/4503599627370496), (7775833825635/4503599627370496)), (177727/9007199254740992), by norm_num⟩
  | 2 => ⟨((555495917329053/1125899906842624), (1936218379299/281474976710656)), (178473/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103531244797833/1125899906842624), (23080209199863/1125899906842624)), (134789/562949953421312), by norm_num⟩
  | 0 => ⟨((135142381444457/140737488355328), (11386278891739/281474976710656)), (546667/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((135142381444457/140737488355328), (11386278891739/281474976710656)), (2085369114402389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2072630584931289/2251799813685248), (87468881998823/1125899906842624)), (68381/70368744177664), by norm_num⟩
  | 2 => ⟨((1894126775567937/2251799813685248), (322036939445003/2251799813685248)), (4368161/2251799813685248), by norm_num⟩
  | 3 => ⟨((1547210560362571/2251799813685248), (270884998754153/1125899906842624)), (8598065/2251799813685248), by norm_num⟩
  | 4 => ⟨((116592612669903/281474976710656), (186124951325185/562949953421312)), (15952743/2251799813685248), by norm_num⟩
  | 5 => ⟨((280420690202357/4503599627370496), (1233547343307569/4503599627370496)), (47529253/4503599627370496), by norm_num⟩
  | 6 => ⟨((-640822188507959/9007199254740992), (307231748848473/9007199254740992)), (127822679/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1325179879/16777216)), (1/33554432), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-43349291/16777216), (-674132519/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((169691583691797/9007199254740992), (658393731796665/9007199254740992)), (50568111/9007199254740992), by norm_num⟩
  | 1 => ⟨((-484800867/8589934592), (-470249975/2147483648)), (291/17179869184), by norm_num⟩
  | 2 => ⟨((1452333603/17179869184), (5634972107/17179869184)), (219/8589934592), by norm_num⟩
  | 3 => ⟨((-1450267549/17179869184), (-2813477967/8589934592)), (55/2147483648), by norm_num⟩
  | 4 => ⟨((1086153325/17179869184), (4214213373/17179869184)), (331/17179869184), by norm_num⟩
  | 5 => ⟨((-325382457/8589934592), (-5049862003/34359738368)), (399/34359738368), by norm_num⟩
  | 6 => ⟨((40614947/2147483648), (5042678193/68719476736)), (25/4294967296), by norm_num⟩
  | 7 => ⟨((-278106303/34359738368), (-2158073401/68719476736)), (43/17179869184), by norm_num⟩
  | 8 => ⟨((1666264055/549755813888), (808126267/68719476736)), (259/274877906944), by norm_num⟩
  | 9 => ⟨((-554631223/549755813888), (-4303875447/1099511627776)), (347/1099511627776), by norm_num⟩
  | 10 => ⟨((332305331/1099511627776), (5157303431/4398046511104)), (209/2199023255552), by norm_num⟩
  | 11 => ⟨((-1447996807/17592186044416), (-5618145575/17592186044416)), (457/17592186044416), by norm_num⟩
  | 12 => ⟨((722968461/35184372088832), (5610153339/70368744177664)), (229/35184372088832), by norm_num⟩
  | 13 => ⟨((-666406139/140737488355328), (-161601129/8796093022208)), (53/35184372088832), by norm_num⟩
  | 14 => ⟨((1140785359/1125899906842624), (4426182561/1125899906842624)), (365/1125899906842624), by norm_num⟩
  | 15 => ⟨((-911330005/4503599627370496), (-1767954393/2251799813685248)), (147/2251799813685248), by norm_num⟩
  | 16 => ⟨((682525177/18014398509481984), (5296318033/36028797018963968)), (221/18014398509481984), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1717559035107/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888991117472283/316912650057057350374175801344), (126933353457/39614081257132168796771975168)), (46201/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888857106060593/39614081257132168796771975168), (571072147393/9903520314283042199192993792)), (25991/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888577013609449/2475880078570760549798248448), (1213208491915/1237940039285380274899124224)), (55239/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770243410212201/154742504910672534362390528), (2425697696667/154742504910672534362390528)), (55247/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548665509311655/9671406556917033397649408), (2273327623897/9671406556917033397649408)), (51803/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157251489169885/75557863725914323419136), (1988398014595/604462909807314587353088)), (45337/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886530086352549/75557863725914323419136), (3229715577475/75557863725914323419136)), (9211/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162074155050479/590295810358705651712), (151314690339/295147905179352825856)), (55281/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620147487512037/590295810358705651712), (3326890511231/590295810358705651712)), (76035/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455462364296019/18446744073709551616), (2077783142307/36893488147419103232)), (95079/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910414714870633/4611686018427387904), (1167706538175/2305843009213693952)), (107013/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592078983599323/1152921504606846976), (2332799506217/576460752303423488)), (107075/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596456712132591/72057594037927936), (4076525823739/144115188075855872)), (1465/2251799813685248), by norm_num⟩
  | 4 => ⟨((1489138752413523/36028797018963968), (6103060141497/36028797018963968)), (70389/18014398509481984), by norm_num⟩
  | 3 => ⟨((185767312437571/1125899906842624), (1902085161513/2251799813685248)), (22027/1125899906842624), by norm_num⟩
  | 2 => ⟨((2221722118314131/4503599627370496), (1894423680063/562949953421312)), (353163/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206795820178907/2251799813685248), (5645104825209/562949953421312)), (531581/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162241460710623/2251799813685248), (11138389301231/562949953421312)), (267637/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162241460710623/2251799813685248), (11138389301231/562949953421312)), (1020954134227561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1037681743855411/1125899906842624), (85563155325933/2251799813685248)), (2098305/2251799813685248), by norm_num⟩
  | 2 => ⟨((1909500358975923/2251799813685248), (39429492661285/562949953421312)), (4027253/2251799813685248), by norm_num⟩
  | 3 => ⟨((804093827669829/1125899906842624), (66871513118871/562949953421312)), (3697137/1125899906842624), by norm_num⟩
  | 4 => ⟨((139594932642037/281474976710656), (191032864001621/1125899906842624)), (12318365/2251799813685248), by norm_num⟩
  | 5 => ⟨((489021034121421/2251799813685248), (378963985990619/2251799813685248)), (8199253/1125899906842624), by norm_num⟩
  | 6 => ⟨((169691583691797/9007199254740992), (658393731796665/9007199254740992)), (50568111/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-674132519/8388608)), (1/33554432), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-88110603/33554432), (-5480894533/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((40741324991171/562949953421312), (12667457522507/18014398509481984)), (20444345/9007199254740992), by norm_num⟩
  | 1 => ⟨((-7570671269/34359738368), (-73559491/34359738368)), (15/2147483648), by norm_num⟩
  | 2 => ⟨((5762269637/17179869184), (13997095/4294967296)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((-5847786401/17179869184), (-56819293/17179869184)), (47/4294967296), by norm_num⟩
  | 4 => ⟨((4450929227/17179869184), (43246903/17179869184)), (145/17179869184), by norm_num⟩
  | 5 => ⟨((-677547695/4294967296), (-52666467/34359738368)), (89/17179869184), by norm_num⟩
  | 6 => ⟨((5500824427/68719476736), (3340505/4294967296)), (91/34359738368), by norm_num⟩
  | 7 => ⟨((-1196241671/34359738368), (-46492537/137438953472)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((7283969217/549755813888), (35386893/274877906944)), (123/274877906944), by norm_num⟩
  | 9 => ⟨((-4928046159/1099511627776), (-47882751/1099511627776)), (21/137438953472), by norm_num⟩
  | 10 => ⟨((3000709421/2199023255552), (14578011/1099511627776)), (103/2199023255552), by norm_num⟩
  | 11 => ⟨((-830520651/2199023255552), (-32278605/8796093022208)), (115/8796093022208), by norm_num⟩
  | 12 => ⟨((6742770019/70368744177664), (65515291/70368744177664)), (59/17592186044416), by norm_num⟩
  | 13 => ⟨((-6316466035/281474976710656), (-61373161/281474976710656)), (223/281474976710656), by norm_num⟩
  | 14 => ⟨((686807949/140737488355328), (13346569/281474976710656)), (49/281474976710656), by norm_num⟩
  | 15 => ⟨((-4460804717/4503599627370496), (-43342857/4503599627370496)), (161/4503599627370496), by norm_num⟩
  | 16 => ⟨((3395255013/18014398509481984), (32989575/18014398509481984)), (247/36028797018963968), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (1582033349/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444479907870927/158456325028528675187087900672), (7482203233/316912650057057350374175801344)), (23051/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944393407505353/19807040628566084398385987584), (16831150057/39614081257132168796771975168)), (6483/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944251256030021/1237940039285380274899124224), (17878309727/2475880078570760549798248448)), (27553/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885084556985857/77371252455336267181195264), (8936463435/77371252455336267181195264)), (27553/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548596074563985/9671406556917033397649408), (8375075975/4835703278458516698824704)), (25831/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257951375749163/604462909807314587353088), (3662667137/151115727451828646838272)), (45205/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886432120711103/75557863725914323419136), (743644605/2361183241434822606848)), (73457/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648260061380639/2361183241434822606848), (8919052799/2361183241434822606848)), (55093/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620047529480633/590295810358705651712), (24512187471/590295810358705651712)), (75753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821725376460665/73786976294838206464), (30617440707/73786976294838206464)), (23673/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910345514365117/4611686018427387904), (34413308707/9223372036854775808)), (106529/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591942066742851/1152921504606846976), (17187106143/576460752303423488)), (53265/576460752303423488), by norm_num⟩
  | 5 => ⟨((596397643717975/72057594037927936), (15016756137/72057594037927936)), (93215/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488964867397801/36028797018963968), (44962571227/36028797018963968)), (8739/2251799813685248), by norm_num⟩
  | 3 => ⟨((742963464906511/4503599627370496), (28025040165/4503599627370496)), (2731/140737488355328), by norm_num⟩
  | 2 => ⟨((2221316243718373/4503599627370496), (55821050983/2251799813685248)), (174791/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206229839202031/2251799813685248), (166322690925/2251799813685248)), (4097/17592186044416), by norm_num⟩
  | 0 => ⟨((2161278847020943/2251799813685248), (164055766215/1125899906842624)), (524515/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161278847020943/2251799813685248), (164055766215/1125899906842624)), (2000865940574264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037198359848501/1125899906842624), (314921650759/1125899906842624)), (1007013/1125899906842624), by norm_num⟩
  | 2 => ⟨((955484880990531/1125899906842624), (1160444965535/2251799813685248)), (1855919/1125899906842624), by norm_num⟩
  | 3 => ⟨((810863395222725/1125899906842624), (1969602471857/2251799813685248)), (6303863/2251799813685248), by norm_num⟩
  | 4 => ⟨((583975957261141/1125899906842624), (1418490700517/1125899906842624)), (2272751/562949953421312), by norm_num⟩
  | 5 => ⟨((1211567403001363/4503599627370496), (5885883529547/4503599627370496)), (18906915/4503599627370496), by norm_num⟩
  | 6 => ⟨((40741324991171/562949953421312), (12667457522507/18014398509481984)), (20444345/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-5480894533/67108864)), (1/33554432), by norm_num⟩, -13, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile039Terms2
