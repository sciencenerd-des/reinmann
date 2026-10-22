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
namespace Reinmann.XiBand97.Tile049Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨49,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15131/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15131/512))
  have he : value ((69/80), (15131/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-5498737781/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((797311239846085/9007199254740992), (-208834658124159/9007199254740992)), (32284197/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4216415695/17179869184), (1104378925/17179869184)), (43/4294967296), by norm_num⟩
  | 2 => ⟨((2922596651/8589934592), (-382748569/4294967296)), (241/17179869184), by norm_num⟩
  | 3 => ⟨((-1350526419/4294967296), (1414939155/17179869184)), (225/17179869184), by norm_num⟩
  | 4 => ⟨((3744454319/17179869184), (-490380543/8589934592)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((-4152732727/34359738368), (1087698851/34359738368)), (177/34359738368), by norm_num⟩
  | 6 => ⟨((3837939975/68719476736), (-1005247189/68719476736)), (165/68719476736), by norm_num⟩
  | 7 => ⟨((-6080588053/274877906944), (1592649725/274877906944)), (33/34359738368), by norm_num⟩
  | 8 => ⟨((4214742465/549755813888), (-1103940667/549755813888)), (185/549755813888), by norm_num⟩
  | 9 => ⟨((-5193665523/2199023255552), (1360343753/2199023255552)), (115/1099511627776), by norm_num⟩
  | 10 => ⟨((5759959383/8796093022208), (-1508669499/8796093022208)), (257/8796093022208), by norm_num⟩
  | 11 => ⟨((-5807272155/35184372088832), (190132729/4398046511104)), (261/35184372088832), by norm_num⟩
  | 12 => ⟨((5367059095/140737488355328), (-1405759627/140737488355328)), (243/140737488355328), by norm_num⟩
  | 13 => ⟨((-4578660775/562949953421312), (1199259473/562949953421312)), (209/562949953421312), by norm_num⟩
  | 14 => ⟨((1813534747/1125899906842624), (-475007613/1125899906842624)), (167/2251799813685248), by norm_num⟩
  | 15 => ⟨((-2681699193/9007199254740992), (1404800801/18014398509481984)), (249/18014398509481984), by norm_num⟩
  | 16 => ⟨((1858812235/36028797018963968), (-973733715/72057594037927936)), (175/72057594037927936), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-333688781293/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778280854058647/633825300114114700748351602688), (-98674223517/158456325028528675187087900672)), (46121/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944596548863949/19807040628566084398385987584), (-110985509019/9903520314283042199192993792)), (51887/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888934070899947/2475880078570760549798248448), (-58946675491/309485009821345068724781056)), (55131/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770600541763187/154742504910672534362390528), (-235722038321/77371252455336267181195264)), (55133/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193625049866935/1208925819614629174706176), (-3451886419/75557863725914323419136)), (6461/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629152510227093/302231454903657293676544), (-193236987503/302231454903657293676544)), (45229/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29484477072507/1180591620717411303424), (-627762884105/75557863725914323419136)), (73501/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324237675928795/1180591620717411303424), (-58824640371/590295810358705651712)), (6891/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810319604026955/295147905179352825856), (-323352788921/295147905179352825856)), (37903/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911232209878861/36893488147419103232), (-201958541141/18446744073709551616)), (23691/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821521690136113/9223372036854775808), (-28376901105/288230376151711744)), (106619/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199096472041883/144115188075855872), (-453560519267/576460752303423488)), (13329/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193520214001975/144115188075855872), (-396337473023/72057594037927936)), (93317/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490050122245123/36028797018963968), (-296725940305/9007199254740992)), (140003/36028797018963968), by norm_num⟩
  | 3 => ⟨((743639885161329/4503599627370496), (-1479946890055/9007199254740992)), (43763/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112005386664349/2251799813685248), (-1474437322205/2251799813685248)), (350251/4503599627370496), by norm_num⟩
  | 1 => ⟨((276280483668765/281474976710656), (-2197933200903/1125899906842624)), (262875/1125899906842624), by norm_num⟩
  | 0 => ⟨((542299133278879/562949953421312), (-2170640507045/562949953421312)), (526511/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((542299133278879/562949953421312), (-2170640507045/562949953421312)), (2008480076316451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1044794964410345/1125899906842624), (-8364057646521/1125899906842624)), (2036909/2251799813685248), by norm_num⟩
  | 2 => ⟨((242367583824099/281474976710656), (-31046188948107/2251799813685248)), (1905311/1125899906842624), by norm_num⟩
  | 3 => ⟨((834560655744859/1125899906842624), (-26732713117991/1125899906842624)), (3333723/1125899906842624), by norm_num⟩
  | 4 => ⟨((1235947966489875/2251799813685248), (-4953830809915/140737488355328)), (2550239/562949953421312), by norm_num⟩
  | 5 => ⟨((168896565989505/562949953421312), (-87008474961427/2251799813685248)), (5958075/1125899906842624), by norm_num⟩
  | 6 => ⟨((797311239846085/9007199254740992), (-208834658124159/9007199254740992)), (32284197/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-5498737781/67108864)), (1/33554432), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-163990341/67108864), (-5618971589/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-718251943313155/18014398509481984), (-1389809904365625/18014398509481984)), (140053373/18014398509481984), by norm_num⟩
  | 1 => ⟨((1940690031/17179869184), (938803665/4294967296)), (381/17179869184), by norm_num⟩
  | 2 => ⟨((-1374597223/8589934592), (-5319662143/17179869184)), (271/8589934592), by norm_num⟩
  | 3 => ⟨((2596351463/17179869184), (2511956295/8589934592)), (257/8589934592), by norm_num⟩
  | 4 => ⟨((-1839004403/17179869184), (-111201689/536870912)), (183/8589934592), by norm_num⟩
  | 5 => ⟨((1042058363/17179869184), (4032743797/34359738368)), (417/34359738368), by norm_num⟩
  | 6 => ⟨((-984124553/34359738368), (-952135295/17179869184)), (99/17179869184), by norm_num⟩
  | 7 => ⟨((796638519/68719476736), (1541487099/68719476736)), (161/68719476736), by norm_num⟩
  | 8 => ⟨((-2257046883/549755813888), (-4367361819/549755813888)), (229/274877906944), by norm_num⟩
  | 9 => ⟨((2842086821/2199023255552), (171856497/68719476736)), (579/2199023255552), by norm_num⟩
  | 10 => ⟨((-1610447661/4398046511104), (-779049793/1099511627776)), (165/2199023255552), by norm_num⟩
  | 11 => ⟨((829589419/8796093022208), (3210493483/17592186044416)), (171/8796093022208), by norm_num⟩
  | 12 => ⟨((-1566935875/70368744177664), (-1516002163/35184372088832)), (325/70368744177664), by norm_num⟩
  | 13 => ⟨((2731977619/562949953421312), (1321586941/140737488355328)), (569/562949953421312), by norm_num⟩
  | 14 => ⟨((-1105753635/1125899906842624), (-4279243151/2251799813685248)), (463/2251799813685248), by norm_num⟩
  | 15 => ⟨((835422921/4503599627370496), (3233069013/9007199254740992)), (351/9007199254740992), by norm_num⟩
  | 16 => ⟨((-295866421/9007199254740992), (-4579987135/72057594037927936)), (499/72057594037927936), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644697451/10141204801825835211973625643008), (-1333739117805/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889097520918775/316912650057057350374175801344), (-49295300091/9903520314283042199192993792)), (2891/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944548143680829/19807040628566084398385987584), (-1774250405481/19807040628566084398385987584)), (3253/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944415424220159/1237940039285380274899124224), (-3769341537843/2475880078570760549798248448)), (55313/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885248456553835/77371252455336267181195264), (-942070926337/38685626227668133590597632)), (27663/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548902815822121/9671406556917033397649408), (-3531642349653/9671406556917033397649408)), (25941/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629109602178749/302231454903657293676544), (-772265948731/151115727451828646838272)), (22705/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886866274396529/75557863725914323419136), (-1254405830937/18889465931478580854784)), (73817/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296844804629823/4722366482869645213696), (-1880688044463/2361183241434822606848)), (27693/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810246226014297/295147905179352825856), (-2584450643337/295147905179352825856)), (2381/18446744073709551616), by norm_num⟩
  | 8 => ⟨((56946226880221/2305843009213693952), (-3228321442111/36893488147419103232)), (95295/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910655516161649/4611686018427387904), (-3628781116397/4611686018427387904)), (107283/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592558183290197/1152921504606846976), (-3624933564263/576460752303423488)), (107379/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193330026682611/144115188075855872), (-6334985212203/144115188075855872)), (5879/9007199254740992), by norm_num⟩
  | 4 => ⟨((744879138121371/18014398509481984), (-2371300480933/9007199254740992)), (141311/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486903522938071/9007199254740992), (-5913158578945/4503599627370496)), (177015/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111612076998177/2251799813685248), (-11781134344701/2251799813685248)), (355163/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208979309236007/2251799813685248), (-35118153641173/2251799813685248)), (16737/70368744177664), by norm_num⟩
  | 0 => ⟨((2166332950283067/2251799813685248), (-69339291927799/2251799813685248)), (1082577/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166332950283067/2251799813685248), (-69339291927799/2251799813685248)), (4129703530318450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2081974821023053/2251799813685248), (-133415050431729/2251799813685248)), (134353/140737488355328), by norm_num⟩
  | 2 => ⟨((1917052996210821/2251799813685248), (-246706455925843/2251799813685248)), (1057445/562949953421312), by norm_num⟩
  | 3 => ⟨((1605039707757337/2251799813685248), (-420063406740559/2251799813685248)), (8128811/2251799813685248), by norm_num⟩
  | 4 => ⟨((266420130156683/562949953421312), (-299413137658541/1125899906842624)), (7310455/1125899906842624), by norm_num⟩
  | 5 => ⟨((690187519610259/4503599627370496), (-1133595434134937/4503599627370496)), (21615247/2251799813685248), by norm_num⟩
  | 6 => ⟨((-718251943313155/18014398509481984), (-1389809904365625/18014398509481984)), (140053373/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-163990341/67108864), (-5618971589/67108864)), (1/33554432), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-2866165519/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1232939021604727/18014398509481984), (835175910411777/18014398509481984)), (67856159/9007199254740992), by norm_num⟩
  | 1 => ⟨((3398563507/17179869184), (-2302140107/17179869184)), (47/2147483648), by norm_num⟩
  | 2 => ⟨((-4911555989/17179869184), (1663510187/8589934592)), (273/8589934592), by norm_num⟩
  | 3 => ⟨((18484665/67108864), (-3205441909/17179869184)), (33/1073741824), by norm_num⟩
  | 4 => ⟨((-3419363435/17179869184), (2316229691/17179869184)), (383/17179869184), by norm_num⟩
  | 5 => ⟨((3953292601/34359738368), (-1338952977/17179869184)), (445/34359738368), by norm_num⟩
  | 6 => ⟨((-952207107/17179869184), (2580047913/68719476736)), (431/68719476736), by norm_num⟩
  | 7 => ⟨((1572704303/68719476736), (-2130656463/137438953472)), (179/68719476736), by norm_num⟩
  | 8 => ⟨((-4545700101/549755813888), (3079194633/549755813888)), (65/68719476736), by norm_num⟩
  | 9 => ⟨((1459862577/549755813888), (-1977781601/1099511627776)), (335/1099511627776), by norm_num⟩
  | 10 => ⟨((-3375636451/4398046511104), (2286609633/4398046511104)), (389/4398046511104), by norm_num⟩
  | 11 => ⟨((443492921/2199023255552), (-2403327965/17592186044416)), (411/17592186044416), by norm_num⟩
  | 12 => ⟨((-1709145885/35184372088832), (1157751879/35184372088832)), (199/35184372088832), by norm_num⟩
  | 13 => ⟨((3040041229/281474976710656), (-514820513/70368744177664)), (89/70368744177664), by norm_num⟩
  | 14 => ⟨((-5021056749/2251799813685248), (3401194677/2251799813685248)), (295/1125899906842624), by norm_num⟩
  | 15 => ⟨((3870058833/9007199254740992), (-2621524543/9007199254740992)), (457/9007199254740992), by norm_num⟩
  | 16 => ⟨((-699119297/9007199254740992), (947147563/18014398509481984)), (83/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (3316716931851/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889058090146603/316912650057057350374175801344), (122576629611/19807040628566084398385987584)), (23147/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889007426353963/39614081257132168796771975168), (2205893903521/19807040628566084398385987584)), (52093/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944368121478903/1237940039285380274899124224), (1171582696867/618970019642690137449562112)), (55363/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770402093367045/154742504910672534362390528), (4684988102529/154742504910672534362390528)), (55379/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774406847429133/4835703278458516698824704), (274421881303/604462909807314587353088)), (51935/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629070498136665/302231454903657293676544), (3840480494651/604462909807314587353088)), (45461/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886738760642475/75557863725914323419136), (6238108200673/75557863725914323419136)), (73905/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296748797358067/4722366482869645213696), (4676243476387/4722366482869645213696)), (27729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620359838460885/590295810358705651712), (6426037660189/590295810358705651712)), (19075/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227764073669655/9223372036854775808), (501678387289/4611686018427387904)), (23861/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821122287308779/9223372036854775808), (1127798476897/1152921504606846976)), (107469/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592367891490483/1152921504606846976), (9012615698565/1152921504606846976)), (107587/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193161786245519/144115188075855872), (7875054494655/144115188075855872)), (1473/2251799813685248), by norm_num⟩
  | 4 => ⟨((744751228947183/18014398509481984), (11790636734287/36028797018963968)), (141675/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486577727180681/9007199254740992), (7349972489079/4503599627370496)), (177563/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111277303147481/2251799813685248), (14642524225439/2251799813685248)), (44567/562949953421312), by norm_num⟩
  | 1 => ⟨((551982622231245/562949953421312), (5455151073561/281474976710656)), (269167/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082029827363165/1125899906842624), (43070699723431/1125899906842624)), (1090857/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082029827363165/1125899906842624), (43070699723431/1125899906842624)), (4161289223677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519110737564119/562949953421312), (82784946517753/1125899906842624)), (1090083/1125899906842624), by norm_num⟩
  | 2 => ⟨((951283926340369/1125899906842624), (152676288131335/1125899906842624)), (2170691/1125899906842624), by norm_num⟩
  | 3 => ⟨((783045681234983/1125899906842624), (257995400745603/1125899906842624)), (4256785/1125899906842624), by norm_num⟩
  | 4 => ⟨((485477357954233/1125899906842624), (179431744424659/562949953421312)), (15743809/2251799813685248), by norm_num⟩
  | 5 => ⟨((379803784714447/4503599627370496), (618954126824197/2251799813685248)), (47226725/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1232939021604727/18014398509481984), (835175910411777/18014398509481984)), (67856159/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-2866165519/33554432)), (1/33554432), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-5839559877/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((828645291782935/18014398509481984), (1154783390746681/18014398509481984)), (5575807/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1163432835/8589934592), (-1621336569/8589934592)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((3425656989/17179869184), (74592603/268435456)), (373/17179869184), by norm_num⟩
  | 3 => ⟨((-210138291/1073741824), (-4685511847/17179869184)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((618739375/4294967296), (1724525465/8589934592)), (273/17179869184), by norm_num⟩
  | 5 => ⟨((-1457472267/17179869184), (-495875/4194304)), (81/8589934592), by norm_num⟩
  | 6 => ⟨((2860958769/68719476736), (3986974525/68719476736)), (5/1073741824), by norm_num⟩
  | 7 => ⟨((-1203416931/68719476736), (-26204025/1073741824)), (271/137438953472), by norm_num⟩
  | 8 => ⟨((442923465/68719476736), (617249221/68719476736)), (201/274877906944), by norm_num⟩
  | 9 => ⟨((-2318508649/1099511627776), (-1615513481/549755813888)), (33/137438953472), by norm_num⟩
  | 10 => ⟨((170667681/274877906944), (951356173/1099511627776)), (313/4398046511104), by norm_num⟩
  | 11 => ⟨((-1461878029/8796093022208), (-2037243781/8796093022208)), (337/17592186044416), by norm_num⟩
  | 12 => ⟨((2869607101/70368744177664), (1999513333/35184372088832)), (333/70368744177664), by norm_num⟩
  | 13 => ⟨((-2599810155/281474976710656), (-3623043075/281474976710656)), (19/17592186044416), by norm_num⟩
  | 14 => ⟨((2187137817/1125899906842624), (3047951215/1125899906842624)), (257/1125899906842624), by norm_num⟩
  | 15 => ⟨((-26832891/70368744177664), (-2393201697/4503599627370496)), (203/4503599627370496), by norm_num⟩
  | 16 => ⟨((1264124963/18014398509481984), (3523318181/36028797018963968)), (301/36028797018963968), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1235359468259/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444512861884701/158456325028528675187087900672), (365215461041/158456325028528675187087900672)), (11543/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888935011779457/39614081257132168796771975168), (1643108339707/39614081257132168796771975168)), (51949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888659845406389/2475880078570760549798248448), (218168810723/309485009821345068724781056)), (55201/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885163153005715/77371252455336267181195264), (1744842075773/154742504910672534362390528)), (55207/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548743292060511/9671406556917033397649408), (408812365097/2417851639229258349412352)), (51763/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258080041127811/604462909807314587353088), (1430303517245/604462909807314587353088)), (45299/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886640921064491/75557863725914323419136), (290403955303/9444732965739290427392)), (73623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81042279842715/295147905179352825856), (870769541561/2361183241434822606848)), (13807/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620262118653227/590295810358705651712), (2393179580435/590295810358705651712)), (75955/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113874563489653/4611686018427387904), (1494660526461/36893488147419103232)), (47485/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820991303263667/9223372036854775808), (3360027770633/9223372036854775808)), (26719/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398060329607539/288230376151711744), (1678166781529/576460752303423488)), (13365/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193055984508863/144115188075855872), (2932641116955/144115188075855872)), (93605/144115188075855872), by norm_num⟩
  | 4 => ⟨((744676811529311/18014398509481984), (4390673238977/36028797018963968)), (35127/9007199254740992), by norm_num⟩
  | 3 => ⟨((92900555078177/562949953421312), (1368466533597/2251799813685248)), (87905/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222268224093317/4503599627370496), (10904423190265/4503599627370496)), (88037/1125899906842624), by norm_num⟩
  | 1 => ⟨((2207628201935301/2251799813685248), (4062192779139/562949953421312)), (132387/562949953421312), by norm_num⟩
  | 0 => ⟨((1081979162758125/1125899906842624), (2004283334733/140737488355328)), (532217/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081979162758125/1125899906842624), (2004283334733/140737488355328)), (2030246738914107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039543394418697/1125899906842624), (30817557280393/1125899906842624)), (2076141/2251799813685248), by norm_num⟩
  | 2 => ⟨((1917933806515067/2251799813685248), (113815403689985/2251799813685248)), (3947457/2251799813685248), by norm_num⟩
  | 3 => ⟨((406954041582559/562949953421312), (48470207944891/562949953421312)), (7123407/2251799813685248), by norm_num⟩
  | 4 => ⟨((580023960957583/1125899906842624), (280311198530405/2251799813685248)), (720351/140737488355328), by norm_num⟩
  | 5 => ⟨((1125443572219125/4503599627370496), (72203226363309/562949953421312)), (29489347/4503599627370496), by norm_num⟩
  | 6 => ⟨((828645291782935/18014398509481984), (1154783390746681/18014398509481984)), (5575807/1125899906842624), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-5839559877/67108864)), (1/33554432), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-5941287325/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((573337492149621/9007199254740992), (-182730443372581/4503599627370496)), (67795519/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1637998227/8589934592), (2088209101/17179869184)), (195/17179869184), by norm_num⟩
  | 2 => ⟨((613375519/2147483648), (-3127857699/17179869184)), (295/17179869184), by norm_num⟩
  | 3 => ⟨((-306251473/1073741824), (3123408085/17179869184)), (297/17179869184), by norm_num⟩
  | 4 => ⟨((1834894843/8589934592), (-2339223601/17179869184)), (7/536870912), by norm_num⟩
  | 5 => ⟨((-274842685/2147483648), (2803075055/34359738368)), (271/34359738368), by norm_num⟩
  | 6 => ⟨((548903401/8589934592), (-2799087469/68719476736)), (273/68719476736), by norm_num⟩
  | 7 => ⟨((-3758554591/137438953472), (1197902381/68719476736)), (59/34359738368), by norm_num⟩
  | 8 => ⟨((1407452911/137438953472), (-448574353/68719476736)), (179/274877906944), by norm_num⟩
  | 9 => ⟨((-3747868541/1099511627776), (2388993185/1099511627776)), (15/68719476736), by norm_num⟩
  | 10 => ⟨((2245522149/2199023255552), (-1431356797/2199023255552)), (289/4398046511104), by norm_num⟩
  | 11 => ⟨((-2446175699/8796093022208), (1559258819/8796093022208)), (317/17592186044416), by norm_num⟩
  | 12 => ⟨((4885391659/70368744177664), (-3114081311/70368744177664)), (319/70368744177664), by norm_num⟩
  | 13 => ⟨((-4503177065/281474976710656), (2870447349/281474976710656)), (37/35184372088832), by norm_num⟩
  | 14 => ⟨((3854375105/1125899906842624), (-2456883361/1125899906842624)), (255/1125899906842624), by norm_num⟩
  | 15 => ⟨((-769778393/1125899906842624), (1962710607/4503599627370496)), (205/4503599627370496), by norm_num⟩
  | 16 => ⟨((4612099951/36028797018963968), (-1469938877/18014398509481984)), (155/18014398509481984), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-369606825725/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111124002305787/39614081257132168796771975168), (-874085753391/633825300114114700748351602688)), (721/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((118053702014595/2475880078570760549798248448), (-983127211307/39614081257132168796771975168)), (25957/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472144851191691/618970019642690137449562112), (-522148741719/1237940039285380274899124224)), (27581/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442561487453099/38685626227668133590597632), (-260997014649/38685626227668133590597632)), (27583/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387167011945645/2417851639229258349412352), (-61150635547/604462909807314587353088)), (25861/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314503572994081/151115727451828646838272), (-213945101305/151115727451828646838272)), (45261/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235816780816947/9444732965739290427392), (-695013770229/37778931862957161709568)), (73555/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296596618306647/4722366482869645213696), (-1041982294695/4722366482869645213696)), (55173/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810076275219405/295147905179352825856), (-1431851390883/590295810358705651712)), (75873/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821856412331647/73786976294838206464), (-1788503841909/73786976294838206464)), (94857/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28450595533125/144115188075855872), (-2010266649957/9223372036854775808)), (106735/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592088740401499/1152921504606846976), (-2008018867181/1152921504606846976)), (53381/576460752303423488), by norm_num⟩
  | 5 => ⟨((596461582342653/72057594037927936), (-1754491093845/144115188075855872)), (93447/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489155761351793/36028797018963968), (-2626694150765/36028797018963968)), (70115/18014398509481984), by norm_num⟩
  | 3 => ⟨((743081969735247/4503599627370496), (-204660128947/562949953421312)), (87697/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221785461910249/4503599627370496), (-6522782016937/4503599627370496)), (175553/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206921741187931/2251799813685248), (-9718578706227/2251799813685248)), (527463/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081307706189363/1125899906842624), (-19176340047405/2251799813685248)), (8267/17592186044416), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081307706189363/1125899906842624), (-19176340047405/2251799813685248)), (31536102362030739/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1038399963757629/1125899906842624), (-18416845177575/1125899906842624)), (512639/562949953421312), by norm_num⟩
  | 2 => ⟨((14959357427035/17592186044416), (-8492784859781/281474976710656)), (962369/562949953421312), by norm_num⟩
  | 3 => ⟨((1626181088754237/2251799813685248), (-115548213460329/2251799813685248)), (847379/281474976710656), by norm_num⟩
  | 4 => ⟨((584224567343315/1125899906842624), (-20861348156545/281474976710656)), (1310867/281474976710656), by norm_num⟩
  | 5 => ⟨((148483541700693/562949953421312), (-346395611954783/4503599627370496)), (24875435/4503599627370496), by norm_num⟩
  | 6 => ⟨((573337492149621/9007199254740992), (-182730443372581/4503599627370496)), (67795519/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-5941287325/67108864)), (1/33554432), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-754756305/8388608)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-138412080908635/4503599627370496), (-1180392347375149/18014398509481984)), (116453637/18014398509481984), by norm_num⟩
  | 1 => ⟨((1607508415/17179869184), (1713624471/8589934592)), (85/4294967296), by norm_num⟩
  | 2 => ⟨((-2447047719/17179869184), (-652146019/2147483648)), (65/2147483648), by norm_num⟩
  | 3 => ⟨((310420487/2147483648), (5294595167/17179869184)), (265/8589934592), by norm_num⟩
  | 4 => ⟨((-472541069/4294967296), (-2014939223/8589934592)), (405/17179869184), by norm_num⟩
  | 5 => ⟨((575464755/8589934592), (1226905535/8589934592)), (495/34359738368), by norm_num⟩
  | 6 => ⟨((-1168010239/34359738368), (-622556905/8589934592)), (505/68719476736), by norm_num⟩
  | 7 => ⟨((1016009537/68719476736), (2166158247/68719476736)), (441/137438953472), by norm_num⟩
  | 8 => ⟨((-386657979/68719476736), (-3297458693/274877906944)), (337/274877906944), by norm_num⟩
  | 9 => ⟨((1046390127/549755813888), (4461860879/1099511627776)), (229/549755813888), by norm_num⟩
  | 10 => ⟨((-159287911/274877906944), (-339605889/274877906944)), (35/274877906944), by norm_num⟩
  | 11 => ⟨((1410779983/8796093022208), (1503909453/4398046511104)), (39/1099511627776), by norm_num⟩
  | 12 => ⟨((-89482319/2199023255552), (-3052457383/35184372088832)), (159/17592186044416), by norm_num⟩
  | 13 => ⟨((2682396829/281474976710656), (5718938457/281474976710656)), (299/140737488355328), by norm_num⟩
  | 14 => ⟨((-1166659619/562949953421312), (-4974696129/1125899906842624)), (261/562949953421312), by norm_num⟩
  | 15 => ⟨((1894358073/4503599627370496), (2019409865/2251799813685248)), (213/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1441853915/18014398509481984), (-1537034661/9007199254740992)), (163/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-2617426951937/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222239311936859/79228162514264337593543950336), (-773692619035/158456325028528675187087900672)), (46253/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472195188883869/9903520314283042199192993792), (-3480819341361/39614081257132168796771975168)), (52045/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888495697437011/2475880078570760549798248448), (-1848689678521/1237940039285380274899124224)), (55309/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770161876344993/154742504910672534362390528), (-3696264657953/154742504910672534362390528)), (55321/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774294420104645/4835703278458516698824704), (-3464064132925/9671406556917033397649408)), (25939/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314486149254121/151115727451828646838272), (-3029872564101/604462909807314587353088)), (22703/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886420264874825/75557863725914323419136), (-4921324673373/75557863725914323419136)), (73811/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296510496402075/4722366482869645213696), (-3689053458965/4722366482869645213696)), (13845/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620033101322401/590295810358705651712), (-5069297649639/590295810358705651712)), (9523/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821705556221481/73786976294838206464), (-6331898783399/73786976294838206464)), (23821/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910333140561259/4611686018427387904), (-7116896505655/9223372036854775808)), (53635/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795957131858471/576460752303423488), (-888598974159/144115188075855872)), (107363/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74547970742937/9007199254740992), (-6211085075759/144115188075855872)), (94049/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488916401834447/36028797018963968), (-9298437252581/36028797018963968)), (141283/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485854444323739/9007199254740992), (-11591269912809/9007199254740992)), (88487/4503599627370496), by norm_num⟩
  | 2 => ⟨((555283943254691/1125899906842624), (-23087435513633/4503599627370496)), (355061/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205871119005209/2251799813685248), (-17197090521595/1125899906842624)), (267691/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160213737522265/2251799813685248), (-16961298699985/562949953421312)), (1081981/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160213737522265/2251799813685248), (-16961298699985/562949953421312)), (4127429970748137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2070308556288967/2251799813685248), (-130171537399541/2251799813685248)), (535287/562949953421312), by norm_num⟩
  | 2 => ⟨((29623754068497/35184372088832), (-119679931593257/1125899906842624)), (4184701/2251799813685248), by norm_num⟩
  | 3 => ⟨((196355181538107/281474976710656), (-403061774301613/2251799813685248)), (7936327/2251799813685248), by norm_num⟩
  | 4 => ⟨((511831482613815/1125899906842624), (-281173370325635/1125899906842624)), (13913797/2251799813685248), by norm_num⟩
  | 5 => ⟨((324918762854017/2251799813685248), (-31955190272835/140737488355328)), (39199609/4503599627370496), by norm_num⟩
  | 6 => ⟨((-138412080908635/4503599627370496), (-1180392347375149/18014398509481984)), (116453637/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-754756305/8388608)), (1/33554432), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨49,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile049Terms2
