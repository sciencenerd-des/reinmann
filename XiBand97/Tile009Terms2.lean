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
namespace Reinmann.XiBand97.Tile009Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (12067/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (12067/640))
  have he : value ((69/80), (12067/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-877050675/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-43884196521773/1125899906842624), (-1491394615170087/18014398509481984)), (293440011/18014398509481984), by norm_num⟩
  | 1 => ⟨((232072503/2147483648), (985866521/4294967296)), (49/1073741824), by norm_num⟩
  | 2 => ⟨((-643441605/4294967296), (-1366701199/4294967296)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((594666313/4294967296), (631550055/2147483648)), (1/16777216), by norm_num⟩
  | 4 => ⟨((-206095639/2147483648), (-109439285/536870912)), (179/4294967296), by norm_num⟩
  | 5 => ⟨((114283689/2147483648), (121372051/1073741824)), (201/8589934592), by norm_num⟩
  | 6 => ⟨((-422482223/17179869184), (-448686373/8589934592)), (187/17179869184), by norm_num⟩
  | 7 => ⟨((334676985/34359738368), (1421740317/68719476736)), (299/68719476736), by norm_num⟩
  | 8 => ⟨((-463960817/137438953472), (-246368823/34359738368)), (209/137438953472), by norm_num⟩
  | 9 => ⟨((142930281/137438953472), (607181707/274877906944)), (65/137438953472), by norm_num⟩
  | 10 => ⟨((-79257377/274877906944), (-1346772123/2199023255552)), (291/2199023255552), by norm_num⟩
  | 11 => ⟨((159816807/2199023255552), (678917309/4398046511104)), (295/8796093022208), by norm_num⟩
  | 12 => ⟨((-590808369/35184372088832), (-627452825/17592186044416)), (275/35184372088832), by norm_num⟩
  | 13 => ⟨((252010557/70368744177664), (1070565309/140737488355328)), (237/140737488355328), by norm_num⟩
  | 14 => ⟨((-199634751/281474976710656), (-848067801/562949953421312)), (95/281474976710656), by norm_num⟩
  | 15 => ⟨((590405397/4503599627370496), (627024859/2251799813685248)), (283/4503599627370496), by norm_num⟩
  | 16 => ⟨((-102309459/4503599627370496), (-434620513/9007199254740992)), (99/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-2619306455699/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778275794048155/633825300114114700748351602688), (-387274078661/79228162514264337593543950336)), (46253/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944593562207761/19807040628566084398385987584), (-3484734850623/39614081257132168796771975168)), (104089/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944463676496705/1237940039285380274899124224), (-3701626857623/2475880078570760549798248448)), (110617/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885296703300373/77371252455336267181195264), (-925152559683/38685626227668133590597632)), (55321/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774496633355713/4835703278458516698824704), (-433530280537/1208925819614629174706176)), (51877/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258298337114829/604462909807314587353088), (-379204056251/75557863725914323419136)), (22703/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886994843034941/75557863725914323419136), (-4927629366965/75557863725914323419136)), (36905/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((20264706433687/73786976294838206464), (-1846976152647/2361183241434822606848)), (13845/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620624980337891/590295810358705651712), (-5076309981749/590295810358705651712)), (152367/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911222436624117/36893488147419103232), (-3170539096989/36893488147419103232)), (23821/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910748640939151/4611686018427387904), (-7127791560065/9223372036854775808)), (107269/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592744351219607/1152921504606846976), (-7120395582077/1152921504606846976)), (107363/576460752303423488), by norm_num⟩
  | 5 => ⟨((298373207888405/36028797018963968), (-3111016803053/72057594037927936)), (2939/2251799813685248), by norm_num⟩
  | 4 => ⟨((745001149410521/18014398509481984), (-9316445209725/36028797018963968)), (282565/36028797018963968), by norm_num⟩
  | 3 => ⟨((371802056639235/2251799813685248), (-11616542062261/9007199254740992)), (353947/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223832582135191/4503599627370496), (-11573109612749/2251799813685248)), (710119/4503599627370496), by norm_num⟩
  | 1 => ⟨((552472371333725/562949953421312), (-17251395255269/1125899906842624)), (535377/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084071664501153/1125899906842624), (-34071582978137/1125899906842624)), (2163905/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084071664501153/1125899906842624), (-34071582978137/1125899906842624)), (8254642495162200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085532637266255/2251799813685248), (-131223166275511/2251799813685248)), (1074499/562949953421312), by norm_num⟩
  | 2 => ⟨((1923895203919277/2251799813685248), (-243067962231609/2251799813685248)), (1057777/281474976710656), by norm_num⟩
  | 3 => ⟨((50546937765963/70368744177664), (-103836336587687/562949953421312)), (4071701/562949953421312), by norm_num⟩
  | 4 => ⟨((542632825517875/1125899906842624), (-149174435459355/562949953421312)), (29406333/2251799813685248), by norm_num⟩
  | 5 => ⟨((364931790654743/2251799813685248), (-71895330052335/281474976710656)), (43929639/2251799813685248), by norm_num⟩
  | 6 => ⟨((-43884196521773/1125899906842624), (-1491394615170087/18014398509481984)), (293440011/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-877050675/16777216)), (1/16777216), by norm_num⟩, -8, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-896228011/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-782158626852543/9007199254740992), (4801569838217/4503599627370496)), (254200863/18014398509481984), by norm_num⟩
  | 1 => ⟨((2113363513/8589934592), (-12973663/4294967296)), (173/4294967296), by norm_num⟩
  | 2 => ⟨((-1496902427/4294967296), (9189289/2147483648)), (247/4294967296), by norm_num⟩
  | 3 => ⟨((706840655/2147483648), (-17356811/4294967296)), (235/4294967296), by norm_num⟩
  | 4 => ⟨((-250328797/1073741824), (12293887/4294967296)), (335/8589934592), by norm_num⟩
  | 5 => ⟨((1134775821/8589934592), (-6966241/4294967296)), (191/8589934592), by norm_num⟩
  | 6 => ⟨((-1071687333/17179869184), (6578949/8589934592)), (91/8589934592), by norm_num⟩
  | 7 => ⟨((108439959/4294967296), (-21302361/68719476736)), (297/68719476736), by norm_num⟩
  | 8 => ⟨((-307233539/34359738368), (15088533/137438953472)), (213/137438953472), by norm_num⟩
  | 9 => ⟨((773740589/274877906944), (-9499785/274877906944)), (135/274877906944), by norm_num⟩
  | 10 => ⟨((-1753737729/2199023255552), (10765967/1099511627776)), (77/549755813888), by norm_num⟩
  | 11 => ⟨((1806804777/8796093022208), (-22183477/8796093022208)), (5/137438953472), by norm_num⟩
  | 12 => ⟨((-426588617/8796093022208), (10475087/17592186044416)), (19/2199023255552), by norm_num⟩
  | 13 => ⟨((1487528077/140737488355328), (-18263481/140737488355328)), (267/140737488355328), by norm_num⟩
  | 14 => ⟨((-1204138399/562949953421312), (14784097/562949953421312)), (109/281474976710656), by norm_num⟩
  | 15 => ⟨((56859683/140737488355328), (-22339467/4503599627370496)), (331/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1288764901/18014398509481984), (15823119/18014398509481984)), (59/4503599627370496), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (4076282869291/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444546979805787/158456325028528675187087900672), (2410565419999/316912650057057350374175801344)), (92675/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889087880249987/39614081257132168796771975168), (1355646956403/9903520314283042199192993792)), (104291/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944410696739955/1237940039285380274899124224), (2880029861137/1237940039285380274899124224)), (110843/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442621717744943/38685626227668133590597632), (719805001513/19342813113834066795298816)), (27721/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548892777931485/9671406556917033397649408), (5396816866461/9671406556917033397649408)), (103995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258209798335519/604462909807314587353088), (4720494446677/604462909807314587353088)), (91039/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886849822855539/75557863725914323419136), (7667578600817/75557863725914323419136)), (9251/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296831446184247/4722366482869645213696), (5747862894481/4722366482869645213696)), (55541/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810236214554071/295147905179352825856), (3949364297597/295147905179352825856)), (152851/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455562938150891/18446744073709551616), (4933269374661/36893488147419103232)), (747/288230376151711744), by norm_num⟩
  | 7 => ⟨((910638341887113/4611686018427387904), (11090410894741/9223372036854775808)), (215369/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592519590505589/1152921504606846976), (2769652524007/288230376151711744)), (215661/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298322873877463/36028797018963968), (2420128945951/36028797018963968)), (23629/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489690985168331/36028797018963968), (14494257232207/36028797018963968)), (284205/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486802862912773/9007199254740992), (9035731045575/4503599627370496)), (44551/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111486735165141/2251799813685248), (9001005908785/1125899906842624)), (89535/562949953421312), by norm_num⟩
  | 1 => ⟨((138030052156105/140737488355328), (6707426073329/281474976710656)), (270777/562949953421312), by norm_num⟩
  | 0 => ⟨((270606492868423/281474976710656), (26484018549559/562949953421312)), (1100549/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270606492868423/281474976710656), (26484018549559/562949953421312)), (4198261265281295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((32441837293413/35184372088832), (101845605751669/1125899906842624)), (2219659/1125899906842624), by norm_num⟩
  | 2 => ⟨((474002893348621/562949953421312), (93906992641585/562949953421312)), (4494853/1125899906842624), by norm_num⟩
  | 3 => ⟨((1533779110018525/2251799813685248), (316278105698437/1125899906842624)), (18137823/2251799813685248), by norm_num⟩
  | 4 => ⟨((216754502985467/562949953421312), (861712037683471/2251799813685248)), (17449423/1125899906842624), by norm_num⟩
  | 5 => ⟨((4073451417521/2251799813685248), (1327151469216935/4503599627370496)), (107168825/4503599627370496), by norm_num⟩
  | 6 => ⟨((-782158626852543/9007199254740992), (4801569838217/4503599627370496)), (254200863/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-896228011/16777216)), (1/16777216), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-1828617769/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-688748883705475/18014398509481984), (1320334202966135/18014398509481984)), (66742395/4503599627370496), by norm_num⟩
  | 1 => ⟨((474629479/4294967296), (-454933249/2147483648)), (185/4294967296), by norm_num⟩
  | 2 => ⟨((-685927821/4294967296), (1314926215/4294967296)), (269/4294967296), by norm_num⟩
  | 3 => ⟨((330431067/2147483648), (-1266875199/4294967296)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((-59691789/536870912), (457717537/2147483648)), (95/2147483648), by norm_num⟩
  | 5 => ⟨((138025169/2147483648), (-529189537/4294967296)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((-531925401/17179869184), (1019702995/17179869184)), (27/2147483648), by norm_num⟩
  | 7 => ⟨((219637451/17179869184), (-105261455/4294967296)), (45/8589934592), by norm_num⟩
  | 8 => ⟨((-634833885/137438953472), (1216978947/137438953472)), (131/68719476736), by norm_num⟩
  | 9 => ⟨((203878437/137438953472), (-390835731/137438953472)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((-471427581/1099511627776), (903728447/1099511627776)), (99/549755813888), by norm_num⟩
  | 11 => ⟨((123872815/1099511627776), (-949858611/4398046511104)), (105/2199023255552), by norm_num⟩
  | 12 => ⟨((-59673081/2199023255552), (114393521/2199023255552)), (51/4398046511104), by norm_num⟩
  | 13 => ⟨((106139931/17592186044416), (-813882591/70368744177664)), (23/8796093022208), by norm_num⟩
  | 14 => ⟨((-701220249/562949953421312), (336060465/140737488355328)), (153/281474976710656), by norm_num⟩
  | 15 => ⟨((135119147/562949953421312), (-129511957/281474976710656)), (119/1125899906842624), by norm_num⟩
  | 16 => ⟨((-390544567/9007199254740992), (374337703/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (2672453028049/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778119073073981/633825300114114700748351602688), (3160525704933/633825300114114700748351602688)), (92511/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889010840403559/39614081257132168796771975168), (888703735441/9903520314283042199192993792)), (104095/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944370041258251/1237940039285380274899124224), (3776029670529/2475880078570760549798248448)), (110625/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770406171339211/154742504910672534362390528), (1887474324383/77371252455336267181195264)), (110651/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774408885538621/4835703278458516698824704), (1768933056423/4835703278458516698824704)), (103763/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258144815866535/604462909807314587353088), (3094484985957/604462909807314587353088)), (90821/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886745441207943/75557863725914323419136), (2513193336145/37778931862957161709568)), (147635/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296754221829157/4722366482869645213696), (3767908315697/4722366482869645213696)), (27693/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810183984533075/295147905179352825856), (5177817713505/590295810358705651712)), (152385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911061879515419/36893488147419103232), (3233845237949/36893488147419103232)), (1489/576460752303423488), by norm_num⟩
  | 7 => ⟨((1821136234548467/9223372036854775808), (7269856323525/9223372036854775808)), (214569/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796191780865253/576460752303423488), (3630996743377/576460752303423488)), (26845/144115188075855872), by norm_num⟩
  | 5 => ⟨((149147178875713/18014398509481984), (6345407529585/144115188075855872)), (94065/72057594037927936), by norm_num⟩
  | 4 => ⟨((744764889483191/18014398509481984), (9500460038421/36028797018963968)), (141313/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486618594450339/9007199254740992), (11844735458231/9007199254740992)), (177019/4503599627370496), by norm_num⟩
  | 2 => ⟨((138916023442911/281474976710656), (23597152394669/4503599627370496)), (710347/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208132831565761/2251799813685248), (8791408080157/562949953421312)), (1071215/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164660730355487/2251799813685248), (69415073073191/2251799813685248)), (2165301/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164660730355487/2251799813685248), (69415073073191/2251799813685248)), (8259967812545012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2078753891320681/2251799813685248), (66728881432129/1125899906842624)), (1074129/562949953421312), by norm_num⟩
  | 2 => ⟨((1911096510470563/2251799813685248), (123201823801113/1125899906842624)), (8441961/2251799813685248), by norm_num⟩
  | 3 => ⟨((797489877420139/1125899906842624), (418244240218819/2251799813685248)), (16176867/2251799813685248), by norm_num⟩
  | 4 => ⟨((1052061626205141/2251799813685248), (296247957599669/1125899906842624)), (28925891/2251799813685248), by norm_num⟩
  | 5 => ⟨((671269489598729/4503599627370496), (1107278208793117/4503599627370496)), (84501815/4503599627370496), by norm_num⟩
  | 6 => ⟨((-688748883705475/18014398509481984), (1320334202966135/18014398509481984)), (66742395/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1828617769/33554432)), (1/16777216), by norm_num⟩, -9, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-931411923/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((729055797006347/18014398509481984), (1220104644688299/18014398509481984)), (93117299/9007199254740992), by norm_num⟩
  | 1 => ⟨((-127950925/1073741824), (-428262195/2147483648)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((376743691/2147483648), (315247975/1073741824)), (49/1073741824), by norm_num⟩
  | 3 => ⟨((-739532539/4294967296), (-1237637901/4294967296)), (195/4294967296), by norm_num⟩
  | 4 => ⟨((544377109/4294967296), (911037319/4294967296)), (73/2147483648), by norm_num⟩
  | 5 => ⟨((-80144259/1073741824), (-1072997517/8589934592)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((9832495/268435456), (526562619/8589934592)), (173/17179869184), by norm_num⟩
  | 7 => ⟨((-264696517/17179869184), (-885960857/34359738368)), (147/34359738368), by norm_num⟩
  | 8 => ⟨((389691371/68719476736), (1304328841/137438953472)), (219/137438953472), by norm_num⟩
  | 9 => ⟨((-509965539/274877906944), (-853448151/274877906944)), (145/274877906944), by norm_num⟩
  | 10 => ⟨((150156241/274877906944), (1005170401/1099511627776)), (173/1099511627776), by norm_num⟩
  | 11 => ⟨((-321546101/2199023255552), (-538120529/2199023255552)), (187/4398046511104), by norm_num⟩
  | 12 => ⟨((157795479/4398046511104), (1056308707/17592186044416)), (93/8796093022208), by norm_num⟩
  | 13 => ⟨((-571838965/70368744177664), (-59812241/4398046511104)), (85/35184372088832), by norm_num⟩
  | 14 => ⟨((240534991/140737488355328), (805090257/281474976710656)), (145/281474976710656), by norm_num⟩
  | 15 => ⟨((-188864161/562949953421312), (-632143769/1125899906842624)), (115/1125899906842624), by norm_num⟩
  | 16 => ⟨((556098997/9007199254740992), (930654377/9007199254740992)), (171/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1344543963135/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111128202272525/39614081257132168796771975168), (794988432117/316912650057057350374175801344)), (92357/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888934762576305/39614081257132168796771975168), (1788330597469/39614081257132168796771975168)), (12989/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944329782571823/1237940039285380274899124224), (1899609150085/2475880078570760549798248448)), (55209/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442581502086995/38685626227668133590597632), (949527887087/77371252455336267181195264)), (110431/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774371497263579/4835703278458516698824704), (889888521065/4835703278458516698824704)), (103543/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314519940582113/151115727451828646838272), (1556717408487/604462909807314587353088)), (90615/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943320216720889/37778931862957161709568), (632141183909/18889465931478580854784)), (73637/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296676081548729/4722366482869645213696), (236932580703/590295810358705651712)), (110479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620261525203637/590295810358705651712), (325586828893/73786976294838206464)), (151945/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821992200575927/73786976294838206464), (3253524343115/73786976294838206464)), (189987/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820990285291451/9223372036854775808), (1828497351567/4611686018427387904)), (213813/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592240174723473/1152921504606846976), (3652973584789/1152921504606846976)), (213909/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193054842689669/144115188075855872), (398979221767/18014398509481984)), (11705/9007199254740992), by norm_num⟩
  | 4 => ⟨((1489351629114779/36028797018963968), (597341066509/4503599627370496)), (281137/36028797018963968), by norm_num⟩
  | 3 => ⟨((371601474699209/2251799813685248), (2978826802837/4503599627370496)), (351803/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222260797494907/4503599627370496), (5934081226391/2251799813685248)), (352377/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207613437030553/2251799813685248), (17684823144037/2251799813685248)), (530007/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163914470045757/2251799813685248), (34902603474133/2251799813685248)), (1065815/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163914470045757/2251799813685248), (34902603474133/2251799813685248)), (4065761570457076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((64966194118001/70368744177664), (16770196054049/562949953421312)), (4162951/2251799813685248), by norm_num⟩
  | 2 => ⟨((1917311242946249/2251799813685248), (30965333401249/562949953421312)), (3967355/1125899906842624), by norm_num⟩
  | 3 => ⟨((203211934633223/281474976710656), (210925257248795/2251799813685248)), (7192519/1125899906842624), by norm_num⟩
  | 4 => ⟨((1153919768629075/2251799813685248), (304556590354379/2251799813685248)), (11732775/1125899906842624), by norm_num⟩
  | 5 => ⟨((550127106404427/2251799813685248), (312135979531001/2251799813685248)), (60793949/4503599627370496), by norm_num⟩
  | 6 => ⟨((729055797006347/18014398509481984), (1220104644688299/18014398509481984)), (93117299/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-931411923/16777216)), (1/16777216), by norm_num⟩, -9, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-59227343/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1356941935425751/18014398509481984), (88423653300319/18014398509481984)), (89964647/18014398509481984), by norm_num⟩
  | 1 => ⟨((-969179809/4294967296), (-31577777/2147483648)), (131/8589934592), by norm_num⟩
  | 2 => ⟨((1451701617/4294967296), (47299283/2147483648)), (25/1073741824), by norm_num⟩
  | 3 => ⟨((-724818231/2147483648), (-11807999/536870912)), (51/2147483648), by norm_num⟩
  | 4 => ⟨((271420171/1073741824), (70747207/4294967296)), (39/2147483648), by norm_num⟩
  | 5 => ⟨((-650481733/4294967296), (-84775877/8589934592)), (3/268435456), by norm_num⟩
  | 6 => ⟨((1299112747/17179869184), (84655277/17179869184)), (49/8589934592), by norm_num⟩
  | 7 => ⟨((-555970569/17179869184), (-36229221/17179869184)), (43/17179869184), by norm_num⟩
  | 8 => ⟨((1665538977/137438953472), (108533047/137438953472)), (131/137438953472), by norm_num⟩
  | 9 => ⟨((-277194937/68719476736), (-36126217/137438953472)), (89/274877906944), by norm_num⟩
  | 10 => ⟨((664321455/549755813888), (86579579/1099511627776)), (109/1099511627776), by norm_num⟩
  | 11 => ⟨((-361841677/1099511627776), (-94316087/4398046511104)), (121/4398046511104), by norm_num⟩
  | 12 => ⟨((180663465/2199023255552), (94181915/17592186044416)), (123/17592186044416), by norm_num⟩
  | 13 => ⟨((-666116151/35184372088832), (-43406739/35184372088832)), (115/70368744177664), by norm_num⟩
  | 14 => ⟨((71268059/17592186044416), (74305697/281474976710656)), (25/70368744177664), by norm_num⟩
  | 15 => ⟨((-1821866875/2251799813685248), (-59359993/1125899906842624)), (81/1125899906842624), by norm_num⟩
  | 16 => ⟨((1364456349/9007199254740992), (88913323/9007199254740992)), (123/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (84763436601/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888992220583773/316912650057057350374175801344), (100228820445/633825300114114700748351602688)), (46105/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888859709249753/39614081257132168796771975168), (112732306653/39614081257132168796771975168)), (51869/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944289970617039/1237940039285380274899124224), (29936631215/618970019642690137449562112)), (55111/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885123259791819/77371252455336267181195264), (119711047797/154742504910672534362390528)), (110223/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387167154325141/2417851639229258349412352), (112191427807/9671406556917033397649408)), (103335/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629007412815243/302231454903657293676544), (98129836571/604462909807314587353088)), (90419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886535179892783/75557863725914323419136), (159390402315/75557863725914323419136)), (36733/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648298688077867/2361183241434822606848), (119481077927/4722366482869645213696)), (110201/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202519210791467/73786976294838206464), (82093123777/295147905179352825856)), (151529/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821857972754531/73786976294838206464), (205082573997/73786976294838206464)), (189415/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820840062505971/9223372036854775808), (115255755535/4611686018427387904)), (213097/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398022732348291/288230376151711744), (230253813523/1152921504606846976)), (13319/72057594037927936), by norm_num⟩
  | 5 => ⟨((298231337501031/36028797018963968), (100591283077/72057594037927936)), (93237/72057594037927936), by norm_num⟩
  | 4 => ⟨((23268118397039/562949953421312), (150597889551/18014398509481984)), (279727/36028797018963968), by norm_num⟩
  | 3 => ⟨((92885602943545/562949953421312), (46935660313/1125899906842624)), (43711/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110899836761937/2251799813685248), (747950946781/4503599627370496)), (87433/562949953421312), by norm_num⟩
  | 1 => ⟨((2206949992715395/2251799813685248), (1114407757597/2251799813685248)), (524715/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162699313038135/2251799813685248), (2198922463725/2251799813685248)), (131241/140737488355328), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162699313038135/2251799813685248), (2198922463725/2251799813685248)), (500644684374761537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2077122244583949/2251799813685248), (4223828488501/2251799813685248)), (2018819/1125899906842624), by norm_num⟩
  | 2 => ⟨((1915986914999107/2251799813685248), (3896175875605/1125899906842624)), (3732003/1125899906842624), by norm_num⟩
  | 3 => ⟨((815113562802501/1125899906842624), (13260542879213/2251799813685248)), (3188361/562949953421312), by norm_num⟩
  | 4 => ⟨((1180151371765035/2251799813685248), (19200371694287/2251799813685248)), (9308167/1125899906842624), by norm_num⟩
  | 5 => ⟨((1236689511690599/4503599627370496), (2515692653461/281474976710656)), (39661667/4503599627370496), by norm_num⟩
  | 6 => ⟨((1356941935425751/18014398509481984), (88423653300319/18014398509481984)), (89964647/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-59227343/1048576)), (1/16777216), by norm_num⟩, -9, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-120383905/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((427856673634817/9007199254740992), (-245917570959993/4503599627370496)), (38932881/4503599627370496), by norm_num⟩
  | 1 => ⟨((-310568629/2147483648), (714017451/4294967296)), (115/4294967296), by norm_num⟩
  | 2 => ⟨((118191645/536870912), (-1086921075/4294967296)), (89/2147483648), by norm_num⟩
  | 3 => ⟨((-959565641/4294967296), (1103051867/4294967296)), (183/4294967296), by norm_num⟩
  | 4 => ⟨((730354781/4294967296), (-209891635/1073741824)), (141/4294967296), by norm_num⟩
  | 5 => ⟨((-889432607/8589934592), (255607917/2147483648)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((451316255/8589934592), (-1037605385/17179869184)), (179/17179869184), by norm_num⟩
  | 7 => ⟨((-785167123/34359738368), (225643777/8589934592)), (79/17179869184), by norm_num⟩
  | 8 => ⟨((597614731/68719476736), (-343488771/34359738368)), (61/34359738368), by norm_num⟩
  | 9 => ⟨((-202161273/68719476736), (232390949/68719476736)), (167/274877906944), by norm_num⟩
  | 10 => ⟨((984775251/1099511627776), (-566015567/549755813888)), (205/1099511627776), by norm_num⟩
  | 11 => ⟨((-272560941/1099511627776), (626635307/2199023255552)), (115/2199023255552), by norm_num⟩
  | 12 => ⟨((276605967/4398046511104), (-158983771/2199023255552)), (59/4398046511104), by norm_num⟩
  | 13 => ⟨((-518235737/35184372088832), (297864405/17592186044416)), (7/2199023255552), by norm_num⟩
  | 14 => ⟨((112698595/35184372088832), (-129550695/35184372088832)), (197/281474976710656), by norm_num⟩
  | 15 => ⟨((-91496907/140737488355328), (841429329/1125899906842624)), (81/562949953421312), by norm_num⟩
  | 16 => ⟨((557128773/4503599627370496), (-320218809/2251799813685248)), (125/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-556769689399/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777918702003517/633825300114114700748351602688), (-658308494717/316912650057057350374175801344)), (46165/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944392859201767/19807040628566084398385987584), (-740429182891/19807040628566084398385987584)), (12985/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944250639393929/1237940039285380274899124224), (-1572990730463/2475880078570760549798248448)), (55191/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((27658871939787/2417851639229258349412352), (-393129253897/38685626227668133590597632)), (110393/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548594765330363/9671406556917033397649408), (-368432893733/2417851639229258349412352)), (103505/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628975074485509/302231454903657293676544), (-1289012220201/604462909807314587353088)), (90579/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471607493776339/18889465931478580854784), (-2093702371399/75557863725914323419136)), (36803/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648259190316663/2361183241434822606848), (-1569452568481/4722366482869645213696)), (27607/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620044918346381/590295810358705651712), (-1078329406333/295147905179352825856)), (151869/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455430447372959/18446744073709551616), (-2693817337879/73786976294838206464)), (189883/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820686550025179/9223372036854775808), (-3027788487355/9223372036854775808)), (106841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591937035074497/1152921504606846976), (-756086794233/288230376151711744)), (106881/576460752303423488), by norm_num⟩
  | 5 => ⟨((298197566087141/36028797018963968), (-2642437403407/144115188075855872)), (46783/36028797018963968), by norm_num⟩
  | 4 => ⟨((372239024066883/9007199254740992), (-3955936079239/36028797018963968)), (280879/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485913811576787/9007199254740992), (-2465719320533/4503599627370496)), (43927/1125899906842624), by norm_num⟩
  | 2 => ⟨((555320895587013/1125899906842624), (-9822547016097/4503599627370496)), (351893/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206164917579175/2251799813685248), (-3658348288317/562949953421312)), (1058079/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080543038489133/1125899906842624), (-14433728971097/1125899906842624)), (1062913/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080543038489133/1125899906842624), (-14433728971097/1125899906842624)), (4054691318992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1036828334739785/1125899906842624), (-27704532639841/1125899906842624)), (129215/70368744177664), by norm_num⟩
  | 2 => ⟨((1908243260456437/2251799813685248), (-102051147769481/2251799813685248)), (3909509/1125899906842624), by norm_num⟩
  | 3 => ⟨((806239054255441/1125899906842624), (-10810153602989/140737488355328)), (6980429/1125899906842624), by norm_num⟩
  | 4 => ⟨((1141384604018139/2251799813685248), (-247711341706631/2251799813685248)), (22138987/2251799813685248), by norm_num⟩
  | 5 => ⟨((1102582829907867/4503599627370496), (-502236317715843/4503599627370496)), (27314309/2251799813685248), by norm_num⟩
  | 6 => ⟨((427856673634817/9007199254740992), (-245917570959993/4503599627370496)), (38932881/4503599627370496), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-120383905/2097152)), (1/16777216), by norm_num⟩, -9, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile009Terms2
