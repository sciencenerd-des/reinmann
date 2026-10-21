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
namespace Reinmann.XiBand58.Tile008Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2991/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2991/160))
  have he : value ((15/16), (2991/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/8388608), (-1739128909/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((4149555817295/9007199254740992), (-1338902449893271/18014398509481984)), (216761229/18014398509481984), by norm_num⟩
  | 1 => ⟨((-5486017/4294967296), (1770127217/8589934592)), (289/8589934592), by norm_num⟩
  | 2 => ⟨((3802617/2147483648), (-613479345/2147483648)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-7028729/4294967296), (1133950609/4294967296)), (47/1073741824), by norm_num⟩
  | 4 => ⟨((9743887/8589934592), (-1571989335/8589934592)), (263/8589934592), by norm_num⟩
  | 5 => ⟨((-2701579/4294967296), (1743391961/17179869184)), (147/8589934592), by norm_num⟩
  | 6 => ⟨((9987157/34359738368), (-1611236297/34359738368)), (137/17179869184), by norm_num⟩
  | 7 => ⟨((-1977877/17179869184), (1276370167/68719476736)), (219/68719476736), by norm_num⟩
  | 8 => ⟨((10967679/274877906944), (-1769424765/274877906944)), (153/137438953472), by norm_num⟩
  | 9 => ⟨((-6757525/549755813888), (136274643/68719476736)), (95/274877906944), by norm_num⟩
  | 10 => ⟨((7494335/2199023255552), (-1209067323/2199023255552)), (53/549755813888), by norm_num⟩
  | 11 => ⟨((-3777947/4398046511104), (304749675/2199023255552)), (215/8796093022208), by norm_num⟩
  | 12 => ⟨((6983129/35184372088832), (-35206063/1099511627776)), (25/4398046511104), by norm_num⟩
  | 13 => ⟨((-5957337/140737488355328), (30034441/4398046511104)), (43/35184372088832), by norm_num⟩
  | 14 => ⟨((4719213/562949953421312), (-95169317/70368744177664)), (275/1125899906842624), by norm_num⟩
  | 15 => ⟨((-3489183/2251799813685248), (17591025/70368744177664)), (205/4503599627370496), by norm_num⟩
  | 16 => ⟨((9674069/36028797018963968), (-1560725681/36028797018963968)), (143/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (-2038063534221/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444489371241969/158456325028528675187087900672), (-1204926842109/316912650057057350374175801344)), (46219/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944414609450755/19807040628566084398385987584), (-1355236680063/19807040628566084398385987584)), (13001/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944273662448119/1237940039285380274899124224), (-359889283259/309485009821345068724781056)), (55263/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770213655647071/154742504910672534362390528), (-2878255477577/154742504910672534362390528)), (55273/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387159386124865/2417851639229258349412352), (-2697452366705/9671406556917033397649408)), (51829/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257987374308891/604462909807314587353088), (-589839759125/151115727451828646838272)), (45361/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886490079591005/75557863725914323419136), (-958062400385/18889465931478580854784)), (73731/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648281560511151/2361183241434822606848), (-2872692735063/4722366482869645213696)), (13829/590295810358705651712), by norm_num⟩
  | 9 => ⟨((101256617992363/36893488147419103232), (-3947525432455/590295810358705651712)), (152175/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455449294971467/18446744073709551616), (-2465384336387/36893488147419103232)), (190303/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820770236632339/9223372036854775808), (-5542116404105/9223372036854775808)), (3347/144115188075855872), by norm_num⟩
  | 6 => ⟨((398004828800267/288230376151711744), (-2767937273671/576460752303423488)), (107177/576460752303423488), by norm_num⟩
  | 5 => ⟨((596430340644787/72057594037927936), (-1209219124587/36028797018963968)), (46931/36028797018963968), by norm_num⟩
  | 4 => ⟨((744529287810569/18014398509481984), (-452581759977/2251799813685248)), (281915/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486036428244059/9007199254740992), (-9027170573903/9007199254740992)), (352971/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221512460130757/4503599627370496), (-17981134575495/4503599627370496)), (176919/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103233833088411/1125899906842624), (-26789339613721/2251799813685248)), (1065867/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161531216517927/2251799813685248), (-26426572126555/1125899906842624)), (1074615/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2161531216517927/2251799813685248), (-26426572126555/1125899906842624)), (4099330906394576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1036820350713625/1125899906842624), (-50734403875473/1125899906842624)), (4227039/2251799813685248), by norm_num⟩
  | 2 => ⟨((1905004971400581/2251799813685248), (-46720371944011/562949953421312)), (2041539/562949953421312), by norm_num⟩
  | 3 => ⟨((49878424315635/70368744177664), (-316200544215751/2251799813685248)), (15172461/2251799813685248), by norm_num⟩
  | 4 => ⟨((271736300254815/562949953421312), (-112063850915177/562949953421312)), (12885005/1125899906842624), by norm_num⟩
  | 5 => ⟨((435437003391115/2251799813685248), (-865492672801263/4503599627370496)), (35138235/2251799813685248), by norm_num⟩
  | 6 => ⟨((4149555817295/9007199254740992), (-1338902449893271/18014398509481984)), (216761229/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-1739128909/33554432)), (1/16777216), by norm_num⟩, -8, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-888578099/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1142469411160815/18014398509481984), (-543015828639933/18014398509481984)), (113920721/9007199254740992), by norm_num⟩
  | 1 => ⟨((385863731/2147483648), (183401071/2147483648)), (155/4294967296), by norm_num⟩
  | 2 => ⟨((-34163571/134217728), (-259807181/2147483648)), (111/2147483648), by norm_num⟩
  | 3 => ⟨((1032455309/4294967296), (490726115/4294967296)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((-182822885/1073741824), (-10861967/134217728)), (19/536870912), by norm_num⟩
  | 5 => ⟨((207190495/2147483648), (196955327/4294967296)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((-195671625/4294967296), (-186005487/8589934592)), (83/8589934592), by norm_num⟩
  | 7 => ⟨((1267153049/68719476736), (602277975/68719476736)), (271/68719476736), by norm_num⟩
  | 8 => ⟨((-224382183/34359738368), (-426595499/137438953472)), (193/137438953472), by norm_num⟩
  | 9 => ⟨((565086751/274877906944), (268585791/274877906944)), (245/549755813888), by norm_num⟩
  | 10 => ⟨((-1280809059/2199023255552), (-304384339/1099511627776)), (35/274877906944), by norm_num⟩
  | 11 => ⟨((659782785/4398046511104), (156797413/2199023255552)), (291/8796093022208), by norm_num⟩
  | 12 => ⟨((-623101797/17592186044416), (-592320697/35184372088832)), (277/35184372088832), by norm_num⟩
  | 13 => ⟨((1086387893/140737488355328), (258180139/70368744177664)), (243/140737488355328), by norm_num⟩
  | 14 => ⟨((-439709811/281474976710656), (-417988237/562949953421312)), (199/562949953421312), by norm_num⟩
  | 15 => ⟨((332211121/1125899906842624), (39474995/281474976710656)), (303/4503599627370496), by norm_num⟩
  | 16 => ⟨((-941224981/18014398509481984), (-223682165/9007199254740992)), (217/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (-1757157653005/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777863803729967/633825300114114700748351602688), (-4155017971477/633825300114114700748351602688)), (46305/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944361757033127/19807040628566084398385987584), (-4673302292911/39614081257132168796771975168)), (26053/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472108647825047/618970019642690137449562112), (-4964036395849/2475880078570760549798248448)), (27689/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442525111903085/38685626227668133590597632), (-4962521049819/154742504910672534362390528)), (55395/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548530908305901/9671406556917033397649408), (-4650753861559/9671406556917033397649408)), (51951/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78618347778903/37778931862957161709568), (-4067800492149/604462909807314587353088)), (90951/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235792087020147/9444732965739290427392), (-3303579850513/37778931862957161709568)), (18483/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324111814962791/1180591620717411303424), (-4952731722041/4722366482869645213696)), (55479/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619945242343395/590295810358705651712), (-6805721216755/590295810358705651712)), (19083/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910797185847683/36893488147419103232), (-531295472369/4611686018427387904)), (373/144115188075855872), by norm_num⟩
  | 7 => ⟨((910269665564191/4611686018427387904), (-9554491059987/9223372036854775808)), (215049/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397946246253685/288230376151711744), (-9543465016713/1152921504606846976)), (53825/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192651800839111/144115188075855872), (-8338138948901/144115188075855872)), (188671/144115188075855872), by norm_num⟩
  | 4 => ⟨((744368799947885/18014398509481984), (-3120612734483/9007199254740992)), (141787/18014398509481984), by norm_num⟩
  | 3 => ⟨((742810937584267/4503599627370496), (-3889950491711/2251799813685248)), (177731/4503599627370496), by norm_num⟩
  | 2 => ⟨((555160901175943/1125899906842624), (-30990074405521/4503599627370496)), (89239/562949953421312), by norm_num⟩
  | 1 => ⟨((137816617823045/140737488355328), (-46162182398165/2251799813685248)), (539181/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079169445064907/1125899906842624), (-45519007972351/1125899906842624)), (2186833/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1079169445064907/1125899906842624), (-45519007972351/1125899906842624)), (8342105874068450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065076485058115/2251799813685248), (-174518968426537/2251799813685248)), (4368961/2251799813685248), by norm_num⟩
  | 2 => ⟨((940155513173683/1125899906842624), (-320095077461105/2251799813685248)), (8690565/2251799813685248), by norm_num⟩
  | 3 => ⟨((1524606528663887/2251799813685248), (-534575320569557/2251799813685248)), (16984435/2251799813685248), by norm_num⟩
  | 4 => ⟨((452672187263859/1125899906842624), (-90485066528749/281474976710656)), (31063189/2251799813685248), by norm_num⟩
  | 5 => ⟨((131292937209885/2251799813685248), (-1164155292493791/4503599627370496)), (89899505/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1142469411160815/18014398509481984), (-543015828639933/18014398509481984)), (113920721/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-888578099/16777216)), (1/16777216), by norm_num⟩, -8, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-14164135/262144)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-486218870491875/9007199254740992), (350660335756123/9007199254740992)), (219646891/18014398509481984), by norm_num⟩
  | 1 => ⟨((335062335/2147483648), (-1887863/16777216)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((-484227355/2147483648), (698448115/4294967296)), (223/4294967296), by norm_num⟩
  | 3 => ⟨((466532357/2147483648), (-336462451/2147483648)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((-674225975/4294967296), (486250783/4294967296)), (159/4294967296), by norm_num⟩
  | 5 => ⟨((779505487/8589934592), (-140544553/2147483648)), (93/4294967296), by norm_num⟩
  | 6 => ⟨((-751020215/17179869184), (135408669/4294967296)), (181/17179869184), by norm_num⟩
  | 7 => ⟨((1240415783/68719476736), (-894586041/68719476736)), (151/34359738368), by norm_num⟩
  | 8 => ⟨((-896315687/137438953472), (646421557/137438953472)), (55/34359738368), by norm_num⟩
  | 9 => ⟨((1151415799/549755813888), (-830399383/549755813888)), (285/549755813888), by norm_num⟩
  | 10 => ⟨((-332801971/549755813888), (480032585/1099511627776)), (83/549755813888), by norm_num⟩
  | 11 => ⟨((699579213/4398046511104), (-504535501/4398046511104)), (11/274877906944), by norm_num⟩
  | 12 => ⟨((-674014667/17592186044416), (121524597/4398046511104)), (171/17592186044416), by norm_num⟩
  | 13 => ⟨((1198863359/140737488355328), (-432309247/70368744177664)), (153/70368744177664), by norm_num⟩
  | 14 => ⟨((-990045941/562949953421312), (714019679/562949953421312)), (255/562949953421312), by norm_num⟩
  | 15 => ⟨((381546777/1125899906842624), (-550341951/2251799813685248)), (99/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1102812029/18014398509481984), (49709151/1125899906842624)), (9/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (1639193937513/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777782481318255/633825300114114700748351602688), (484466870909/79228162514264337593543950336)), (46291/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888632114782445/39614081257132168796771975168), (4359166489863/39614081257132168796771975168)), (26045/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888337594712655/2475880078570760549798248448), (4630332753007/2475880078570760549798248448)), (110719/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885001790236397/77371252455336267181195264), (4628891319379/154742504910672534362390528)), (3461/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774220116406631/4835703278458516698824704), (4338054543491/9671406556917033397649408)), (103863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78613397547399/37778931862957161709568), (3794267168281/604462909807314587353088)), (90915/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886208247467431/75557863725914323419136), (1540703859913/18889465931478580854784)), (147799/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648175574140505/2361183241434822606848), (2309801272741/2361183241434822606848)), (55453/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619813454085765/590295810358705651712), (6347878355229/590295810358705651712)), (76293/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821430183413565/73786976294838206464), (3964369394495/36893488147419103232)), (190869/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820355370376475/9223372036854775808), (8911436836845/9223372036854775808)), (214915/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795800980711389/576460752303423488), (8900952640079/1152921504606846976)), (107575/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192492707205043/144115188075855872), (3888275384721/72057594037927936)), (23565/18014398509481984), by norm_num⟩
  | 4 => ⟨((186062632216125/4503599627370496), (2910322597555/9007199254740992)), (141655/18014398509481984), by norm_num⟩
  | 3 => ⟨((742664928287801/4503599627370496), (906905778967/562949953421312)), (44383/1125899906842624), by norm_num⟩
  | 2 => ⟨((2220070493427677/4503599627370496), (28897891471729/4503599627370496)), (178229/1125899906842624), by norm_num⟩
  | 1 => ⟨((2204233353411777/2251799813685248), (10760010344787/562949953421312)), (67273/140737488355328), by norm_num⟩
  | 0 => ⟨((1078390646419907/1125899906842624), (84858521431791/2251799813685248)), (1090419/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1078390646419907/1125899906842624), (84858521431791/2251799813685248)), (4159618381980514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((257821795939483/281474976710656), (162555543747563/2251799813685248)), (4341997/2251799813685248), by norm_num⟩
  | 2 => ⟨((938757675312907/1125899906842624), (297791034348307/2251799813685248)), (8581143/2251799813685248), by norm_num⟩
  | 3 => ⟨((1526061229249959/2251799813685248), (248293491663747/1125899906842624)), (8289643/1125899906842624), by norm_num⟩
  | 4 => ⟨((462355541277403/1125899906842624), (673081272678541/2251799813685248)), (29784233/2251799813685248), by norm_num⟩
  | 5 => ⟨((178547037851969/2251799813685248), (552807321968221/2251799813685248)), (84535083/4503599627370496), by norm_num⟩
  | 6 => ⟨((-486218870491875/9007199254740992), (350660335756123/9007199254740992)), (219646891/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-14164135/262144)), (1/16777216), by norm_num⟩, -9, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-923461693/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((73726275009723/18014398509481984), (35540839461115/562949953421312)), (181656983/18014398509481984), by norm_num⟩
  | 1 => ⟨((-103513011/8589934592), (-798399605/4294967296)), (257/8589934592), by norm_num⟩
  | 2 => ⟨((9524617/536870912), (1175419459/4294967296)), (191/4294967296), by norm_num⟩
  | 3 => ⟨((-74785743/4294967296), (-1153650291/4294967296)), (189/4294967296), by norm_num⟩
  | 4 => ⟨((27525257/2147483648), (849213221/4294967296)), (281/8589934592), by norm_num⟩
  | 5 => ⟨((-129674303/17179869184), (-250045651/2147483648)), (167/8589934592), by norm_num⟩
  | 6 => ⟨((127272691/34359738368), (490829441/8589934592)), (165/17179869184), by norm_num⟩
  | 7 => ⟨((-53535239/34359738368), (-825838479/34359738368)), (35/8589934592), by norm_num⟩
  | 8 => ⟨((39407811/68719476736), (75988469/8589934592)), (13/8589934592), by norm_num⟩
  | 9 => ⟨((-12892655/68719476736), (-1591064249/549755813888)), (137/274877906944), by norm_num⟩
  | 10 => ⟨((121477235/2199023255552), (1873916637/2199023255552)), (325/2199023255552), by norm_num⟩
  | 11 => ⟨((-130066293/8796093022208), (-2006412069/8796093022208)), (175/4398046511104), by norm_num⟩
  | 12 => ⟨((127657421/35184372088832), (1969252635/35184372088832)), (173/17592186044416), by norm_num⟩
  | 13 => ⟨((-115655227/140737488355328), (-1784105913/140737488355328)), (79/35184372088832), by norm_num⟩
  | 14 => ⟨((48648537/281474976710656), (46903491/17592186044416)), (67/140737488355328), by norm_num⟩
  | 15 => ⟨((-76396079/2251799813685248), (-1178491453/2251799813685248)), (53/562949953421312), by norm_num⟩
  | 16 => ⟨((28117949/4503599627370496), (1734998085/18014398509481984)), (315/18014398509481984), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (490453343299/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888854799734141/316912650057057350374175801344), (2319076403607/633825300114114700748351602688)), (92429/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888550425965259/39614081257132168796771975168), (2608338418069/39614081257132168796771975168)), (103997/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944125602659413/1237940039285380274899124224), (692644816713/618970019642690137449562112)), (55257/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769917646181961/154742504910672534362390528), (1384850914563/77371252455336267181195264)), (110533/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774180076288447/4835703278458516698824704), (2595663541923/9671406556917033397649408)), (51823/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314436193319721/151115727451828646838272), (8868258107/2361183241434822606848)), (45355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943048036002703/37778931862957161709568), (1843724806551/37778931862957161709568)), (73721/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296267806931743/4722366482869645213696), (1382030258811/2361183241434822606848)), (110615/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619700142157087/590295810358705651712), (949525981163/147573952589676412928)), (76075/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821290464126319/73786976294838206464), (1185978437997/18446744073709551616)), (190269/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820200822139795/9223372036854775808), (2665898884211/4611686018427387904)), (214165/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99465668800215/72057594037927936), (5325423022797/1152921504606846976)), (107153/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192364042663081/144115188075855872), (4652582838313/144115188075855872)), (46919/36028797018963968), by norm_num⟩
  | 4 => ⟨((372078853197049/9007199254740992), (6964572821267/36028797018963968)), (281831/36028797018963968), by norm_num⟩
  | 3 => ⟨((742555304882499/4503599627370496), (2170185145891/2251799813685248)), (352845/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219670202891715/4503599627370496), (17286762729507/4503599627370496)), (707363/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101863820311985/1125899906842624), (12872036934155/1125899906842624)), (1065243/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156144073832305/2251799813685248), (12687052012831/562949953421312)), (536843/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2156144073832305/2251799813685248), (12687052012831/562949953421312)), (2047893526317405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2063408060638205/2251799813685248), (97184880629683/2251799813685248)), (526137/281474976710656), by norm_num⟩
  | 2 => ⟨((1886583300107475/2251799813685248), (44527063383859/562949953421312)), (4038611/1125899906842624), by norm_num⟩
  | 3 => ⟨((1566513140657019/2251799813685248), (4663159535335/35184372088832)), (462879/70368744177664), by norm_num⟩
  | 4 => ⟨((32819520254043/70368744177664), (415235529606113/2251799813685248)), (6133751/562949953421312), by norm_num⟩
  | 5 => ⟨((413247776661053/2251799813685248), (96831562317633/562949953421312)), (63869039/4503599627370496), by norm_num⟩
  | 6 => ⟨((73726275009723/18014398509481984), (35540839461115/562949953421312)), (181656983/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-923461693/16777216)), (1/16777216), by norm_num⟩, -9, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-469774381/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((14493554497129/281474976710656), (565138187302745/18014398509481984)), (53586309/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1325036895/8589934592), (-100910825/1073741824)), (155/8589934592), by norm_num⟩
  | 2 => ⟨((248090987/1073741824), (302301815/2147483648)), (59/2147483648), by norm_num⟩
  | 3 => ⟨((-990952235/4294967296), (-37733971/268435456)), (15/536870912), by norm_num⟩
  | 4 => ⟨((371078449/2147483648), (452163499/4294967296)), (91/4294967296), by norm_num⟩
  | 5 => ⟨((-889321349/8589934592), (-541824315/8589934592)), (111/8589934592), by norm_num⟩
  | 6 => ⟨((444028111/8589934592), (541053529/17179869184)), (113/17179869184), by norm_num⟩
  | 7 => ⟨((-190027049/8589934592), (-231550217/17179869184)), (49/17179869184), by norm_num⟩
  | 8 => ⟨((1138540327/137438953472), (346831229/68719476736)), (149/137438953472), by norm_num⟩
  | 9 => ⟨((-94743389/34359738368), (-461783781/274877906944)), (101/274877906944), by norm_num⟩
  | 10 => ⟨((454121325/549755813888), (553352231/1099511627776)), (123/1099511627776), by norm_num⟩
  | 11 => ⟨((-494700331/2199023255552), (-75349779/549755813888)), (17/549755813888), by norm_num⟩
  | 12 => ⟨((987993165/17592186044416), (300970353/8796093022208)), (137/17592186044416), by norm_num⟩
  | 13 => ⟨((-910696311/70368744177664), (-277423569/35184372088832)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((194871595/70368744177664), (118726677/70368744177664)), (111/281474976710656), by norm_num⟩
  | 15 => ⟨((-1245404003/2251799813685248), (-189692447/562949953421312)), (179/2251799813685248), by norm_num⟩
  | 16 => ⟨((932724241/9007199254740992), (284133893/4503599627370496)), (17/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (356392956099/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777638060415949/633825300114114700748351602688), (842523390799/633825300114114700748351602688)), (92283/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888470100761957/39614081257132168796771975168), (236902582227/9903520314283042199192993792)), (103825/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888166068360855/2475880078570760549798248448), (1006547716693/2475880078570760549798248448)), (6895/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769832743595953/154742504910672534362390528), (1006223604015/154742504910672534362390528)), (110327/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774140402612645/4835703278458516698824704), (471495202453/4835703278458516698824704)), (103439/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257675592946647/604462909807314587353088), (824772544627/604462909807314587353088)), (90517/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942992059809577/37778931862957161709568), (669805310929/37778931862957161709568)), (147103/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296184249617251/4722366482869645213696), (502072073561/2361183241434822606848)), (27585/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619585911300739/590295810358705651712), (1379782648937/590295810358705651712)), (18967/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821148664687933/73786976294838206464), (1723356122891/73786976294838206464)), (189701/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113752665957597/576460752303423488), (121055670811/576460752303423488)), (213455/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24863972299507/18014398509481984), (1934537378751/1152921504606846976)), (106753/576460752303423488), by norm_num⟩
  | 5 => ⟨((596114513955491/72057594037927936), (1690076496849/144115188075855872)), (46719/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488116677163511/36028797018963968), (2529836846227/36028797018963968)), (17527/2251799813685248), by norm_num⟩
  | 3 => ⟨((1484868787771559/9007199254740992), (3153081113983/9007199254740992)), (350745/9007199254740992), by norm_num⟩
  | 2 => ⟨((554801559131533/1125899906842624), (6278602711975/4503599627370496)), (351055/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203080484381977/2251799813685248), (9349302971805/2251799813685248)), (527365/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155042543816645/2251799813685248), (2303247557787/281474976710656)), (2115789/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2155042543816645/2251799813685248), (2303247557787/281474976710656)), (8071094521529387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062292047756973/2251799813685248), (35268474192469/2251799813685248)), (4084379/2251799813685248), by norm_num⟩
  | 2 => ⟨((1888180556339673/2251799813685248), (32300337455227/1125899906842624)), (475577/140737488355328), by norm_num⟩
  | 3 => ⟨((1581425020331789/2251799813685248), (108337994835085/2251799813685248)), (1649699/281474976710656), by norm_num⟩
  | 4 => ⟨((1105412638671815/2251799813685248), (76085100746317/1125899906842624)), (19807093/2251799813685248), by norm_num⟩
  | 5 => ⟨((66545731786831/281474976710656), (74700629663835/1125899906842624)), (44247381/4503599627370496), by norm_num⟩
  | 6 => ⟨((14493554497129/281474976710656), (565138187302745/18014398509481984)), (53586309/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-469774381/8388608)), (1/16777216), by norm_num⟩, -9, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-119356347/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((969314197939485/18014398509481984), (-370255878949291/18014398509481984)), (89482867/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1407193577/8589934592), (268757899/4294967296)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((1071058105/4294967296), (-409119727/4294967296)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((-543476739/2147483648), (103797849/1073741824)), (105/4294967296), by norm_num⟩
  | 4 => ⟨((827313563/4294967296), (-9875465/134217728)), (41/2147483648), by norm_num⟩
  | 5 => ⟨((-503754941/4294967296), (384845757/8589934592)), (51/4294967296), by norm_num⟩
  | 6 => ⟨((1022462147/17179869184), (-390557181/17179869184)), (53/8589934592), by norm_num⟩
  | 7 => ⟨((-889402557/34359738368), (339731457/34359738368)), (47/17179869184), by norm_num⟩
  | 8 => ⟨((1353903021/137438953472), (-258580011/68719476736)), (145/137438953472), by norm_num⟩
  | 9 => ⟨((-915997361/274877906944), (349890065/274877906944)), (25/68719476736), by norm_num⟩
  | 10 => ⟨((69719363/68719476736), (-213049631/549755813888)), (31/274877906944), by norm_num⟩
  | 11 => ⟨((-1234979869/4398046511104), (29483381/274877906944)), (139/4398046511104), by norm_num⟩
  | 12 => ⟨((626653987/8796093022208), (-478735013/17592186044416)), (143/17592186044416), by norm_num⟩
  | 13 => ⟨((-146758625/8796093022208), (448467535/70368744177664)), (17/8796093022208), by norm_num⟩
  | 14 => ⟨((1021279833/281474976710656), (-97526391/70368744177664)), (15/35184372088832), by norm_num⟩
  | 15 => ⟨((-829149165/1125899906842624), (158358019/562949953421312)), (99/1125899906842624), by norm_num⟩
  | 16 => ⟨((1262181619/9007199254740992), (-241062271/4503599627370496)), (153/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (-475288540305/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444391961813537/158456325028528675187087900672), (-280877778361/316912650057057350374175801344)), (2883/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((118024446355303/2475880078570760549798248448), (-315910209933/19807040628566084398385987584)), (6487/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888082214124673/2475880078570760549798248448), (-167778470983/618970019642690137449562112)), (110283/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884874467039205/77371252455336267181195264), (-167723570479/38685626227668133590597632)), (6893/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548202281287913/9671406556917033397649408), (-628730163305/9671406556917033397649408)), (12925/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314401732988741/151115727451828646838272), (-137476445193/151115727451828646838272)), (5655/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885872634415499/75557863725914323419136), (-223290012591/18889465931478580854784)), (147039/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296100713441393/4722366482869645213696), (-669488041485/4722366482869645213696)), (6893/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619471175238733/590295810358705651712), (-919925765887/590295810358705651712)), (75829/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910502716829591/36893488147419103232), (-574488781195/36893488147419103232)), (189593/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454970444999413/2305843009213693952), (-645661390611/4611686018427387904)), (213319/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795566837893363/576460752303423488), (-1289728486513/1152921504606846976)), (213355/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298022227287403/36028797018963968), (-1126721488697/144115188075855872)), (186725/144115188075855872), by norm_num⟩
  | 4 => ⟨((743953612288579/18014398509481984), (-105406684989/2251799813685248)), (140083/18014398509481984), by norm_num⟩
  | 3 => ⟨((371152059408059/2251799813685248), (-1050945897177/4503599627370496)), (350347/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218688916563687/4503599627370496), (-2092558509161/2251799813685248)), (701115/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101156948915195/1125899906842624), (-1557803865359/562949953421312)), (263185/562949953421312), by norm_num⟩
  | 0 => ⟨((269193325213445/281474976710656), (-191840994193/35184372088832)), (2109821/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((269193325213445/281474976710656), (-191840994193/35184372088832)), (8048328408248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029756773357067/1125899906842624), (-23484206003135/2251799813685248)), (2029267/1125899906842624), by norm_num⟩
  | 2 => ⟨((1883402119225967/2251799813685248), (-21478836663605/1125899906842624)), (1877147/562949953421312), by norm_num⟩
  | 3 => ⟨((393613828309733/562949953421312), (-71859472134047/2251799813685248)), (12846829/2251799813685248), by norm_num⟩
  | 4 => ⟨((274640948833107/562949953421312), (-50244043462653/1125899906842624)), (4696227/562949953421312), by norm_num⟩
  | 5 => ⟨((132865336155561/562949953421312), (-196096604125201/4503599627370496)), (10002701/1125899906842624), by norm_num⟩
  | 6 => ⟨((969314197939485/18014398509481984), (-370255878949291/18014398509481984)), (89482867/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-119356347/2097152)), (1/16777216), by norm_num⟩, -9, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile008Terms2
