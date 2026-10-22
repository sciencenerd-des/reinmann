/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import XiBand97.Tile005Gamma
import XiBand97.Tile005Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile005
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-796893035/70368744177664), (-40715855/1099511627776)), (781/70368744177664), by norm_num⟩
  | 1 => ⟨((263780211/17592186044416), (-3347359117/70368744177664)), (1801/70368744177664), by norm_num⟩
  | 2 => ⟨((870443745/35184372088832), (-2768404837/140737488355328)), (4155/140737488355328), by norm_num⟩
  | 3 => ⟨((920494027/70368744177664), (-651452451/562949953421312)), (12733/562949953421312), by norm_num⟩
  | 4 => ⟨((501407359/140737488355328), (2103809481/1125899906842624)), (14623/1125899906842624), by norm_num⟩
  | 5 => ⟨((1105570479/2251799813685248), (940878823/1125899906842624)), (26973/4503599627370496), by norm_num⟩
  | 6 => ⟨((-54029861/36028797018963968), (6894690357/36028797018963968)), (20971/9007199254740992), by norm_num⟩
  | 7 => ⟨((-4508409/281474976710656), (3974146459/144115188075855872)), (57597/72057594037927936), by norm_num⟩
  | 8 => ⟨((-2254947909/576460752303423488), (2765328887/1152921504606846976)), (302289/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-1335341069/2305843009213693952), (27459345/576460752303423488)), (906565/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-569058655/9223372036854775808), (-1701490397/73786976294838206464)), (248507/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-2877158759/590295810358705651712), (-696405813/147573952589676412928)), (25403617/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-2456045119/9444732965739290427392), (-5555288171/9444732965739290427392)), (191794091/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((-28965321/9444732965739290427392), (-2137565431/37778931862957161709568)), (1515529463/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((200545559/151115727451828646838272), (-677227319/151115727451828646838272)), (6047719219/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((31507057/151115727451828646838272), (-44877961/151115727451828646838272)), (3022571747/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((800683/37778931862957161709568), (-38109/2361183241434822606848)), (6044710123/151115727451828646838272), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile005Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1853116427/134217728), (1605891877/67108864)), (6777/33554432), by norm_num⟩
  | 1 => ⟨((1814518817/134217728), (-1268446063/268435456)), (27417/134217728), by norm_num⟩
  | 2 => ⟨((-1608677223/268435456), (334441131/268435456)), (220681/1073741824), by norm_num⟩
  | 3 => ⟨((1058797227/536870912), (-687869/16777216)), (440421/2147483648), by norm_num⟩
  | 4 => ⟨((-132090987/268435456), (-12806907/134217728)), (1749299/8589934592), by norm_num⟩
  | 5 => ⟨((103949889/1073741824), (47646589/1073741824)), (1736403/8589934592), by norm_num⟩
  | 6 => ⟨((-32441685/2147483648), (-13408307/1073741824)), (27635183/137438953472), by norm_num⟩
  | 7 => ⟨((1938851/1073741824), (11342367/4294967296)), (110207931/549755813888), by norm_num⟩
  | 8 => ⟨((-302025/2147483648), (-482661/1073741824)), (1760800685/8796093022208), by norm_num⟩
  | 9 => ⟨((-14893/34359738368), (1088343/17179869184)), (3519529305/17592186044416), by norm_num⟩
  | 10 => ⟨((87105/34359738368), (-255747/34359738368)), (3518780249/17592186044416), by norm_num⟩
  | 11 => ⟨((-152867/274877906944), (49317/68719476736)), (3518535577/17592186044416), by norm_num⟩
  | 12 => ⟨((90735/1099511627776), (-29235/549755813888)), (3518463177/17592186044416), by norm_num⟩
  | 13 => ⟨((-21423/2199023255552), (9871/4398046511104)), (3518443573/17592186044416), by norm_num⟩
  | 14 => ⟨((16811/17592186044416), (265/2199023255552)), (439804833/2199023255552), by norm_num⟩
  | 15 => ⟨((-2747/35184372088832), (-719/17592186044416)), (3518437521/17592186044416), by norm_num⟩
  | 16 => ⟨((45/8796093022208), (101/17592186044416)), (439804659/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile005Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (2127/128)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (2127/128))
  have he : value ((69/80), (2127/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_logpi : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negativeHalfLogPi : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negativeHalfLogPi : Sound J_negativeHalfLogPi F_negativeHalfLogPi c := by
  apply sound_round (sound_scale (A_logpi hcre) S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negativeHalfLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piArg : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66258563/134217728), (-5106230555/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
private theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul (A_negativeHalfLogPi hcre) (A_variable hcre) S_negativeHalfLogPi S_variable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negativeHalfLogPi, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piPower : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-171168557361027/281474976710656), (29623331093881/562949953421312)), (866517/140737488355328), by norm_num⟩
  | 1 => ⟨((186864627/536870912), (-64679551/2147483648)), (63/17179869184), by norm_num⟩
  | 2 => ⟨((-1711276185/17179869184), (74040615/8589934592)), (75/68719476736), by norm_num⟩
  | 3 => ⟨((2611931989/137438953472), (-113008673/68719476736)), (59/274877906944), by norm_num⟩
  | 4 => ⟨((-5979913215/2199023255552), (517457621/2199023255552)), (35/1099511627776), by norm_num⟩
  | 5 => ⟨((5476308297/17592186044416), (-473879363/17592186044416)), (33/8796093022208), by norm_num⟩
  | 6 => ⟨((-2089631257/70368744177664), (361642579/140737488355328)), (13/35184372088832), by norm_num⟩
  | 7 => ⟨((1366893343/562949953421312), (-236561753/1125899906842624)), (71/2251799813685248), by norm_num⟩
  | 8 => ⟨((-6258894641/36028797018963968), (541598617/36028797018963968)), (21/9007199254740992), by norm_num⟩
  | 9 => ⟨((6368661109/576460752303423488), (-275548499/288230376151711744)), (11/72057594037927936), by norm_num⟩
  | 10 => ⟨((-5832317363/9223372036854775808), (504685763/9223372036854775808)), (83/9223372036854775808), by norm_num⟩
  | 11 => ⟨((606947999/18446744073709551616), (-420166455/147573952589676412928)), (71/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-3705554739/2361183241434822606848), (641302797/4722366482869645213696)), (111/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((2610374925/37778931862957161709568), (-451765217/75557863725914323419136)), (5/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-6830112433/2417851639229258349412352), (591027595/2417851639229258349412352)), (27/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((521242255/4835703278458516698824704), (-360835707/38685626227668133590597632)), (17/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-596681587/154742504910672534362390528), (206529709/618970019642690137449562112)), (5/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (3979836863135/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111324846718687/39614081257132168796771975168), (4722218960079/633825300114114700748351602688)), (5793/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946236619527625/19807040628566084398385987584), (5312223843253/39614081257132168796771975168)), (3259/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((946208916639349/1237940039285380274899124224), (5643949017447/2475880078570760549798248448)), (433/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1774082743099667/154742504910672534362390528), (2821811891089/77371252455336267181195264)), (3465/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552263304392495/9671406556917033397649408), (2645275715869/4835703278458516698824704)), (6499/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261158404783473/604462909807314587353088), (4628886299763/604462909807314587353088)), (2845/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891640174272179/75557863725914323419136), (7521290386433/75557863725914323419136)), (4625/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300423216268381/4722366482869645213696), (5640398450697/4722366482869645213696)), (6943/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812704748185925/295147905179352825856), (7754621344601/590295810358705651712)), (597/36893488147419103232), by norm_num⟩
  | 8 => ⟨((457105164484177/18446744073709551616), (9691884533415/73786976294838206464)), (5975/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828213356512873/9223372036854775808), (2725363016285/2305843009213693952)), (6729/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799726035855009/576460752303423488), (10899048776593/1152921504606846976)), (3369/288230376151711744), by norm_num⟩
  | 5 => ⟨((299838172071613/36028797018963968), (1191744510841/18014398509481984)), (11811/144115188075855872), by norm_num⟩
  | 4 => ⟨((749386642934685/18014398509481984), (14295491229603/36028797018963968)), (4439/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498139062439377/9007199254740992), (8929897326139/4503599627370496)), (22265/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122797777735885/2251799813685248), (4461338020469/562949953421312)), (11185/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121143593103427/1125899906842624), (26731612531441/1125899906842624)), (33819/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115975820659751/1125899906842624), (26657856104207/562949953421312)), (68691/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1115975820659751/1125899906842624), (26657856104207/562949953421312)), (262035374168014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1103614503897989/1125899906842624), (105691536741837/1125899906842624)), (71339/562949953421312), by norm_num⟩
  | 2 => ⟨((267962157413127/281474976710656), (103599540402007/562949953421312)), (4789/17592186044416), by norm_num⟩
  | 3 => ⟨((491130703129419/562949953421312), (197252037659227/562949953421312)), (348187/562949953421312), by norm_num⟩
  | 4 => ⟨((359358767091465/562949953421312), (344174580210985/562949953421312)), (53221/35184372088832), by norm_num⟩
  | 5 => ⟨((37952154564245/1125899906842624), (439407276107467/562949953421312)), (8513497/2251799813685248), by norm_num⟩
  | 6 => ⟨((-171168557361027/281474976710656), (29623331093881/562949953421312)), (866517/140737488355328), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-5106230555/536870912)), (1/268435456), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound (A_piArg hcre) S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue,J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_piPower,J_piArg,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piGamma : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((9714423/1099511627776), (3085391379/140737488355328)), (1075/140737488355328), by norm_num⟩
  | 1 => ⟨((-1642683291/140737488355328), (4832437603/281474976710656)), (6101/281474976710656), by norm_num⟩
  | 2 => ⟨((-4940389781/562949953421312), (-43258673/281474976710656)), (4355/140737488355328), by norm_num⟩
  | 3 => ⟨((-2781093859/2251799813685248), (-2271250085/1125899906842624)), (33145/1125899906842624), by norm_num⟩
  | 4 => ⟨((1844642573/9007199254740992), (-3635237625/9007199254740992)), (189521/9007199254740992), by norm_num⟩
  | 5 => ⟨((2322909705/36028797018963968), (-36962593/9007199254740992)), (434555/36028797018963968), by norm_num⟩
  | 6 => ⟨((272232581/72057594037927936), (846993295/144115188075855872)), (3337137/576460752303423488), by norm_num⟩
  | 7 => ⟨((-327818817/1152921504606846976), (2224600301/4611686018427387904)), (5550003/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-4337011955/147573952589676412928), (-358376367/73786976294838206464)), (132693693/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1723484927/4722366482869645213696), (-341059221/590295810358705651712)), (1519526667/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-162371933/4722366482869645213696), (559821979/4722366482869645213696)), (2400477159/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1056628981/75557863725914323419136), (-147808229/75557863725914323419136)), (5156987111/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((5850477/151115727451828646838272), (-71531129/75557863725914323419136)), (7874843235/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((7067813/151115727451828646838272), (2257121/151115727451828646838272)), (7260821433/151115727451828646838272), by norm_num⟩
  | 14 => ⟨((-51037/18889465931478580854784), (345385/151115727451828646838272)), (3558904171/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((-2341/18889465931478580854784), (-39745/151115727451828646838272)), (7086776113/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((2861/151115727451828646838272), (-183/37778931862957161709568)), (7080466295/151115727451828646838272), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1421880487/2199023255552), (-802757835/8796093022208)), (14295/2199023255552), by norm_num⟩
  | 1 => ⟨((-3661307/137438953472), (-2302043013/8796093022208)), (229847/17592186044416), by norm_num⟩
  | 2 => ⟨((-2257908317/70368744177664), (-2885057863/70368744177664)), (550103/35184372088832), by norm_num⟩
  | 3 => ⟨((903293575/70368744177664), (-162135207/4398046511104)), (291401/17592186044416), by norm_num⟩
  | 4 => ⟨((2480835397/281474976710656), (121779735/70368744177664)), (9234783/562949953421312), by norm_num⟩
  | 5 => ⟨((-293919111/4503599627370496), (4335379805/4503599627370496)), (35706649/2251799813685248), by norm_num⟩
  | 6 => ⟨((-2249958851/72057594037927936), (1555813875/144115188075855872)), (1103385325/72057594037927936), by norm_num⟩
  | 7 => ⟨((-104056785/72057594037927936), (608852097/144115188075855872)), (4300916649/288230376151711744), by norm_num⟩
  | 8 => ⟨((-290824673/576460752303423488), (-17862287/576460752303423488)), (8470091259/576460752303423488), by norm_num⟩
  | 9 => ⟨((-3464171/576460752303423488), (-723437/72057594037927936)), (4201994135/288230376151711744), by norm_num⟩
  | 10 => ⟨((-959139/576460752303423488), (-257307/576460752303423488)), (4187352625/288230376151711744), by norm_num⟩
  | 11 => ⟨((-649/144115188075855872), (-65961/576460752303423488)), (8363035503/576460752303423488), by norm_num⟩
  | 12 => ⟨((-623/576460752303423488), (-125/72057594037927936)), (1044849517/72057594037927936), by norm_num⟩
  | 13 => ⟨((17/576460752303423488), (-125/288230376151711744)), (4178689465/288230376151711744), by norm_num⟩
  | 14 => ⟨((7/288230376151711744), (-11/576460752303423488)), (261154365/18014398509481984), by norm_num⟩
  | 15 => ⟨((3/576460752303423488), 0), (522300795/36028797018963968), by norm_num⟩
  | 16 => ⟨(0, (1/576460752303423488)), (4178389167/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-728002805879/1125899906842624), (-51376501923/562949953421312)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-7498357115/281474976710656), (-147330752353/562949953421312)), (1/33554432), by norm_num⟩
  | 2 => ⟨((-36126531025/1125899906842624), (-46160926015/1125899906842624)), (1/16777216), by norm_num⟩
  | 3 => ⟨((3613173963/281474976710656), (-20753306189/562949953421312)), (1/16777216), by norm_num⟩
  | 4 => ⟨((4961671135/562949953421312), (60889859/35184372088832)), (1/16777216), by norm_num⟩
  | 5 => ⟨((-4592509/70368744177664), (1083845293/1125899906842624)), (1/16777216), by norm_num⟩
  | 6 => ⟨((-35155601/1125899906842624), (6077327/562949953421312)), (1/16777216), by norm_num⟩
  | 7 => ⟨((-1625893/1125899906842624), (594583/140737488355328)), (1/16777216), by norm_num⟩
  | 8 => ⟨((-71001/140737488355328), (-8723/281474976710656)), (1/16777216), by norm_num⟩
  | 9 => ⟨((-423/70368744177664), (-2825/281474976710656)), (1/16777216), by norm_num⟩
  | 10 => ⟨((-937/562949953421312), (-503/1125899906842624)), (1/16777216), by norm_num⟩
  | 11 => ⟨((-5/1125899906842624), (-129/1125899906842624)), (1/16777216), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), (-1/562949953421312)), (1/16777216), by norm_num⟩
  | 13 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 14 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 15 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 16 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨5,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨5,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(326799/1048576)) (K:=(591311/1073741824)) (L:=(385466244923626813/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile005
