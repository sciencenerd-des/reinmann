/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile009Gamma
import XiBand97.Tile009Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile009
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((884936239/140737488355328), (289178765/70368744177664)), (225/35184372088832), by norm_num⟩
  | 1 => ⟨((568932957/140737488355328), (325374563/35184372088832)), (233/17592186044416), by norm_num⟩
  | 2 => ⟨((-2352121/2199023255552), (116246235/17592186044416)), (2005/140737488355328), by norm_num⟩
  | 3 => ⟨((-272518703/140737488355328), (307809327/140737488355328)), (2947/281474976710656), by norm_num⟩
  | 4 => ⟨((-254326577/281474976710656), (152735007/562949953421312)), (6609/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1049113727/4503599627370496), (-134736977/2251799813685248)), (377/140737488355328), by norm_num⟩
  | 6 => ⟨((-161216723/4503599627370496), (-159974427/4503599627370496)), (18831/18014398509481984), by norm_num⟩
  | 7 => ⟨((-174551839/72057594037927936), (-310438451/36028797018963968)), (26753/72057594037927936), by norm_num⟩
  | 8 => ⟨((11009825/36028797018963968), (-96527473/72057594037927936)), (157185/1152921504606846976), by norm_num⟩
  | 9 => ⟨((554006087/4611686018427387904), (-652588653/4611686018427387904)), (300275/4611686018427387904), by norm_num⟩
  | 10 => ⟨((758413545/36893488147419103232), (-327543511/36893488147419103232)), (1694957/36893488147419103232), by norm_num⟩
  | 11 => ⟨((720644063/295147905179352825856), (21708983/295147905179352825856)), (24372949/590295810358705651712), by norm_num⟩
  | 12 => ⟨((1038166619/4722366482869645213696), (496584503/4722366482869645213696)), (190116493/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((282761085/18889465931478580854784), (316086947/18889465931478580854784)), (1512983627/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((25289415/37778931862957161709568), (68233377/37778931862957161709568)), (1511476881/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-4699/18889465931478580854784), (5853009/37778931862957161709568)), (1511209923/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-148605/37778931862957161709568), (209089/18889465931478580854784)), (1511165475/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile009Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((467918621/33554432), (498122197/16777216)), (7011/33554432), by norm_num⟩
  | 1 => ⟨((-405957253/33554432), (-673879675/67108864)), (14735/67108864), by norm_num⟩
  | 2 => ⟨((856425949/134217728), (709204841/134217728)), (30219/134217728), by norm_num⟩
  | 3 => ⟨((-70513787/33554432), (-277166467/134217728)), (14969/67108864), by norm_num⟩
  | 4 => ⟨((34012479/67108864), (43458039/67108864)), (232469/1073741824), by norm_num⟩
  | 5 => ⟨((-6071319/67108864), (-11223373/67108864)), (450329/2147483648), by norm_num⟩
  | 6 => ⟨((1480517/134217728), (9678903/268435456)), (1759539/8589934592), by norm_num⟩
  | 7 => ⟨((-516927/1073741824), (-7037763/1073741824)), (27776943/137438953472), by norm_num⟩
  | 8 => ⟨((-372599/2147483648), (1085209/1073741824)), (110396347/549755813888), by norm_num⟩
  | 9 => ⟨((259829/4294967296), (-567331/4294967296)), (1761672109/8796093022208), by norm_num⟩
  | 10 => ⟨((-209759/17179869184), (123937/8589934592)), (1759987629/8796093022208), by norm_num⟩
  | 11 => ⟨((65289/34359738368), (-21597/17179869184)), (1759438893/8796093022208), by norm_num⟩
  | 12 => ⟨((-33753/137438953472), (10111/137438953472)), (1759276749/8796093022208), by norm_num⟩
  | 13 => ⟨((29785/1099511627776), (37/137438953472)), (1759232845/8796093022208), by norm_num⟩
  | 14 => ⟨((-11291/4398046511104), (-3699/4398046511104)), (1759221859/8796093022208), by norm_num⟩
  | 15 => ⟨((1817/8796093022208), (657/4398046511104)), (1759219301/8796093022208), by norm_num⟩
  | 16 => ⟨((-119/8796093022208), (-161/8796093022208)), (1759218745/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile009Zeta.zetaJet_sound

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
  | 0 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-66258563/134217728), (-1448445795/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-69549351160137/562949953421312), (1346017114984965/2251799813685248)), (56857887/2251799813685248), by norm_num⟩
  | 1 => ⟨((303707965/4294967296), (-183680775/536870912)), (1/67108864), by norm_num⟩
  | 2 => ⟨((-10864487/536870912), (1682118981/17179869184)), (19/4294967296), by norm_num⟩
  | 3 => ⟨((265320597/68719476736), (-320928645/17179869184)), (15/17179869184), by norm_num⟩
  | 4 => ⟨((-303720417/549755813888), (1469506445/549755813888)), (71/549755813888), by norm_num⟩
  | 5 => ⟨((278142271/4398046511104), (-336437589/1099511627776)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((-53066295/8796093022208), (128376721/4398046511104)), (27/17592186044416), by norm_num⟩
  | 7 => ⟨((277698623/562949953421312), (-1343603833/562949953421312)), (73/562949953421312), by norm_num⟩
  | 8 => ⟨((-317889913/9007199254740992), (1538063463/9007199254740992)), (43/4503599627370496), by norm_num⟩
  | 9 => ⟨((323464963/144115188075855872), (-1565037523/144115188075855872)), (45/72057594037927936), by norm_num⟩
  | 10 => ⟨((-37028001/288230376151711744), (358309045/576460752303423488)), (85/2305843009213693952), by norm_num⟩
  | 11 => ⟨((123307809/18446744073709551616), (-1193213301/36893488147419103232)), (73/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-23525689/73786976294838206464), (455302309/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 13 => ⟨((132581215/9444732965739290427392), (-641474659/9444732965739290427392)), (21/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-86725531/151115727451828646838272), (1678434773/604462909807314587353088)), (113/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((211791589/9671406556917033397649408), (-256180593/2417851639229258349412352)), (71/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-121222081/154742504910672534362390528), (293257581/77371252455336267181195264)), (21/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (2311625679229/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890602707961265/316912650057057350374175801344), (2742826650051/633825300114114700748351602688)), (11559/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946241285714115/19807040628566084398385987584), (3085535347717/39614081257132168796771975168)), (6503/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946214165702173/1237940039285380274899124224), (204888451933/154742504910672534362390528)), (27643/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774093896503441/154742504910672534362390528), (3278028342183/154742504910672534362390528)), (27/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((776137228416925/4835703278458516698824704), (1536476476167/4835703278458516698824704)), (25927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261168859173911/604462909807314587353088), (2688635159535/604462909807314587353088)), (5673/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945829233703533/37778931862957161709568), (4368659503493/75557863725914323419136)), (36885/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325109519379575/1180591620717411303424), (3276168458305/4722366482869645213696)), (27673/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812715892439641/295147905179352825856), (2252100692497/295147905179352825856)), (38067/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114278206197219/4611686018427387904), (1407363994655/18446744073709551616)), (47607/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828251649806055/9223372036854775808), (791505398885/1152921504606846976)), (53591/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399873785082199/288230376151711744), (6330673773153/1152921504606846976)), (419/9007199254740992), by norm_num⟩
  | 5 => ⟨((149924467838267/18014398509481984), (5537797669281/144115188075855872)), (23487/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498848599076091/36028797018963968), (8303609525109/36028797018963968)), (35277/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498251967994847/9007199254740992), (648381404389/562949953421312)), (44177/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122938796787177/2251799813685248), (10365973892153/2251799813685248)), (88597/2251799813685248), by norm_num⟩
  | 1 => ⟨((140178161342525/140737488355328), (15528589011639/1125899906842624)), (133505/1125899906842624), by norm_num⟩
  | 0 => ⟨((558409599381727/562949953421312), (30975389244575/1125899906842624)), (269451/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558409599381727/562949953421312), (30975389244575/1125899906842624)), (1027873997214889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((553479772230765/562949953421312), (7681390944983/140737488355328)), (549383/1125899906842624), by norm_num⟩
  | 2 => ⟨((542491914499665/562949953421312), (30208685406625/281474976710656)), (1140253/1125899906842624), by norm_num⟩
  | 3 => ⟨((1032586349230961/1125899906842624), (116443513183797/562949953421312)), (1221191/562949953421312), by norm_num⟩
  | 4 => ⟨((898834963407843/1125899906842624), (427171123967029/1125899906842624)), (2745155/562949953421312), by norm_num⟩
  | 5 => ⟨((555492649472743/1125899906842624), (341021736698181/562949953421312)), (6466103/562949953421312), by norm_num⟩
  | 6 => ⟨((-69549351160137/562949953421312), (1346017114984965/2251799813685248)), (56857887/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1448445795/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-227521579/70368744177664), (457519249/140737488355328)), (1373/281474976710656), by norm_num⟩
  | 1 => ⟨((-1175621059/281474976710656), (-165160511/281474976710656)), (3571/281474976710656), by norm_num⟩
  | 2 => ⟨((-505258469/562949953421312), (-930206429/562949953421312)), (149/8796093022208), by norm_num⟩
  | 3 => ⟨((519635517/2251799813685248), (-1097497803/2251799813685248)), (34743/2251799813685248), by norm_num⟩
  | 4 => ⟨((246275537/2251799813685248), (-181883331/9007199254740992)), (48175/4503599627370496), by norm_num⟩
  | 5 => ⟨((225704095/18014398509481984), (218640165/18014398509481984)), (433103/72057594037927936), by norm_num⟩
  | 6 => ⟨((-95845241/288230376151711744), (609209379/288230376151711744)), (1646763/576460752303423488), by norm_num⟩
  | 7 => ⟨((-856544557/4611686018427387904), (209334935/2305843009213693952)), (1374301/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1000408451/73786976294838206464), (-546985327/73786976294838206464)), (33931005/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-74226529/590295810358705651712), (-968929987/1180591620717411303424)), (26873973/147573952589676412928), by norm_num⟩
  | 10 => ⟨((26753913/2361183241434822606848), (-203141861/9444732965739290427392)), (420924619/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-5920183/9444732965739290427392), (-3475289/2361183241434822606848)), (1156379485/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1216275/18889465931478580854784), (-3763149/18889465931478580854784)), (253137465/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((515661/37778931862957161709568), (-26893/9444732965739290427392)), (976555595/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((4771/18889465931478580854784), (2179/4722366482869645213696)), (1936446383/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-111/9444732965739290427392), (-251/37778931862957161709568)), (1932853609/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((1/590295810358705651712), (-9/9444732965739290427392)), (966064061/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-622797901/4398046511104), (-222821179/4398046511104)), (6895/4398046511104), by norm_num⟩
  | 1 => ⟨((272145785/8796093022208), (-1223115015/8796093022208)), (27099/8796093022208), by norm_num⟩
  | 2 => ⟨((190761159/4398046511104), (105824455/35184372088832)), (144803/35184372088832), by norm_num⟩
  | 3 => ⟨((538332979/281474976710656), (869884033/281474976710656)), (625627/140737488355328), by norm_num⟩
  | 4 => ⟨((355886755/281474976710656), (11800659/17592186044416)), (2414873/562949953421312), by norm_num⟩
  | 5 => ⟨((-407843757/4503599627370496), (826700097/2251799813685248)), (8828551/2251799813685248), by norm_num⟩
  | 6 => ⟨((-755858341/18014398509481984), (-37070747/9007199254740992)), (127696601/36028797018963968), by norm_num⟩
  | 7 => ⟨((-218305975/576460752303423488), (-968670359/576460752303423488)), (940843647/288230376151711744), by norm_num⟩
  | 8 => ⟨((-37029185/288230376151711744), (-17424423/288230376151711744)), (1783522709/576460752303423488), by norm_num⟩
  | 9 => ⟨((1155115/576460752303423488), (-10812897/576460752303423488)), (1732411209/576460752303423488), by norm_num⟩
  | 10 => ⟨((330329/576460752303423488), (-12553/72057594037927936)), (1709003637/576460752303423488), by norm_num⟩
  | 11 => ⟨((9935/576460752303423488), (-13065/288230376151711744)), (106212901/36028797018963968), by norm_num⟩
  | 12 => ⟨((153/36028797018963968), (213/576460752303423488)), (1695838825/576460752303423488), by norm_num⟩
  | 13 => ⟨((7/576460752303423488), (27/576460752303423488)), (423656087/144115188075855872), by norm_num⟩
  | 14 => ⟨((5/576460752303423488), (9/576460752303423488)), (1694242703/576460752303423488), by norm_num⟩
  | 15 => ⟨((-3/576460752303423488), (1/576460752303423488)), (1694131259/576460752303423488), by norm_num⟩
  | 16 => ⟨(0, 0), (1694100843/576460752303423488), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-159436254163/1125899906842624), (-28521112547/562949953421312)), (1/536870912), by norm_num⟩
  | 1 => ⟨((34834664379/1125899906842624), (-19569839557/140737488355328)), (1/134217728), by norm_num⟩
  | 2 => ⟨((6104357069/140737488355328), (3386386307/1125899906842624)), (1/134217728), by norm_num⟩
  | 3 => ⟨((2153329725/1125899906842624), (1739767479/562949953421312)), (1/67108864), by norm_num⟩
  | 4 => ⟨((711774179/562949953421312), (188810647/281474976710656)), (1/67108864), by norm_num⟩
  | 5 => ⟨((-101961713/1125899906842624), (413350059/1125899906842624)), (1/67108864), by norm_num⟩
  | 6 => ⟨((-5905105/140737488355328), (-579249/140737488355328)), (1/67108864), by norm_num⟩
  | 7 => ⟨((-213225/562949953421312), (-945935/562949953421312)), (1/67108864), by norm_num⟩
  | 8 => ⟨((-72313/562949953421312), (-68089/1125899906842624)), (1/67108864), by norm_num⟩
  | 9 => ⟨((1125/562949953421312), (-21113/1125899906842624)), (1/67108864), by norm_num⟩
  | 10 => ⟨((647/1125899906842624), (-201/1125899906842624)), (1/67108864), by norm_num⟩
  | 11 => ⟨((5/281474976710656), (-25/562949953421312)), (1/67108864), by norm_num⟩
  | 12 => ⟨((5/1125899906842624), 0), (1/67108864), by norm_num⟩
  | 13 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | 14 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | 15 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | 16 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨9,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨9,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(326799/1048576)) (K:=(215567/536870912)) (L:=(88779367800455003/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile009
