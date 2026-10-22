/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile017Gamma
import XiBand97.Tile017Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile017
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1701519445/1125899906842624), (113829917/1125899906842624)), (2777/1125899906842624), by norm_num⟩
  | 1 => ⟨((-261092211/140737488355328), (-140880723/140737488355328)), (193/35184372088832), by norm_num⟩
  | 2 => ⟨((-406509551/562949953421312), (-354419923/281474976710656)), (3457/562949953421312), by norm_num⟩
  | 3 => ⟨((1272617/70368744177664), (-741914591/1125899906842624)), (10391/2251799813685248), by norm_num⟩
  | 4 => ⟨((268828591/2251799813685248), (-421752773/2251799813685248)), (11813/4503599627370496), by norm_num⟩
  | 5 => ⟨((950010147/18014398509481984), (-485490361/18014398509481984)), (683/562949953421312), by norm_num⟩
  | 6 => ⟨((7320757/562949953421312), (45153053/72057594037927936)), (70205/144115188075855872), by norm_num⟩
  | 7 => ⟨((148484981/72057594037927936), (370056807/288230376151711744)), (53951/288230376151711744), by norm_num⟩
  | 8 => ⟨((27962005/144115188075855872), (98270125/288230376151711744)), (95381/1152921504606846976), by norm_num⟩
  | 9 => ⟨((72663589/36893488147419103232), (2058678551/36893488147419103232)), (942955/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-218981821/73786976294838206464), (475627511/73786976294838206464)), (6290365/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-92799563/147573952589676412928), (305703269/590295810358705651712)), (47894515/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-1559224967/18889465931478580854784), (407572449/18889465931478580854784)), (47357875/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-76682333/9444732965739290427392), (-3096409/2361183241434822606848)), (1511956779/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-736247/1180591620717411303424), (-14724425/37778931862957161709568)), (1511296569/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-1368133/37778931862957161709568), (-1874003/37778931862957161709568)), (1511180101/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-11923/9444732965739290427392), (-87849/18889465931478580854784)), (1511160809/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile017Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((45212547/33554432), (924984085/134217728)), (28169/134217728), by norm_num⟩
  | 1 => ⟨((12157571/4194304), (1019846933/67108864)), (7513/33554432), by norm_num⟩
  | 2 => ⟨((-134027173/67108864), (-75391973/8388608)), (3881/16777216), by norm_num⟩
  | 3 => ⟨((13057783/16777216), (501728885/134217728)), (30757/134217728), by norm_num⟩
  | 4 => ⟨((-39269229/268435456), (-160090715/134217728)), (237269/1073741824), by norm_num⟩
  | 5 => ⟨((-286967/134217728), (81960523/268435456)), (456113/2147483648), by norm_num⟩
  | 6 => ⟨((5873449/536870912), (-8649343/134217728)), (1771155/8589934592), by norm_num⟩
  | 7 => ⟨((-4515943/1073741824), (5977/524288)), (27856431/137438953472), by norm_num⟩
  | 8 => ⟨((2279433/2147483648), (-3653427/2147483648)), (110516411/549755813888), by norm_num⟩
  | 9 => ⟨((-450083/2147483648), (913597/4294967296)), (881158103/4398046511104), by norm_num⟩
  | 10 => ⟨((591871/17179869184), (-370427/17179869184)), (1760180653/8796093022208), by norm_num⟩
  | 11 => ⟨((-333729/68719476736), (108375/68719476736)), (1759491885/8796093022208), by norm_num⟩
  | 12 => ⟨((20475/34359738368), (-1201/34359738368)), (1759290125/8796093022208), by norm_num⟩
  | 13 => ⟨((-8795/137438953472), (-7345/549755813888)), (1759235949/8796093022208), by norm_num⟩
  | 14 => ⟨((26335/4398046511104), (13649/4398046511104)), (1759222523/8796093022208), by norm_num⟩
  | 15 => ⟨((-2105/4398046511104), (-995/2199023255552)), (879609717/4398046511104), by norm_num⟩
  | 16 => ⟨((17/549755813888), (465/8796093022208)), (879609385/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile017Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53817/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53817/2560))
  have he : value ((69/80), (53817/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-807481223/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((591567960908205/1125899906842624), (349766086223587/1125899906842624)), (32387573/2251799813685248), by norm_num⟩
  | 1 => ⟨((-322907221/1073741824), (-763678917/4294967296)), (19/2147483648), by norm_num⟩
  | 2 => ⟨((739283093/8589934592), (6829735/134217728)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((-1128372601/68719476736), (-333576609/34359738368)), (39/68719476736), by norm_num⟩
  | 4 => ⟨((1291681839/549755813888), (763710227/549755813888)), (47/549755813888), by norm_num⟩
  | 5 => ⟨((-295725361/1099511627776), (-699393537/4398046511104)), (45/4398046511104), by norm_num⟩
  | 6 => ⟨((451367545/17592186044416), (66718057/4398046511104)), (9/8796093022208), by norm_num⟩
  | 7 => ⟨((-1181014671/562949953421312), (-349138989/281474976710656)), (25/281474976710656), by norm_num⟩
  | 8 => ⟨((675971395/4503599627370496), (399669835/4503599627370496)), (15/2251799813685248), by norm_num⟩
  | 9 => ⟨((-687826363/72057594037927936), (-406679115/72057594037927936)), (33/72057594037927936), by norm_num⟩
  | 10 => ⟨((1259800631/2305843009213693952), (744860379/2305843009213693952)), (63/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-262205715/9223372036854775808), (-620119227/36893488147419103232)), (55/36893488147419103232), by norm_num⟩
  | 12 => ⟨((400206291/295147905179352825856), (59155751/73786976294838206464)), (11/147573952589676412928), by norm_num⟩
  | 13 => ⟨((-1127699943/18889465931478580854784), (-333377753/9444732965739290427392)), (65/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((737663901/302231454903657293676544), (54518211/37778931862957161709568)), (45/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-450360487/4835703278458516698824704), (-133138401/2417851639229258349412352)), (57/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((515541109/154742504910672534362390528), (609630027/309485009821345068724781056)), (17/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (695546098385/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781209059315911/633825300114114700748351602688), (206322588485/158456325028528675187087900672)), (23071/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892486892688491/39614081257132168796771975168), (232102507289/9903520314283042199192993792)), (6489/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892433192485951/2475880078570760549798248448), (493192959553/1237940039285380274899124224)), (6895/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774099061010727/154742504910672534362390528), (986329967385/154742504910672534362390528)), (13791/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552279620900151/9671406556917033397649408), (462312449233/4835703278458516698824704)), (6465/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630586850008729/302231454903657293676544), (404493671645/302231454903657293676544)), (22629/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891666937945913/75557863725914323419136), (657246492017/37778931862957161709568)), (36775/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300444958952187/4722366482869645213696), (15402691045/73786976294838206464)), (27585/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812721052745845/295147905179352825856), (84704898041/36893488147419103232)), (37933/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914232743748533/36893488147419103232), (1693860317409/73786976294838206464)), (47423/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914134690740637/4611686018427387904), (952633066201/4611686018427387904)), (53361/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599515083303185/1152921504606846976), (238107222383/144115188075855872)), (53373/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199415679227837/144115188075855872), (1666291231389/144115188075855872)), (11679/36028797018963968), by norm_num⟩
  | 4 => ⟨((187360434182993/4503599627370496), (1249259188523/18014398509481984)), (17525/9007199254740992), by norm_num⟩
  | 3 => ⟨((749152125254975/4503599627370496), (3121541055011/9007199254740992)), (43837/4503599627370496), by norm_num⟩
  | 2 => ⟨((561502049513745/1125899906842624), (3119131493197/2251799813685248)), (21937/562949953421312), by norm_num⟩
  | 1 => ⟨((70097233897685/70368744177664), (4672676179897/1125899906842624)), (131803/1125899906842624), by norm_num⟩
  | 0 => ⟨((279302447078865/281474976710656), (4660642595697/562949953421312)), (132169/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279302447078865/281474976710656), (4660642595697/562949953421312)), (504184725047874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((554254786400257/562949953421312), (9249340009903/562949953421312)), (528973/1125899906842624), by norm_num⟩
  | 2 => ⟨((272770977322679/281474976710656), (36425909197619/1125899906842624)), (264747/281474976710656), by norm_num⟩
  | 3 => ⟨((1056166043735585/1125899906842624), (70599034896913/1125899906842624)), (2121005/1125899906842624), by norm_num⟩
  | 4 => ⟨((1972648690105853/2251799813685248), (264905620563465/2251799813685248)), (2122635/562949953421312), by norm_num⟩
  | 5 => ⟨((848469709329219/1125899906842624), (232065800090363/1125899906842624)), (8436827/1125899906842624), by norm_num⟩
  | 6 => ⟨((591567960908205/1125899906842624), (349766086223587/1125899906842624)), (32387573/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-807481223/67108864)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-929370565/1125899906842624), (-29298545/70368744177664)), (2349/1125899906842624), by norm_num⟩
  | 1 => ⟨((-107699487/562949953421312), (-972734823/1125899906842624)), (1639/281474976710656), by norm_num⟩
  | 2 => ⟨((577505069/2251799813685248), (-363897159/1125899906842624)), (18365/2251799813685248), by norm_num⟩
  | 3 => ⟨((140232459/1125899906842624), (-2446175/2251799813685248)), (68893/9007199254740992), by norm_num⟩
  | 4 => ⟨((622681917/36028797018963968), (380166157/18014398509481984)), (195007/36028797018963968), by norm_num⟩
  | 5 => ⟨((-136882571/144115188075855872), (162089497/36028797018963968)), (890831/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1268901231/2305843009213693952), (643692227/2305843009213693952)), (3448197/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-141398909/2305843009213693952), (-504056671/18446744073709551616)), (1487413/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-238693075/147573952589676412928), (-211490999/36893488147419103232)), (19875473/73786976294838206464), by norm_num⟩
  | 9 => ⟨((547328131/2361183241434822606848), (-106127899/295147905179352825856)), (149453907/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((447607851/18889465931478580854784), (-3204937/590295810358705651712)), (186040105/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((19363293/18889465931478580854784), (3296225/9444732965739290427392)), (608682919/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((913523/18889465931478580854784), (426481/18889465931478580854784)), (1143544797/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((28663/9444732965739290427392), (12949/4722366482869645213696)), (281274599/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((773/18889465931478580854784), (4859/18889465931478580854784)), (1120836095/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-61/9444732965739290427392), (43/4722366482869645213696)), (279979807/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((-1/4722366482869645213696), (1/9444732965739290427392)), (1119734575/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((247297961/140737488355328), (-879570227/140737488355328)), (9775/35184372088832), by norm_num⟩
  | 1 => ⟨((677726161/70368744177664), (-1142344111/70368744177664)), (41185/70368744177664), by norm_num⟩
  | 2 => ⟨((918634127/70368744177664), (18342067/4398046511104)), (59159/70368744177664), by norm_num⟩
  | 3 => ⟨((-44918113/70368744177664), (1084433707/281474976710656)), (136351/140737488355328), by norm_num⟩
  | 4 => ⟨((-257115111/562949953421312), (80223905/2251799813685248)), (2225223/2251799813685248), by norm_num⟩
  | 5 => ⟨((-490595511/18014398509481984), (300814059/18014398509481984)), (16596355/18014398509481984), by norm_num⟩
  | 6 => ⟨((-444168823/36028797018963968), (-36783893/9007199254740992)), (29632307/36028797018963968), by norm_num⟩
  | 7 => ⟨((66169557/288230376151711744), (-933054157/576460752303423488)), (846728355/1152921504606846976), by norm_num⟩
  | 8 => ⟨((188073479/2305843009213693952), (-1356485/144115188075855872)), (1554759921/2305843009213693952), by norm_num⟩
  | 9 => ⟨((5095759/2305843009213693952), (-6376947/2305843009213693952)), (1476175939/2305843009213693952), by norm_num⟩
  | 10 => ⟨((709461/1152921504606846976), (117027/1152921504606846976)), (1437738687/2305843009213693952), by norm_num⟩
  | 11 => ⟨((9121/2305843009213693952), (60605/2305843009213693952)), (1421097315/2305843009213693952), by norm_num⟩
  | 12 => ⟨((2075/2305843009213693952), (1497/2305843009213693952)), (88412997/144115188075855872), by norm_num⟩
  | 13 => ⟨((-41/1152921504606846976), (5/36028797018963968)), (1412298581/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-17/2305843009213693952), (-1/1152921504606846976)), (1411541063/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-1/1152921504606846976), (-1/1152921504606846976)), (1411310211/2305843009213693952), by norm_num⟩
  | 16 => ⟨(0, (-1/2305843009213693952)), (1411244445/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1978383543/1125899906842624), (-7036561971/1125899906842624)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((10843618517/1125899906842624), (-9138752899/562949953421312)), (1/536870912), by norm_num⟩
  | 2 => ⟨((14698146141/1125899906842624), (4695568841/1125899906842624)), (1/536870912), by norm_num⟩
  | 3 => ⟨((-718689807/1125899906842624), (4337734953/1125899906842624)), (1/268435456), by norm_num⟩
  | 4 => ⟨((-514230195/1125899906842624), (1253495/35184372088832)), (1/268435456), by norm_num⟩
  | 5 => ⟨((-7665555/281474976710656), (9400463/562949953421312)), (1/268435456), by norm_num⟩
  | 6 => ⟨((-13880267/1125899906842624), (-1149503/281474976710656)), (1/268435456), by norm_num⟩
  | 7 => ⟨((129239/562949953421312), (-1822357/1125899906842624)), (1/268435456), by norm_num⟩
  | 8 => ⟨((11479/140737488355328), (-10599/1125899906842624)), (1/268435456), by norm_num⟩
  | 9 => ⟨((311/140737488355328), (-389/140737488355328)), (1/268435456), by norm_num⟩
  | 10 => ⟨((173/281474976710656), (57/562949953421312)), (1/268435456), by norm_num⟩
  | 11 => ⟨((1/281474976710656), (15/562949953421312)), (1/268435456), by norm_num⟩
  | 12 => ⟨((1/1125899906842624), (1/1125899906842624)), (1/268435456), by norm_num⟩
  | 13 => ⟨(0, 0), (1/268435456), by norm_num⟩
  | 14 => ⟨(0, 0), (1/268435456), by norm_num⟩
  | 15 => ⟨(0, 0), (1/268435456), by norm_num⟩
  | 16 => ⟨(0, 0), (1/268435456), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨17,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨17,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(161751/1048576)) (K:=(8459/268435456)) (L:=(3832226312246719/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile017
