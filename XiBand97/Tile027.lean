/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile027Gamma
import XiBand97.Tile027Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile027
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1787737897/9007199254740992), (158109405/9007199254740992)), (2095/9007199254740992), by norm_num⟩
  | 1 => ⟨((262035517/1125899906842624), (764960161/4503599627370496)), (2111/4503599627370496), by norm_num⟩
  | 2 => ⟨((182623773/2251799813685248), (855527835/4503599627370496)), (2351/4503599627370496), by norm_num⟩
  | 3 => ⟨((-223890201/18014398509481984), (1748826427/18014398509481984)), (7277/18014398509481984), by norm_num⟩
  | 4 => ⟨((-376676631/18014398509481984), (987851181/36028797018963968)), (4463/18014398509481984), by norm_num⟩
  | 5 => ⟨((-638831133/72057594037927936), (543798405/144115188075855872)), (19515/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1275097355/576460752303423488), (-136196711/576460752303423488)), (44273/576460752303423488), by norm_num⟩
  | 7 => ⟨((-807781/2251799813685248), (-8963263/36028797018963968)), (30121/576460752303423488), by norm_num⟩
  | 8 => ⟨((-156579301/4611686018427387904), (-1220352195/18446744073709551616)), (100511/2305843009213693952), by norm_num⟩
  | 9 => ⟨((9194475/147573952589676412928), (-1648805749/147573952589676412928)), (6041683/147573952589676412928), by norm_num⟩
  | 10 => ⟨((404223807/590295810358705651712), (-393987905/295147905179352825856)), (23743327/590295810358705651712), by norm_num⟩
  | 11 => ⟨((689061603/4722366482869645213696), (-513585479/4722366482869645213696)), (189122573/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((372814671/18889465931478580854784), (-148819315/37778931862957161709568)), (1511521575/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((75185259/37778931862957161709568), (8928741/18889465931478580854784)), (1511224893/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((5788177/37778931862957161709568), (2198799/18889465931478580854784)), (1511169007/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((315549/37778931862957161709568), (276607/18889465931478580854784)), (377789797/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((6743/37778931862957161709568), (51827/37778931862957161709568)), (755578785/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile027Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((375802067/67108864), (1649931229/67108864)), (1803/8388608), by norm_num⟩
  | 1 => ⟨((-354626121/33554432), (-15389563/2097152)), (7855/33554432), by norm_num⟩
  | 2 => ⟨((561583351/67108864), (62868627/8388608)), (8203/33554432), by norm_num⟩
  | 3 => ⟨((-239686029/67108864), (-277627413/67108864)), (32341/134217728), by norm_num⟩
  | 4 => ⟨((35538993/33554432), (213574729/134217728)), (123139/536870912), by norm_num⟩
  | 5 => ⟨((-62314029/268435456), (-63619815/134217728)), (466585/2147483648), by norm_num⟩
  | 6 => ⟨((20051113/536870912), (62042595/536870912)), (1791827/8589934592), by norm_num⟩
  | 7 => ⟨((-4055147/1073741824), (-25568629/1073741824)), (1749915/8589934592), by norm_num⟩
  | 8 => ⟨((-12269/268435456), (4540583/1073741824)), (27682863/137438953472), by norm_num⟩
  | 9 => ⟨((544761/4294967296), (-5623295/8589934592)), (110218491/549755813888), by norm_num⟩
  | 10 => ⟨((-153999/4294967296), (1525465/17179869184)), (1760546221/8796093022208), by norm_num⟩
  | 11 => ⟨((120451/17179869184), (-723903/68719476736)), (1759595309/8796093022208), by norm_num⟩
  | 12 => ⟨((-306189/274877906944), (148415/137438953472)), (1759317229/8796093022208), by norm_num⟩
  | 13 => ⟨((83437/549755813888), (-101571/1099511627776)), (1759242525/8796093022208), by norm_num⟩
  | 14 => ⟨((-79939/4398046511104), (26045/4398046511104)), (1759223995/8796093022208), by norm_num⟩
  | 15 => ⟨((2129/1099511627776), (-641/4398046511104)), (1759219747/8796093022208), by norm_num⟩
  | 16 => ⟨((-1621/8796093022208), (-141/4398046511104)), (1759218833/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile027Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30399/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30399/1280))
  have he : value ((69/80), (30399/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1824451137/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((177827370594275/562949953421312), (-1176092976792927/2251799813685248)), (43480953/2251799813685248), by norm_num⟩
  | 1 => ⟨((-97067025/536870912), (1283940105/4294967296)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((222231049/4294967296), (-734882305/8589934592)), (15/4294967296), by norm_num⟩
  | 3 => ⟨((-169596349/17179869184), (560827825/34359738368)), (3/4294967296), by norm_num⟩
  | 4 => ⟨((776568037/549755813888), (-1283992745/549755813888)), (29/274877906944), by norm_num⟩
  | 5 => ⟨((-1389001/8589934592), (1175859895/4398046511104)), (7/549755813888), by norm_num⟩
  | 6 => ⟨((542730567/35184372088832), (-897361309/35184372088832)), (45/35184372088832), by norm_num⟩
  | 7 => ⟨((-177508543/140737488355328), (1173984353/562949953421312)), (31/281474976710656), by norm_num⟩
  | 8 => ⟨((101599667/1125899906842624), (-671947487/4503599627370496)), (19/2251799813685248), by norm_num⟩
  | 9 => ⟨((-103381489/18014398509481984), (683731885/72057594037927936)), (41/72057594037927936), by norm_num⟩
  | 10 => ⟨((757400833/2305843009213693952), (-1252301317/2305843009213693952)), (39/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-630559541/36893488147419103232), (521289725/18446744073709551616)), (67/36893488147419103232), by norm_num⟩
  | 12 => ⟨((3759481/4611686018427387904), (-795647903/590295810358705651712)), (53/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-169495247/4722366482869645213696), (1120986995/18889465931478580854784)), (77/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((110872157/75557863725914323419136), (-45829547/18889465931478580854784)), (13/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((-270759833/4835703278458516698824704), (895359183/9671406556917033397649408)), (33/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((309946873/154742504910672534362390528), (-32029513/9671406556917033397649408)), (39/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-1337586287535/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781208080698457/633825300114114700748351602688), (-793547015237/316912650057057350374175801344)), (23089/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946242865997811/19807040628566084398385987584), (-892699883247/19807040628566084398385987584)), (12989/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892431886794819/2475880078570760549798248448), (-948445741731/1237940039285380274899124224)), (27605/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774097673818929/154742504910672534362390528), (-1896783738875/154742504910672534362390528)), (3451/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((97017389614157/604462909807314587353088), (-889060136397/4835703278458516698824704)), (12943/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261172399761465/604462909807314587353088), (-1555740752045/604462909807314587353088)), (11327/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945832331374505/37778931862957161709568), (-2527864050581/75557863725914323419136)), (18409/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325110777647523/1180591620717411303424), (-1895710191367/4722366482869645213696)), (6905/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625439333360473/590295810358705651712), (-2606296245569/590295810358705651712)), (18993/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828461676486011/73786976294838206464), (-3257412376105/73786976294838206464)), (5937/9223372036854775808), by norm_num⟩
  | 7 => ⟨((914132309360745/4611686018427387904), (-3663959220289/9223372036854775808)), (13363/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399877431644737/288230376151711744), (-457896502501/144115188075855872)), (13369/288230376151711744), by norm_num⟩
  | 5 => ⟨((599705162114603/72057594037927936), (-3204389818719/144115188075855872)), (23409/72057594037927936), by norm_num⟩
  | 4 => ⟨((93679631631177/2251799813685248), (-4804813084851/36028797018963968)), (8785/4503599627370496), by norm_num⟩
  | 3 => ⟨((749145103613483/4503599627370496), (-3001457714577/4503599627370496)), (10993/1125899906842624), by norm_num⟩
  | 2 => ⟨((561493279255637/1125899906842624), (-2999131469949/1125899906842624)), (22021/562949953421312), by norm_num⟩
  | 1 => ⟨((1121520702090305/1125899906842624), (-8985759356915/1125899906842624)), (132479/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117104871276775/1125899906842624), (-8962477826975/562949953421312)), (266365/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117104871276775/1125899906842624), (-8962477826975/562949953421312)), (1016101841453170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((277023290838919/281474976710656), (-35569867546399/1125899906842624)), (537051/1125899906842624), by norm_num⟩
  | 2 => ⟨((272361076624943/281474976710656), (-70014619967707/1125899906842624)), (1091049/1125899906842624), by norm_num⟩
  | 3 => ⟨((1049815212499847/1125899906842624), (-33873805580759/281474976710656)), (561785/281474976710656), by norm_num⟩
  | 4 => ⟨((962566049199625/1125899906842624), (-252677782014693/1125899906842624)), (591429/140737488355328), by norm_num⟩
  | 5 => ⟨((766220276158611/1125899906842624), (-13501369708591/35184372088832)), (10213775/1125899906842624), by norm_num⟩
  | 6 => ⟨((177827370594275/562949953421312), (-1176092976792927/2251799813685248)), (43480953/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1824451137/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((647298339/9007199254740992), (-883773617/9007199254740992)), (897/4503599627370496), by norm_num⟩
  | 1 => ⟨((1090755949/9007199254740992), (-52874475/4503599627370496)), (2319/4503599627370496), by norm_num⟩
  | 2 => ⟨((788162985/18014398509481984), (364255993/9007199254740992)), (6351/9007199254740992), by norm_num⟩
  | 3 => ⟨((-24946847/72057594037927936), (1369081531/72057594037927936)), (48013/72057594037927936), by norm_num⟩
  | 4 => ⟨((-242040855/72057594037927936), (416299029/144115188075855872)), (35289/72057594037927936), by norm_num⟩
  | 5 => ⟨((-917776143/1152921504606846976), (-120247845/1152921504606846976)), (702749/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-614391385/9223372036854775808), (-891282163/9223372036854775808)), (1628593/9223372036854775808), by norm_num⟩
  | 7 => ⟨((235475769/73786976294838206464), (-127343751/9223372036854775808)), (7940463/73786976294838206464), by norm_num⟩
  | 8 => ⟨((22908271/18446744073709551616), (-52918413/73786976294838206464)), (22682889/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1114201197/9444732965739290427392), (39732139/1180591620717411303424)), (307198743/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((2626807/590295810358705651712), (145739555/18889465931478580854784)), (1153516841/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1959561/18889465931478580854784), (5109547/9444732965739290427392)), (1130763815/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-25039/1180591620717411303424), (194481/9444732965739290427392)), (1124530403/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-6673/4722366482869645213696), (4279/9444732965739290427392)), (1122966939/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-747/9444732965739290427392), (-87/18889465931478580854784)), (280651237/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((-73/18889465931478580854784), (-5/2361183241434822606848)), (280631761/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((-1/9444732965739290427392), (-1/4722366482869645213696)), (1122511369/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((792286239/281474976710656), (342667937/281474976710656)), (11977/281474976710656), by norm_num⟩
  | 1 => ⟨((-36081699/70368744177664), (481488559/140737488355328)), (24617/281474976710656), by norm_num⟩
  | 2 => ⟨((-876550607/1125899906842624), (143594549/562949953421312)), (140077/1125899906842624), by norm_num⟩
  | 3 => ⟨((-110291043/562949953421312), (954232891/4503599627370496)), (629355/4503599627370496), by norm_num⟩
  | 4 => ⟨((-74612771/562949953421312), (-423059967/9007199254740992)), (629821/4503599627370496), by norm_num⟩
  | 5 => ⟨((9686115/2251799813685248), (-117526593/4503599627370496)), (2333831/18014398509481984), by norm_num⟩
  | 6 => ⟨((1190668185/576460752303423488), (-141894415/576460752303423488)), (66881669/576460752303423488), by norm_num⟩
  | 7 => ⟨((238902885/2305843009213693952), (-401081075/4611686018427387904)), (961112615/9223372036854775808), by norm_num⟩
  | 8 => ⟨((163471289/4611686018427387904), (192082993/18446744073709551616)), (1771779985/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-4833665/18446744073709551616), (59775759/18446744073709551616)), (1684490205/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1432193/18446744073709551616), (743489/18446744073709551616)), (1640507637/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-75517/18446744073709551616), (92173/9223372036854775808)), (1620864549/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-17559/18446744073709551616), (-1373/18446744073709551616)), (806486501/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-213/18446744073709551616), (-71/4611686018427387904)), (1610089139/18446744073709551616), by norm_num⟩
  | 14 => ⟨((-49/18446744073709551616), (-11/18446744073709551616)), (1609121837/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-3/18446744073709551616), (-1/4611686018427387904)), (402205463/4611686018427387904), by norm_num⟩
  | 16 => ⟨(0, (-1/18446744073709551616)), (1608735361/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3169144859/1125899906842624), (1370671805/1125899906842624)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-577307269/1125899906842624), (3851908385/1125899906842624)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((-876550589/1125899906842624), (71797261/281474976710656)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((-220582085/1125899906842624), (238558239/1125899906842624)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-149225547/1125899906842624), (-52882517/1125899906842624)), (1/2147483648), by norm_num⟩
  | 5 => ⟨((4843065/1125899906842624), (-3672705/140737488355328)), (1/2147483648), by norm_num⟩
  | 6 => ⟨((145345/70368744177664), (-69285/281474976710656)), (1/2147483648), by norm_num⟩
  | 7 => ⟨((116653/1125899906842624), (-765/8796093022208)), (1/2147483648), by norm_num⟩
  | 8 => ⟨((39909/1125899906842624), (2931/281474976710656)), (1/2147483648), by norm_num⟩
  | 9 => ⟨((-295/1125899906842624), (57/17592186044416)), (1/2147483648), by norm_num⟩
  | 10 => ⟨((-87/1125899906842624), (45/1125899906842624)), (1/2147483648), by norm_num⟩
  | 11 => ⟨((-5/1125899906842624), (11/1125899906842624)), (1/2147483648), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/2147483648), by norm_num⟩
  | 13 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | 14 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | 15 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | 16 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨27,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨27,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(4827/1073741824)) (L:=(1810291405169565/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile027
