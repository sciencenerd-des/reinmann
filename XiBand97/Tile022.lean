/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile022Gamma
import XiBand97.Tile022Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile022
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-16589753/562949953421312), (-635047173/1125899906842624)), (115/140737488355328), by norm_num⟩
  | 1 => ⟨((216127073/562949953421312), (-99010607/140737488355328)), (2109/1125899906842624), by norm_num⟩
  | 2 => ⟨((548660439/1125899906842624), (-19878219/70368744177664)), (2465/1125899906842624), by norm_num⟩
  | 3 => ⟨((588540473/2251799813685248), (4120129/1125899906842624)), (3849/2251799813685248), by norm_num⟩
  | 4 => ⟨((693545335/9007199254740992), (421438043/9007199254740992)), (9081/9007199254740992), by norm_num⟩
  | 5 => ⟨((26608653/2251799813685248), (388820233/18014398509481984)), (17597/36028797018963968), by norm_num⟩
  | 6 => ⟨((-11088135/144115188075855872), (1598640709/288230376151711744)), (61449/288230376151711744), by norm_num⟩
  | 7 => ⟨((-606766033/1152921504606846976), (531631599/576460752303423488)), (28105/288230376151711744), by norm_num⟩
  | 8 => ⟨((-344675903/2305843009213693952), (430876167/4611686018427387904)), (65475/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-1897790225/73786976294838206464), (73382275/36893488147419103232)), (204689/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-920116189/295147905179352825856), (-189713063/147573952589676412928)), (12112213/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-623689667/2361183241434822606848), (-175843213/590295810358705651712)), (94978335/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-228390067/18889465931478580854784), (-97094915/2361183241434822606848)), (756428619/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((22080875/37778931862957161709568), (-79383073/18889465931478580854784)), (1511473545/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((7643445/37778931862957161709568), (-12555331/37778931862957161709568)), (1511212313/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((507531/18889465931478580854784), (-370583/18889465931478580854784)), (188895785/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((1525/590295810358705651712), (-3147/4722366482869645213696)), (755579333/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile022Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-138260481/16777216), (1437594321/67108864)), (14253/67108864), by norm_num⟩
  | 1 => ⟨((219530219/16777216), (-267204583/67108864)), (3853/16777216), by norm_num⟩
  | 2 => ⟨((-587956725/67108864), (249874609/67108864)), (16113/67108864), by norm_num⟩
  | 3 => ⟨((277743359/67108864), (-211583425/134217728)), (7985/33554432), by norm_num⟩
  | 4 => ⟨((-386833463/268435456), (107323761/268435456)), (244693/1073741824), by norm_num⟩
  | 5 => ⟨((106178065/268435456), (-15410675/268435456)), (465425/2147483648), by norm_num⟩
  | 6 => ⟨((-47841489/536870912), (-299645/536870912)), (1791107/8589934592), by norm_num⟩
  | 7 => ⟨((9068993/536870912), (3221917/1073741824)), (1750155/8589934592), by norm_num⟩
  | 8 => ⟨((-1467061/536870912), (-2219467/2147483648)), (110752443/549755813888), by norm_num⟩
  | 9 => ⟨((3255491/8589934592), (2048293/8589934592)), (110230075/549755813888), by norm_num⟩
  | 10 => ⟨((-192179/4294967296), (-751783/17179869184)), (1760624557/8796093022208), by norm_num⟩
  | 11 => ⟨((300091/68719476736), (465583/68719476736)), (1759623853/8796093022208), by norm_num⟩
  | 12 => ⟨((-87987/274877906944), (-7815/8589934592)), (1759325965/8796093022208), by norm_num⟩
  | 13 => ⟨((11241/1099511627776), (118137/1099511627776)), (1759244989/8796093022208), by norm_num⟩
  | 14 => ⟨((61/34359738368), (-12337/1099511627776)), (1759224635/8796093022208), by norm_num⟩
  | 15 => ⟨((-4019/8796093022208), (4545/4398046511104)), (1759219895/8796093022208), by norm_num⟩
  | 16 => ⟨((37/549755813888), (-91/1099511627776)), (1759218865/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile022Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28609/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28609/1280))
  have he : value ((69/80), (28609/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1717021039/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1339380217500689/2251799813685248), (-308571714110239/2251799813685248)), (12735917/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1462200703/4294967296), (336867583/4294967296)), (31/4294967296), by norm_num⟩
  | 2 => ⟨((418456211/4294967296), (-192811195/8589934592)), (19/8589934592), by norm_num⟩
  | 3 => ⟨((-638692441/34359738368), (294288983/68719476736)), (31/68719476736), by norm_num⟩
  | 4 => ⟨((1462260651/549755813888), (-168440697/274877906944)), (19/274877906944), by norm_num⟩
  | 5 => ⟨((-1339114775/4398046511104), (9640955/137438953472)), (37/4398046511104), by norm_num⟩
  | 6 => ⟨((1021949803/35184372088832), (-235440839/35184372088832)), (15/17592186044416), by norm_num⟩
  | 7 => ⟨((-334244709/140737488355328), (154009237/281474976710656)), (41/562949953421312), by norm_num⟩
  | 8 => ⟨((1530479631/9007199254740992), (-352597953/9007199254740992)), (49/9007199254740992), by norm_num⟩
  | 9 => ⟨((-97332543/9007199254740992), (179390851/72057594037927936)), (13/36028797018963968), by norm_num⟩
  | 10 => ⟨((1426169227/2305843009213693952), (-164283255/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-1187329845/36893488147419103232), (68385437/9223372036854775808)), (43/36893488147419103232), by norm_num⟩
  | 12 => ⟨((906114639/590295810358705651712), (-52188569/147573952589676412928)), (17/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-638311697/9444732965739290427392), (294113549/18889465931478580854784)), (25/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((1670158803/604462909807314587353088), (-192388897/302231454903657293676544)), (17/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-1019669705/9671406556917033397649408), (117457771/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((1167246385/309485009821345068724781056), (-134457421/154742504910672534362390528)), (53/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-147477147129/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222651169598121/79228162514264337593543950336), (-87493458187/158456325028528675187087900672)), (23059/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892487245502771/39614081257132168796771975168), (-196851489297/19807040628566084398385987584)), (25943/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892433589375447/2475880078570760549798248448), (-418288331361/2475880078570760549798248448)), (6891/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774099482673925/154742504910672534362390528), (-418264614133/154742504910672534362390528)), (27565/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552280042527475/9671406556917033397649408), (-392097877967/9671406556917033397649408)), (25843/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78823380953435/37778931862957161709568), (-343060447431/604462909807314587353088)), (11307/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891667629535321/75557863725914323419136), (-557425989203/75557863725914323419136)), (36747/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300445520797131/4722366482869645213696), (-418028162999/4722366482869645213696)), (13781/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812721474067041/295147905179352825856), (-287360786297/295147905179352825856)), (9475/147573952589676412928), by norm_num⟩
  | 8 => ⟨((914233322963609/36893488147419103232), (-718301252339/73786976294838206464)), (47377/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828270829214305/9223372036854775808), (-807950450521/9223372036854775808)), (6663/1152921504606846976), by norm_num⟩
  | 6 => ⟨((799758355792007/576460752303423488), (-403888705709/576460752303423488)), (53309/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199417306985241/144115188075855872), (-176652653133/36028797018963968)), (46651/144115188075855872), by norm_num⟩
  | 4 => ⟨((374721580215501/9007199254740992), (-1059526790183/36028797018963968)), (69989/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498308519253027/9007199254740992), (-82732985891/562949953421312)), (87507/9007199254740992), by norm_num⟩
  | 2 => ⟨((2246018861677121/4503599627370496), (-2645414454123/4503599627370496)), (87537/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121566393638775/1125899906842624), (-3963022604617/2251799813685248)), (262765/2251799813685248), by norm_num⟩
  | 0 => ⟨((2234483360920475/2251799813685248), (-3952835422833/1125899906842624)), (263075/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((2234483360920475/2251799813685248), (-3952835422833/1125899906842624)), (1003551487449264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1108636158564145/1125899906842624), (-7844875842957/1125899906842624)), (1047903/2251799813685248), by norm_num⟩
  | 2 => ⟨((2183164919953513/2251799813685248), (-7724588097123/562949953421312)), (1039137/1125899906842624), by norm_num⟩
  | 3 => ⟨((264524755407575/281474976710656), (-59913140243599/2251799813685248)), (1021723/562949953421312), by norm_num⟩
  | 4 => ⟨((993584009273661/1125899906842624), (-56305213890929/1125899906842624)), (7899043/2251799813685248), by norm_num⟩
  | 5 => ⟨((1748004241571655/2251799813685248), (-198752872509403/2251799813685248)), (7365771/1125899906842624), by norm_num⟩
  | 6 => ⟨((1339380217500689/2251799813685248), (-308571714110239/2251799813685248)), (12735917/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1717021039/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-427031865/4503599627370496), (-1492728365/4503599627370496)), (681/1125899906842624), by norm_num⟩
  | 1 => ⟨((209669087/1125899906842624), (-633544751/2251799813685248)), (7791/4503599627370496), by norm_num⟩
  | 2 => ⟨((1441933819/9007199254740992), (-175410065/9007199254740992)), (22543/9007199254740992), by norm_num⟩
  | 3 => ⟨((331408863/9007199254740992), (611610265/18014398509481984)), (5455/2251799813685248), by norm_num⟩
  | 4 => ⟨((-67234509/144115188075855872), (815049129/72057594037927936)), (254701/144115188075855872), by norm_num⟩
  | 5 => ⟨((-899665993/576460752303423488), (351644779/288230376151711744)), (150377/144115188075855872), by norm_num⟩
  | 6 => ⟨((-314117463/1152921504606846976), (-254636939/4611686018427387904)), (1220293/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-289529289/18446744073709551616), (-1027303515/36893488147419103232)), (4592615/18446744073709551616), by norm_num⟩
  | 8 => ⟨((293542113/295147905179352825856), (-106224527/36893488147419103232)), (36364847/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1043108169/4722366482869645213696), (-114962741/1180591620717411303424)), (353663217/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((280075037/18889465931478580854784), (52919577/9444732965739290427392)), (553340171/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((16535171/37778931862957161709568), (28015449/37778931862957161709568)), (506876067/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((49683/18889465931478580854784), (1551899/37778931862957161709568)), (988335497/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-8449/18889465931478580854784), (82265/37778931862957161709568)), (1963935071/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-1511/18889465931478580854784), (4343/37778931862957161709568)), (980493667/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-269/37778931862957161709568), (13/4722366482869645213696)), (122522043/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((-11/37778931862957161709568), (-3/37778931862957161709568)), (490056211/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69328361/8796093022208), (98553851/140737488355328)), (3817/35184372088832), by norm_num⟩
  | 1 => ⟨((135947027/70368744177664), (330497931/140737488355328)), (72859/281474976710656), by norm_num⟩
  | 2 => ⟨((174464097/70368744177664), (483507149/281474976710656)), (50551/140737488355328), by norm_num⟩
  | 3 => ⟨((-72088051/140737488355328), (436912941/281474976710656)), (28823/70368744177664), by norm_num⟩
  | 4 => ⟨((-1601116489/4503599627370496), (-64200821/1125899906842624)), (1829771/4503599627370496), by norm_num⟩
  | 5 => ⟨((-132257981/36028797018963968), (-590925515/18014398509481984)), (3342353/9007199254740992), by norm_num⟩
  | 6 => ⟨((-54118539/36028797018963968), (-1065255105/576460752303423488)), (188142475/576460752303423488), by norm_num⟩
  | 7 => ⟨((126813751/576460752303423488), (-830489271/1152921504606846976)), (166162741/576460752303423488), by norm_num⟩
  | 8 => ⟨((176801867/2305843009213693952), (4763463/576460752303423488)), (18910695/72057594037927936), by norm_num⟩
  | 9 => ⟨((3457379/4611686018427387904), (6122443/2305843009213693952)), (571233911/2305843009213693952), by norm_num⟩
  | 10 => ⟨((935311/4611686018427387904), (117207/1152921504606846976)), (554440997/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-13703/4611686018427387904), (119109/4611686018427387904)), (547064237/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-1671/2305843009213693952), (547/2305843009213693952)), (544145899/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-3/144115188075855872), (109/2305843009213693952)), (543093865/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-1/288230376151711744), (-3/2305843009213693952)), (542744951/2305843009213693952), by norm_num⟩
  | 15 => ⟨((1/2305843009213693952), 0), (271318819/1152921504606846976), by norm_num⟩
  | 16 => ⟨(0, 0), (271303419/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((277313427/35184372088832), (788430995/1125899906842624)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((67973507/35184372088832), (2643983405/1125899906842624)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((2791425361/1125899906842624), (1934028509/1125899906842624)), (1/1073741824), by norm_num⟩
  | 3 => ⟨((-288352203/562949953421312), (1747651719/1125899906842624)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((-25017445/70368744177664), (-32100419/562949953421312)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((-64579/17592186044416), (-18466417/562949953421312)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((-845605/562949953421312), (-1040289/562949953421312)), (1/1073741824), by norm_num⟩
  | 7 => ⟨((247683/1125899906842624), (-405513/562949953421312)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((86329/1125899906842624), (9303/1125899906842624)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((211/281474976710656), (2989/1125899906842624)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((57/281474976710656), (57/562949953421312)), (1/1073741824), by norm_num⟩
  | 11 => ⟨((-3/1125899906842624), (29/1125899906842624)), (1/1073741824), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/1073741824), by norm_num⟩
  | 13 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 14 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 15 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 16 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨22,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨22,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(6745/1073741824)) (L:=(9341748572215921/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile022
