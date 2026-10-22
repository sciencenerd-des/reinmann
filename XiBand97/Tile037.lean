/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile037Gamma
import XiBand97.Tile037Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile037
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1082808813/36028797018963968), (-139917739/36028797018963968)), (4233/36028797018963968), by norm_num⟩
  | 1 => ⟨((-645243205/18014398509481984), (-31012649/1125899906842624)), (3783/18014398509481984), by norm_num⟩
  | 2 => ⟨((-461437965/36028797018963968), (-8697013/281474976710656)), (8209/36028797018963968), by norm_num⟩
  | 3 => ⟨((36553149/18014398509481984), (-1171779405/72057594037927936)), (809/4503599627370496), by norm_num⟩
  | 4 => ⟨((63937389/18014398509481984), (-693394405/144115188075855872)), (17113/144115188075855872), by norm_num⟩
  | 5 => ⟨((453922721/288230376151711744), (-208152679/288230376151711744)), (21873/288230376151711744), by norm_num⟩
  | 6 => ⟨((1911250363/4611686018427387904), (131411189/4611686018427387904)), (247905/4611686018427387904), by norm_num⟩
  | 7 => ⟨((662508847/9223372036854775808), (415380371/9223372036854775808)), (205489/4611686018427387904), by norm_num⟩
  | 8 => ⟨((34888675/4611686018427387904), (119858811/9223372036854775808)), (3049771/73786976294838206464), by norm_num⟩
  | 9 => ⟨((72278961/590295810358705651712), (347092133/147573952589676412928)), (11908803/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-627077525/4722366482869645213696), (89146853/295147905179352825856)), (189285091/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-603640979/18889465931478580854784), (508350891/18889465931478580854784)), (188979409/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-88215697/18889465931478580854784), (11417957/9444732965739290427392)), (1511293055/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((-19013145/37778931862957161709568), (-3514125/37778931862957161709568)), (377795633/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-1557451/37778931862957161709568), (-541833/18889465931478580854784)), (1511161665/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-90395/37778931862957161709568), (-73887/18889465931478580854784)), (1511157991/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-2159/37778931862957161709568), (-7317/18889465931478580854784)), (755578693/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile037Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-223390317/8388608), (914051219/33554432)), (3677/16777216), by norm_num⟩
  | 1 => ⟨((1030539751/33554432), (54112901/8388608)), (2047/8388608), by norm_num⟩
  | 2 => ⟨((-596427627/33554432), (-247379033/33554432)), (17267/67108864), by norm_num⟩
  | 3 => ⟨((497982161/67108864), (576326329/134217728)), (33897/134217728), by norm_num⟩
  | 4 => ⟨((-159960147/67108864), (-235541057/134217728)), (7973/33554432), by norm_num⟩
  | 5 => ⟨((10348559/16777216), (151500049/268435456)), (238429/1073741824), by norm_num⟩
  | 6 => ⟨((-35327209/268435456), (-80970963/536870912)), (453061/2147483648), by norm_num⟩
  | 7 => ⟨((3132407/134217728), (37043835/1073741824)), (1758755/8589934592), by norm_num⟩
  | 8 => ⟨((-1829567/536870912), (-3692901/536870912)), (27737007/137438953472), by norm_num⟩
  | 9 => ⟨((3361961/8589934592), (2598153/2147483648)), (110293371/549755813888), by norm_num⟩
  | 10 => ⟨((-504323/17179869184), (-1626143/8589934592)), (1760922029/8796093022208), by norm_num⟩
  | 11 => ⟨((-14935/34359738368), (1821085/68719476736)), (1759703213/8796093022208), by norm_num⟩
  | 12 => ⟨((182695/274877906944), (-915029/274877906944)), (1759345869/8796093022208), by norm_num⟩
  | 13 => ⟨((-10519/68719476736), (206265/549755813888)), (1759249565/8796093022208), by norm_num⟩
  | 14 => ⟨((110379/4398046511104), (-166093/4398046511104)), (1759225625/8796093022208), by norm_num⟩
  | 15 => ⟨((-14991/4398046511104), (7369/2199023255552)), (879610047/4398046511104), by norm_num⟩
  | 16 => ⟨((887/2199023255552), (-1117/4398046511104)), (1759218903/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile037Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33621/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33621/1280))
  have he : value ((69/80), (33621/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-63057041/4194304)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-536959569660921/1125899906842624), (-857819067157765/2251799813685248)), (60913293/2251799813685248), by norm_num⟩
  | 1 => ⟨((1172396979/4294967296), (7316255/33554432)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((-335519465/4294967296), (-33500543/536870912)), (21/4294967296), by norm_num⟩
  | 3 => ⟨((1024211091/68719476736), (818113553/68719476736)), (67/68719476736), by norm_num⟩
  | 4 => ⟨((-586222523/274877906944), (-468259517/274877906944)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((1073706307/4398046511104), (428824531/2199023255552)), (19/1099511627776), by norm_num⟩
  | 6 => ⟨((-409701233/17592186044416), (-654517675/35184372088832)), (15/8796093022208), by norm_num⟩
  | 7 => ⟨((1071993705/562949953421312), (428140539/281474976710656)), (81/562949953421312), by norm_num⟩
  | 8 => ⟨((-19174113/140737488355328), (-245052635/2251799813685248)), (3/281474976710656), by norm_num⟩
  | 9 => ⟨((624332237/72057594037927936), (249350289/36028797018963968)), (51/72057594037927936), by norm_num⟩
  | 10 => ⟨((-1143506833/2305843009213693952), (-913403929/2305843009213693952)), (3/72057594037927936), by norm_num⟩
  | 11 => ⟨((952004689/36893488147419103232), (11881827/576460752303423488)), (41/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-90815685/73786976294838206464), (-580329919/590295810358705651712)), (65/590295810358705651712), by norm_num⟩
  | 13 => ⟨((1023600529/18889465931478580854784), (817625849/18889465931478580854784)), (47/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-334784605/151115727451828646838272), (-534834711/302231454903657293676544)), (1/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((408787139/4835703278458516698824704), (653057363/9671406556917033397649408)), (5/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-467950855/154742504910672534362390528), (-747574281/309485009821345068724781056)), (47/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-3214323861847/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781201676241441/633825300114114700748351602688), (-3813910370259/633825300114114700748351602688)), (2893/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236559766995697/4951760157141521099596496896), (-4290439041257/39614081257132168796771975168)), (26043/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892423341874633/2475880078570760549798248448), (-4558359442937/2475880078570760549798248448)), (13839/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887044297766467/77371252455336267181195264), (-569762279887/19342813113834066795298816)), (13843/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776134578159523/4835703278458516698824704), (-4272939418453/9671406556917033397649408)), (6491/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261163890425721/604462909807314587353088), (-467318017499/75557863725914323419136)), (22727/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891649773067189/75557863725914323419136), (-3037306447237/37778931862957161709568)), (18473/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300431014276623/4722366482869645213696), (-4555503142507/4722366482869645213696)), (27723/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625421191609565/590295810358705651712), (-6263074283993/590295810358705651712)), (38141/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457109184000057/18446744073709551616), (-7827727862959/73786976294838206464)), (23855/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828233449751835/9223372036854775808), (-2201164701161/2305843009213693952)), (53719/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799737335311435/576460752303423488), (-4401368557177/576460752303423488)), (53777/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199375279703781/144115188075855872), (-3850114552233/72057594037927936)), (47119/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498812803931741/36028797018963968), (-2886500500563/9007199254740992)), (70807/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498198305564619/9007199254740992), (-14424882328259/9007199254740992)), (44367/4503599627370496), by norm_num⟩
  | 2 => ⟨((561435885950197/1125899906842624), (-7206703785923/1125899906842624)), (89073/2251799813685248), by norm_num⟩
  | 1 => ⟨((280322850254615/281474976710656), (-21591269023939/1125899906842624)), (134459/1125899906842624), by norm_num⟩
  | 0 => ⟨((558209167019531/562949953421312), (-10766559591337/281474976710656)), (4255/17592186044416), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558209167019531/562949953421312), (-10766559591337/281474976710656)), (16231536932343239/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((276342325842641/281474976710656), (-85407126862639/1125899906842624)), (70111/140737488355328), by norm_num⟩
  | 2 => ⟨((1078734363626483/1125899906842624), (-83849741659347/562949953421312)), (74151/70368744177664), by norm_num⟩
  | 3 => ⟨((1008566306526927/1125899906842624), (-5021072319541/17592186044416)), (1313429/562949953421312), by norm_num⟩
  | 4 => ⟨((811742720733717/1125899906842624), (-575719737312745/1125899906842624)), (6205699/1125899906842624), by norm_num⟩
  | 5 => ⟨((145427238577121/562949953421312), (-207539010841961/281474976710656)), (30589485/2251799813685248), by norm_num⟩
  | 6 => ⟨((-536959569660921/1125899906842624), (-857819067157765/2251799813685248)), (60913293/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-63057041/4194304)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((115776833/9007199254740992), (239611527/18014398509481984)), (3665/36028797018963968), by norm_num⟩
  | 1 => ⟨((-55335427/72057594037927936), (1381223207/72057594037927936)), (8651/36028797018963968), by norm_num⟩
  | 2 => ⟨((-1056129927/144115188075855872), (232916167/36028797018963968)), (5719/18014398509481984), by norm_num⟩
  | 3 => ⟨((-935015567/288230376151711744), (-157467557/576460752303423488)), (86523/288230376151711744), by norm_num⟩
  | 4 => ⟨((-289337823/576460752303423488), (-713127733/1152921504606846976)), (263987/1152921504606846976), by norm_num⟩
  | 5 => ⟨((169135417/9223372036854775808), (-1395545587/9223372036854775808)), (1438423/9223372036854775808), by norm_num⟩
  | 6 => ⟨((695008339/36893488147419103232), (-66331513/4611686018427387904)), (488679/4611686018427387904), by norm_num⟩
  | 7 => ⟨((224552411/73786976294838206464), (126399991/295147905179352825856)), (46809535/590295810358705651712), by norm_num⟩
  | 8 => ⟨((120508767/590295810358705651712), (636575031/2361183241434822606848)), (2489475/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-36618313/9444732965739290427392), (599500873/18889465931478580854784)), (74334925/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-37893715/18889465931478580854784), (1990943/1180591620717411303424)), (1160667141/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-3542637/18889465931478580854784), (-78483/18889465931478580854784)), (1152013353/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-10679/1180591620717411303424), (-35985/4722366482869645213696)), (1149644739/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-795/4722366482869645213696), (-6099/9444732965739290427392)), (287262647/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((183/18889465931478580854784), (-631/18889465931478580854784)), (1148912905/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((23/18889465931478580854784), (-3/2361183241434822606848)), (287220809/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((1/9444732965739290427392), (-1/18889465931478580854784)), (1148877257/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-396673191/562949953421312), (-9148081/2251799813685248)), (25249/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1736057289/9007199254740992), (-179911985/4503599627370496)), (247405/9007199254740992), by norm_num⟩
  | 2 => ⟨((-1164619053/4503599627370496), (-268472361/2251799813685248)), (194563/4503599627370496), by norm_num⟩
  | 3 => ⟨((182751587/9007199254740992), (-999615661/9007199254740992)), (460011/9007199254740992), by norm_num⟩
  | 4 => ⟨((134809473/9007199254740992), (-195915525/72057594037927936)), (1823453/36028797018963968), by norm_num⟩
  | 5 => ⟨((463246031/288230376151711744), (-757093521/576460752303423488)), (3209217/72057594037927936), by norm_num⟩
  | 6 => ⟨((419186499/576460752303423488), (148858713/576460752303423488)), (42488547/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-65037829/4611686018427387904), (475433531/4611686018427387904)), (139736713/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-382140679/73786976294838206464), (50182441/36893488147419103232)), (1907445331/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-10727143/36893488147419103232), (7280143/18446744073709551616)), (214834545/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-5931121/73786976294838206464), (-1365009/73786976294838206464)), (1623839801/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-1235/9223372036854775808), (-352541/73786976294838206464)), (1581367717/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-791/36893488147419103232), (-7061/73786976294838206464)), (97760781/4611686018427387904), by norm_num⟩
  | 13 => ⟨((395/73786976294838206464), (-1479/73786976294838206464)), (778906457/36893488147419103232), by norm_num⟩
  | 14 => ⟨((39/36893488147419103232), (1/18446744073709551616)), (777823285/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-1/73786976294838206464), (1/73786976294838206464)), (1554962567/73786976294838206464), by norm_num⟩
  | 16 => ⟨(0, 0), (777380789/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-793346361/1125899906842624), (-2287033/562949953421312)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-217007167/1125899906842624), (-11244499/281474976710656)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-72788687/281474976710656), (-134236197/1125899906842624)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((22843949/1125899906842624), (-31237987/281474976710656)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((1053199/70368744177664), (-47831/17592186044416)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((1809555/1125899906842624), (-1478697/1125899906842624)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((818723/1125899906842624), (145369/562949953421312)), (1/8589934592), by norm_num⟩
  | 7 => ⟨((-7939/562949953421312), (116073/1125899906842624)), (1/8589934592), by norm_num⟩
  | 8 => ⟨((-5831/1125899906842624), (1531/1125899906842624)), (1/8589934592), by norm_num⟩
  | 9 => ⟨((-327/1125899906842624), (111/281474976710656)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-91/1125899906842624), (-21/1125899906842624)), (1/8589934592), by norm_num⟩
  | 11 => ⟨(0, (-5/1125899906842624)), (1/8589934592), by norm_num⟩
  | 12 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 13 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 14 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 15 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 16 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨37,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨37,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(537/1073741824)) (L:=(103987222525853/147573952589676412928)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile037
