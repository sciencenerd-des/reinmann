/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile035Gamma
import XiBand97.Tile035Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile035
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-172548867/4503599627370496), (461503951/18014398509481984)), (1115/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1227832113/18014398509481984), (9086533/2251799813685248)), (4015/18014398509481984), by norm_num⟩
  | 2 => ⟨((-403914687/9007199254740992), (-406502363/18014398509481984)), (1089/4503599627370496), by norm_num⟩
  | 3 => ⟨((-485627227/36028797018963968), (-366914173/18014398509481984)), (6849/36028797018963968), by norm_num⟩
  | 4 => ⟨((-89767039/144115188075855872), (-635814175/72057594037927936)), (17953/144115188075855872), by norm_num⟩
  | 5 => ⟨((155247991/144115188075855872), (-1328452341/576460752303423488)), (2829/36028797018963968), by norm_num⟩
  | 6 => ⟨((562628597/1152921504606846976), (-825135303/2305843009213693952)), (15783/288230376151711744), by norm_num⟩
  | 7 => ⟨((1118861875/9223372036854775808), (-78525331/4611686018427387904)), (207031/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1495655913/73786976294838206464), (134647931/18446744073709551616)), (1528561/36893488147419103232), by norm_num⟩
  | 9 => ⟨((336094017/147573952589676412928), (45201831/18446744073709551616)), (2979167/73786976294838206464), by norm_num⟩
  | 10 => ⟨((152585505/1180591620717411303424), (526772409/1180591620717411303424)), (47328861/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-191638315/18889465931478580854784), (1084384059/18889465931478580854784)), (755944225/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-73335913/18889465931478580854784), (204931285/37778931862957161709568)), (755651859/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-5766719/9444732965739290427392), (13036565/37778931862957161709568)), (377796127/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-641559/9444732965739290427392), (233385/37778931862957161709568)), (1511162005/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-221267/37778931862957161709568), (-73637/37778931862957161709568)), (1511158047/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-7413/18889465931478580854784), (-6519/18889465931478580854784)), (755578697/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile035Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-308879247/16777216), (903692101/67108864)), (7325/33554432), by norm_num⟩
  | 1 => ⟨((569616179/33554432), (702921435/33554432)), (8133/33554432), by norm_num⟩
  | 2 => ⟨((-60678241/8388608), (-526569361/33554432)), (8557/33554432), by norm_num⟩
  | 3 => ⟨((144287969/67108864), (126267853/16777216)), (33657/134217728), by norm_num⟩
  | 4 => ⟨((-55527413/134217728), (-22463761/8388608)), (126947/536870912), by norm_num⟩
  | 5 => ⟨((7238151/268435456), (6383307/8388608)), (475553/2147483648), by norm_num⟩
  | 6 => ⟨((8370215/536870912), (-48312387/268435456)), (1809843/8589934592), by norm_num⟩
  | 7 => ⟨((-8615991/1073741824), (4874009/134217728)), (1757763/8589934592), by norm_num⟩
  | 8 => ⟨((5126225/2147483648), (-13622353/2147483648)), (27731055/137438953472), by norm_num⟩
  | 9 => ⟨((-146615/268435456), (8303739/8589934592)), (110284987/549755813888), by norm_num⟩
  | 10 => ⟨((223561/2147483648), (-2210067/17179869184)), (1760877485/8796093022208), by norm_num⟩
  | 11 => ⟨((-588835/34359738368), (509511/34359738368)), (1759689773/8796093022208), by norm_num⟩
  | 12 => ⟨((341691/137438953472), (-198289/137438953472)), (1759341773/8796093022208), by norm_num⟩
  | 13 => ⟨((-353783/1099511627776), (60349/549755813888)), (1759248517/8796093022208), by norm_num⟩
  | 14 => ⟨((164601/4398046511104), (-20339/4398046511104)), (1759225381/8796093022208), by norm_num⟩
  | 15 => ⟨((-1079/274877906944), (-197/549755813888)), (219902505/1099511627776), by norm_num⟩
  | 16 => ⟨((3263/8796093022208), (527/4398046511104)), (1759218891/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile035Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6581/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6581/256))
  have he : value ((69/80), (6581/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1974853273/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-374684447366957/1125899906842624), (-1152216181706577/2251799813685248)), (30158165/1125899906842624), by norm_num⟩
  | 1 => ⟨((818085641/4294967296), (314468455/1073741824)), (69/4294967296), by norm_num⟩
  | 2 => ⟨((-468243541/8589934592), (-719962877/8589934592)), (21/4294967296), by norm_num⟩
  | 3 => ⟨((714683167/68719476736), (549442015/34359738368)), (67/68719476736), by norm_num⟩
  | 4 => ⟨((-204529795/137438953472), (-1257925391/549755813888)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((749220381/4398046511104), (143998479/549755813888)), (19/1099511627776), by norm_num⟩
  | 6 => ⟨((-285884987/17592186044416), (-879143267/35184372088832)), (15/8796093022208), by norm_num⟩
  | 7 => ⟨((748025345/562949953421312), (35942199/17592186044416)), (81/562949953421312), by norm_num⟩
  | 8 => ⟨((-107035871/1125899906842624), (-329152875/2251799813685248)), (3/281474976710656), by norm_num⟩
  | 9 => ⟨((217826063/36028797018963968), (669850903/72057594037927936)), (51/72057594037927936), by norm_num⟩
  | 10 => ⟨((-398963207/1152921504606846976), (-1226877357/2305843009213693952)), (3/72057594037927936), by norm_num⟩
  | 11 => ⟨((664298337/36893488147419103232), (255353305/9223372036854775808)), (41/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-15842545/18446744073709551616), (-389747413/295147905179352825856)), (1/9223372036854775808), by norm_num⟩
  | 13 => ⟨((357128561/9444732965739290427392), (137278619/2361183241434822606848)), (23/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-467217985/302231454903657293676544), (-359193001/151115727451828646838272)), (31/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((142623571/2417851639229258349412352), (219295447/2417851639229258349412352)), (39/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-653061857/309485009821345068724781056), (-62758513/19342813113834066795298816)), (23/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-2797271066477/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781203555843149/633825300114114700748351602688), (-103720696671/19807040628566084398385987584)), (5783/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892480365274167/39614081257132168796771975168), (-1866883079985/19807040628566084398385987584)), (26029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118276615603771/154742504910672534362390528), (-991731274563/618970019642690137449562112)), (13831/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774091259851459/154742504910672534362390528), (-1983349184393/77371252455336267181195264)), (27669/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776135910204071/4835703278458516698824704), (-1859269362575/4835703278458516698824704)), (12973/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261166387765329/604462909807314587353088), (-1626740140753/302231454903657293676544)), (22711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891654142923317/75557863725914323419136), (-2643226580575/37778931862957161709568)), (18459/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650217282163345/2361183241434822606848), (-991110970879/1180591620717411303424)), (6925/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625426515882371/590295810358705651712), (-5450466432923/590295810358705651712)), (38107/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828444055570243/73786976294838206464), (-6812116433087/73786976294838206464)), (47663/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914121298627163/4611686018427387904), (-1915575171705/2305843009213693952)), (13415/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599484958864257/1152921504606846976), (-7660635991083/1152921504606846976)), (26855/576460752303423488), by norm_num⟩
  | 5 => ⟨((599692782282855/72057594037927936), (-6701181208679/144115188075855872)), (11763/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498830794820369/36028797018963968), (-10048014999955/36028797018963968)), (35345/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498225276618197/9007199254740992), (-12553430290079/9007199254740992)), (88559/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122905458888899/2251799813685248), (-195992493245/35184372088832)), (44427/1125899906842624), by norm_num⟩
  | 1 => ⟨((560679347076201/562949953421312), (-2348800577235/140737488355328)), (67009/562949953421312), by norm_num⟩
  | 0 => ⟨((558309903363893/562949953421312), (-37480724228571/1125899906842624)), (270993/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558309903363893/562949953421312), (-37480724228571/1125899906842624)), (1033756260398482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1106168479559333/1125899906842624), (-4646474210293/70368744177664)), (277781/562949953421312), by norm_num⟩
  | 2 => ⟨((540936955756679/562949953421312), (-9130089240215/70368744177664)), (1165021/1125899906842624), by norm_num⟩
  | 3 => ⟨((1020615926752231/1125899906842624), (-280738429375373/1125899906842624)), (1270623/562949953421312), by norm_num⟩
  | 4 => ⟨((855176200264797/1125899906842624), (-508972619200975/1125899906842624)), (2937261/562949953421312), by norm_num⟩
  | 5 => ⟨((419462870129759/1125899906842624), (-773179334826877/1125899906842624)), (14235231/1125899906842624), by norm_num⟩
  | 6 => ⟨((-374684447366957/1125899906842624), (-1152216181706577/2251799813685248)), (30158165/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1974853273/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((931666597/36028797018963968), (199581543/18014398509481984)), (3829/36028797018963968), by norm_num⟩
  | 1 => ⟨((358350289/36028797018963968), (979681919/36028797018963968)), (9045/36028797018963968), by norm_num⟩
  | 2 => ⟨((-14753063/2251799813685248), (471149499/36028797018963968)), (5987/18014398509481984), by norm_num⟩
  | 3 => ⟨((-1332701377/288230376151711744), (400646311/288230376151711744)), (90479/288230376151711744), by norm_num⟩
  | 4 => ⟨((-146206755/144115188075855872), (-167696501/288230376151711744)), (4289/18014398509481984), by norm_num⟩
  | 5 => ⟨((-242563981/4611686018427387904), (-991167175/4611686018427387904)), (740537/4611686018427387904), by norm_num⟩
  | 6 => ⟨((336078535/18446744073709551616), (-264516971/9223372036854775808)), (1985333/18446744073709551616), by norm_num⟩
  | 7 => ⟨((627423475/147573952589676412928), (-261103923/295147905179352825856)), (11718583/147573952589676412928), by norm_num⟩
  | 8 => ⟨((925133481/2361183241434822606848), (306485149/1180591620717411303424)), (157985045/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((171167141/18889465931478580854784), (805370451/18889465931478580854784)), (1173763349/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-17111941/9444732965739290427392), (28200667/9444732965739290427392)), (571712229/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-548525/2361183241434822606848), (687095/9444732965739290427392)), (1134266777/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-131283/9444732965739290427392), (-12649/2361183241434822606848)), (1131757913/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-549/1180591620717411303424), (-6341/9444732965739290427392)), (1131128045/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-39/9444732965739290427392), (-197/4722366482869645213696)), (1130981993/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((7/9444732965739290427392), (-19/9444732965739290427392)), (282737627/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((1/9444732965739290427392), (-1/18889465931478580854784)), (1130944163/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1407983187/2251799813685248), (324814553/2251799813685248)), (25787/2251799813685248), by norm_num⟩
  | 1 => ⟨((-96374951/281474976710656), (817646289/2251799813685248)), (32757/1125899906842624), by norm_num⟩
  | 2 => ⟨((-528547511/1125899906842624), (-163213151/1125899906842624)), (101913/2251799813685248), by norm_num⟩
  | 3 => ⟨((18531749/2251799813685248), (-77374667/562949953421312)), (488181/9007199254740992), by norm_num⟩
  | 4 => ⟨((260013445/36028797018963968), (-612559559/72057594037927936)), (1971887/36028797018963968), by norm_num⟩
  | 5 => ⟨((734809493/288230376151711744), (-645067447/144115188075855872)), (14204979/288230376151711744), by norm_num⟩
  | 6 => ⟨((673677909/576460752303423488), (342285245/1152921504606846976)), (6038597/144115188075855872), by norm_num⟩
  | 7 => ⟨((-20115363/4611686018427387904), (138329829/1152921504606846976)), (163796735/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-71013983/36893488147419103232), (56728767/18446744073709551616)), (1151232359/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-28612529/73786976294838206464), (34091099/36893488147419103232)), (2122122715/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-997661/9223372036854775808), (-284245/18446744073709551616)), (508315221/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-33349/36893488147419103232), (-18699/4611686018427387904)), (997148803/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-3769/18446744073709551616), (-4811/36893488147419103232)), (247355887/9223372036854775808), by norm_num⟩
  | 13 => ⟨((15/4611686018427387904), (-2165/73786976294838206464)), (1973239159/73786976294838206464), by norm_num⟩
  | 14 => ⟨((33/36893488147419103232), (-3/4611686018427387904)), (61604959/2305843009213693952), by norm_num⟩
  | 15 => ⟨((9/73786976294838206464), (-7/73786976294838206464)), (1970772063/73786976294838206464), by norm_num⟩
  | 16 => ⟨((1/36893488147419103232), (1/73786976294838206464)), (1970601099/73786976294838206464), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-703991585/1125899906842624), (81203623/562949953421312)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-385499835/1125899906842624), (408823129/1125899906842624)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-16517109/35184372088832), (-163213171/1125899906842624)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((9265867/1125899906842624), (-154749329/1125899906842624)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((4062713/562949953421312), (-9571247/1125899906842624)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((717587/281474976710656), (-5039587/1125899906842624)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((657889/562949953421312), (167131/562949953421312)), (1/8589934592), by norm_num⟩
  | 7 => ⟨((-4911/1125899906842624), (135089/1125899906842624)), (1/8589934592), by norm_num⟩
  | 8 => ⟨((-2167/1125899906842624), (1731/562949953421312)), (1/8589934592), by norm_num⟩
  | 9 => ⟨((-437/1125899906842624), (65/70368744177664)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-61/562949953421312), (-17/1125899906842624)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((-1/1125899906842624), (-5/1125899906842624)), (1/8589934592), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨35,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨35,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(573/536870912)) (L:=(189394325939869/295147905179352825856)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile035
