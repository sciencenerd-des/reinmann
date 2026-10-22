/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile028Gamma
import XiBand97.Tile028Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile028
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1320624767/9007199254740992), (614391541/9007199254740992)), (2021/9007199254740992), by norm_num⟩
  | 1 => ⟨((592317379/4503599627370496), (437665805/2251799813685248)), (501/1125899906842624), by norm_num⟩
  | 2 => ⟨((90895863/9007199254740992), (759191001/4503599627370496)), (4425/9007199254740992), by norm_num⟩
  | 3 => ⟨((-163667617/4503599627370496), (1290671345/18014398509481984)), (6833/18014398509481984), by norm_num⟩
  | 4 => ⟨((-857263137/36028797018963968), (560037673/36028797018963968)), (8421/36028797018963968), by norm_num⟩
  | 5 => ⟨((-1147193677/144115188075855872), (18137827/36028797018963968)), (9317/72057594037927936), by norm_num⟩
  | 6 => ⟨((-962738383/576460752303423488), (-57314341/72057594037927936)), (42973/576460752303423488), by norm_num⟩
  | 7 => ⟨((-493648131/2305843009213693952), (-680863107/2305843009213693952)), (118793/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-79075925/9223372036854775808), (-1140637831/18446744073709551616)), (100021/2305843009213693952), by norm_num⟩
  | 9 => ⟨((465943381/147573952589676412928), (-81922213/9223372036854775808)), (188547/4611686018427387904), by norm_num⟩
  | 10 => ⟨((271919549/295147905179352825856), (-129471415/147573952589676412928)), (47471161/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((698812121/4722366482869645213696), (-109785685/2361183241434822606848)), (378218305/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((322519951/18889465931478580854784), (90668873/37778931862957161709568)), (377875043/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((6998929/4722366482869645213696), (17974857/18889465931478580854784)), (1511220939/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((3458863/37778931862957161709568), (5253757/37778931862957161709568)), (755584163/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((49003/18889465931478580854784), (544987/37778931862957161709568)), (755579539/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-9645/37778931862957161709568), (5577/4722366482869645213696)), (1511157553/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile028Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((464022615/67108864), (709043055/33554432)), (14419/67108864), by norm_num⟩
  | 1 => ⟨((-925550651/67108864), (-240681037/134217728)), (15657/67108864), by norm_num⟩
  | 2 => ⟨((1508994737/134217728), (255823961/67108864)), (16329/67108864), by norm_num⟩
  | 3 => ⟨((-687312617/134217728), (-174663019/67108864)), (16109/67108864), by norm_num⟩
  | 4 => ⟨((27851473/16777216), (152437405/134217728)), (122835/536870912), by norm_num⟩
  | 5 => ⟨((-111299927/268435456), (-50019399/134217728)), (466057/2147483648), by norm_num⟩
  | 6 => ⟨((5558533/67108864), (26519547/268435456)), (1791187/8589934592), by norm_num⟩
  | 7 => ⟨((-14334451/1073741824), (-5905547/268435456)), (1749819/8589934592), by norm_num⟩
  | 8 => ⟨((56613/33554432), (2262221/536870912)), (27683503/137438953472), by norm_num⟩
  | 9 => ⟨((-313191/2147483648), (-756661/1073741824)), (110220603/549755813888), by norm_num⟩
  | 10 => ⟨((27799/17179869184), (892347/8589934592)), (1760560045/8796093022208), by norm_num⟩
  | 11 => ⟨((43359/17179869184), (-116533/8589934592)), (1759601837/8796093022208), by norm_num⟩
  | 12 => ⟨((-179239/274877906944), (53941/34359738368)), (1759319245/8796093022208), by norm_num⟩
  | 13 => ⟨((61843/549755813888), (-175889/1099511627776)), (1759243093/8796093022208), by norm_num⟩
  | 14 => ⟨((-69253/4398046511104), (61963/4398046511104)), (1759224157/8796093022208), by norm_num⟩
  | 15 => ⟨((16687/8796093022208), (-4489/4398046511104)), (1759219785/8796093022208), by norm_num⟩
  | 16 => ⟨((-887/4398046511104), (113/2199023255552)), (1759218841/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile028Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30757/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30757/1280))
  have he : value ((69/80), (30757/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-461484289/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((128686231094939/562949953421312), (-159304814575633/281474976710656)), (23424901/1125899906842624), by norm_num⟩
  | 1 => ⟨((-140486693/1073741824), (1391303881/4294967296)), (27/2147483648), by norm_num⟩
  | 2 => ⟨((40204829/1073741824), (-796333567/8589934592)), (33/8589934592), by norm_num⟩
  | 3 => ⟨((-490919139/68719476736), (1215449111/68719476736)), (53/68719476736), by norm_num⟩
  | 4 => ⟨((280984905/274877906944), (-1391360923/549755813888)), (63/549755813888), by norm_num⟩
  | 5 => ⟨((-514642909/4398046511104), (1274185945/4398046511104)), (15/1099511627776), by norm_num⟩
  | 6 => ⟨((98187853/8796093022208), (-972399155/35184372088832)), (3/2199023255552), by norm_num⟩
  | 7 => ⟨((-513822033/562949953421312), (636076785/281474976710656)), (65/562949953421312), by norm_num⟩
  | 8 => ⟨((588187437/9007199254740992), (-1456272211/9007199254740992)), (77/9007199254740992), by norm_num⟩
  | 9 => ⟨((-299251439/72057594037927936), (740905921/72057594037927936)), (81/144115188075855872), by norm_num⟩
  | 10 => ⟨((548099305/2305843009213693952), (-1357019441/2305843009213693952)), (19/576460752303423488), by norm_num⟩
  | 11 => ⟨((-456309567/36893488147419103232), (1129760517/36893488147419103232)), (33/18446744073709551616), by norm_num⟩
  | 12 => ⟨((87058533/147573952589676412928), (-862180419/590295810358705651712)), (53/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-122656621/4722366482869645213696), (1214724545/18889465931478580854784)), (77/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((320934171/302231454903657293676544), (-794589423/302231454903657293676544)), (13/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((-391875133/9671406556917033397649408), (485114805/4835703278458516698824704)), (33/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((56073897/38685626227668133590597632), (-1110650831/309485009821345068724781056)), (39/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-96632042523/633825300114114700748351602688)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781207629885865/633825300114114700748351602688), (-917259031555/316912650057057350374175801344)), (2887/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236560649663459/4951760157141521099596496896), (-1031869325097/19807040628566084398385987584)), (12993/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236553910664007/309485009821345068724781056), (-2192611553019/2475880078570760549798248448)), (27613/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774097034791935/154742504910672534362390528), (-1096243466971/77371252455336267181195264)), (27617/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776138797427011/4835703278458516698824704), (-1027662041805/4835703278458516698824704)), (25895/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630585900391335/302231454903657293676544), (-1798276145861/604462909807314587353088)), (11331/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891663614651953/75557863725914323419136), (-1460975206943/37778931862957161709568)), (36833/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300442259119839/4722366482869645213696), (-2191245505727/4722366482869645213696)), (27631/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406359514086293/147573952589676412928), (-3012609409143/590295810358705651712)), (9501/147573952589676412928), by norm_num⟩
  | 8 => ⟨((914229960449443/36893488147419103232), (-3765231947689/73786976294838206464)), (1485/2305843009213693952), by norm_num⟩
  | 7 => ⟨((228532803087627/1152921504606846976), (-4235157330533/9223372036854775808)), (26741/4611686018427387904), by norm_num⟩
  | 6 => ⟨((6248075230247/4503599627370496), (-1058561598089/288230376151711744)), (53509/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74962991086893/9007199254740992), (-925985136915/36028797018963968)), (11713/36028797018963968), by norm_num⟩
  | 4 => ⟨((374717447730983/9007199254740992), (-2776930065281/18014398509481984)), (70339/36028797018963968), by norm_num⟩
  | 3 => ⟨((749141869026027/4503599627370496), (-6938735107335/9007199254740992)), (2751/281474976710656), by norm_num⟩
  | 2 => ⟨((140372309790369/281474976710656), (-3466673668045/1125899906842624)), (88195/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121504560563793/1125899906842624), (-10386542197149/1125899906842624)), (66349/562949953421312), by norm_num⟩
  | 0 => ⟨((1117056541011875/1125899906842624), (-5179778277599/281474976710656)), (267025/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117056541011875/1125899906842624), (-5179778277599/281474976710656)), (1018619541648482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1107901356584525/1125899906842624), (-41112750224551/1125899906842624)), (134921/281474976710656), by norm_num⟩
  | 2 => ⟨((1088689278897097/1125899906842624), (-80911049854217/1125899906842624)), (137691/140737488355328), by norm_num⟩
  | 3 => ⟨((1046893903120045/1125899906842624), (-156473931626157/1125899906842624)), (1144283/562949953421312), by norm_num⟩
  | 4 => ⟨((475842810981397/562949953421312), (-72746966236113/281474976710656)), (4892065/1125899906842624), by norm_num⟩
  | 5 => ⟨((729222536138411/1125899906842624), (-15372645780403/35184372088832)), (2699725/281474976710656), by norm_num⟩
  | 6 => ⟨((128686231094939/562949953421312), (-159304814575633/281474976710656)), (23424901/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-461484289/33554432)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((649608873/9007199254740992), (-606981195/9007199254740992)), (1647/9007199254740992), by norm_num⟩
  | 1 => ⟨((889798521/9007199254740992), (154284877/18014398509481984)), (8379/18014398509481984), by norm_num⟩
  | 2 => ⟨((264432335/9007199254740992), (701835111/18014398509481984)), (355/562949953421312), by norm_num⟩
  | 3 => ⟨((-215936411/72057594037927936), (553036515/36028797018963968)), (42817/72057594037927936), by norm_num⟩
  | 4 => ⟨((-906491313/288230376151711744), (135907669/72057594037927936)), (125997/288230376151711744), by norm_num⟩
  | 5 => ⟨((-1475543753/2305843009213693952), (-224699371/1152921504606846976)), (630723/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-194772429/4611686018427387904), (-410537819/4611686018427387904)), (1477811/9223372036854775808), by norm_num⟩
  | 7 => ⟨((330844615/73786976294838206464), (-410748811/36893488147419103232)), (1829055/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1349851503/1180591620717411303424), (-65958083/147573952589676412928)), (84817365/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((915486151/9444732965739290427392), (207202047/4722366482869645213696)), (289697013/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((54731319/18889465931478580854784), (68934361/9444732965739290427392)), (545869061/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-3103487/18889465931478580854784), (17667687/37778931862957161709568)), (535728153/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-843023/37778931862957161709568), (146609/9444732965739290427392)), (2131795023/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((-51593/37778931862957161709568), (6115/37778931862957161709568)), (2129005885/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-2619/37778931862957161709568), (-45/2361183241434822606848)), (2128360023/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-57/18889465931478580854784), (-95/37778931862957161709568)), (2128221011/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-3/37778931862957161709568), (-7/37778931862957161709568)), (1064096517/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1082368949/562949953421312), (297812893/281474976710656)), (9881/281474976710656), by norm_num⟩
  | 1 => ⟨((-43166607/70368744177664), (829447215/281474976710656)), (40257/562949953421312), by norm_num⟩
  | 2 => ⟨((-15826385/17592186044416), (3932699/35184372088832)), (114121/1125899906842624), by norm_num⟩
  | 3 => ⟨((-1322445101/9007199254740992), (748488783/9007199254740992)), (1030409/9007199254740992), by norm_num⟩
  | 4 => ⟨((-887396377/9007199254740992), (-91737933/2251799813685248)), (32311/281474976710656), by norm_num⟩
  | 5 => ⟨((328360509/72057594037927936), (-405830387/18014398509481984)), (3847905/36028797018963968), by norm_num⟩
  | 6 => ⟨((155929331/72057594037927936), (-37802823/576460752303423488)), (13829441/144115188075855872), by norm_num⟩
  | 7 => ⟨((1496868153/18446744073709551616), (-152758759/9223372036854775808)), (397964103/4611686018427387904), by norm_num⟩
  | 8 => ⟨((254533371/9223372036854775808), (88785537/9223372036854775808)), (1466354439/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-6592371/18446744073709551616), (27527691/9223372036854775808)), (1392130271/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1909829/18446744073709551616), (520555/18446744073709551616)), (1354021623/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-8699/2305843009213693952), (127507/18446744073709551616)), (1336685121/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-16137/18446744073709551616), (-489/4611686018427387904)), (1329593777/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-167/18446744073709551616), (-435/18446744073709551616)), (331739175/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-1/576460752303423488), (-1/1152921504606846976)), (1326057117/18446744073709551616), by norm_num⟩
  | 15 => ⟨(0, (-5/18446744073709551616)), (331443413/4611686018427387904), by norm_num⟩
  | 16 => ⟨((1/18446744073709551616), 0), (82855669/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((541184457/281474976710656), (297812905/281474976710656)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-43166613/70368744177664), (414723595/140737488355328)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((-506444297/562949953421312), (62923167/562949953421312)), (1/4294967296), by norm_num⟩
  | 3 => ⟨((-165305657/1125899906842624), (46780551/562949953421312)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-110924535/1125899906842624), (-22934489/562949953421312)), (1/2147483648), by norm_num⟩
  | 5 => ⟨((5130629/1125899906842624), (-6341099/281474976710656)), (1/2147483648), by norm_num⟩
  | 6 => ⟨((1218199/562949953421312), (-73837/1125899906842624)), (1/2147483648), by norm_num⟩
  | 7 => ⟨((45681/562949953421312), (-9323/562949953421312)), (1/2147483648), by norm_num⟩
  | 8 => ⟨((31071/1125899906842624), (5419/562949953421312)), (1/2147483648), by norm_num⟩
  | 9 => ⟨((-201/562949953421312), (3361/1125899906842624)), (1/2147483648), by norm_num⟩
  | 10 => ⟨((-117/1125899906842624), (1/35184372088832)), (1/2147483648), by norm_num⟩
  | 11 => ⟨((-1/281474976710656), (1/140737488355328)), (1/2147483648), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨28,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨28,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(4393/1073741824)) (L:=(647722245601313/295147905179352825856)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile028
