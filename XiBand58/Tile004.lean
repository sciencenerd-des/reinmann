/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile004Gamma
import XiBand58.Tile004Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile004
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-287601857/8796093022208), (-389071617/8796093022208)), (315/4398046511104), by norm_num⟩
  | 1 => ⟨((-39350521/17592186044416), (-1235025029/17592186044416)), (2953/17592186044416), by norm_num⟩
  | 2 => ⟨((414757507/17592186044416), (-1311321445/35184372088832)), (1699/8796093022208), by norm_num⟩
  | 3 => ⟨((1164897353/70368744177664), (-522406839/70368744177664)), (10347/70368744177664), by norm_num⟩
  | 4 => ⟨((1530416087/281474976710656), (232368211/281474976710656)), (23641/281474976710656), by norm_num⟩
  | 5 => ⟨((1121240845/1125899906842624), (239628405/281474976710656)), (21717/562949953421312), by norm_num⟩
  | 6 => ⟨((368283525/4503599627370496), (545477819/2251799813685248)), (8377/562949953421312), by norm_num⟩
  | 7 => ⟨((-71702431/9007199254740992), (1489337103/36028797018963968)), (179251/36028797018963968), by norm_num⟩
  | 8 => ⟨((-271402355/72057594037927936), (670429571/144115188075855872)), (214355/144115188075855872), by norm_num⟩
  | 9 => ⟨((-393099187/576460752303423488), (358761945/1152921504606846976)), (484701/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-775931257/9223372036854775808), (-3400547/9223372036854775808)), (2411879/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-582097825/73786976294838206464), (-125773011/36893488147419103232)), (2208173/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-675785913/1180591620717411303424), (-168843463/295147905179352825856)), (3247875/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-559932161/18889465931478580854784), (-608442815/9444732965739290427392)), (192470037/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-21171899/37778931862957161709568), (-54723241/9444732965739290427392)), (1516209833/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((232659/2361183241434822606848), (-8292931/18889465931478580854784)), (377999523/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((619591/37778931862957161709568), (-1077765/37778931862957161709568)), (1511289693/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile004Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-230684157/16777216), (315047749/16777216)), (6923/33554432), by norm_num⟩
  | 1 => ⟨((1722477325/134217728), (-14946665/33554432)), (28641/134217728), by norm_num⟩
  | 2 => ⟨((-708975567/134217728), (-5923417/8388608)), (58291/268435456), by norm_num⟩
  | 3 => ⟨((214411077/134217728), (73534273/134217728)), (115801/536870912), by norm_num⟩
  | 4 => ⟨((-96345573/268435456), (-59675351/268435456)), (453521/2147483648), by norm_num⟩
  | 5 => ⟨((8232593/134217728), (8533359/134217728)), (1774531/8589934592), by norm_num⟩
  | 6 => ⟨((-4104453/536870912), (-7566921/536870912)), (1746243/8589934592), by norm_num⟩
  | 7 => ⟨((573065/1073741824), (678809/268435456)), (110734011/549755813888), by norm_num⟩
  | 8 => ⟨((155905/4294967296), (-1608187/4294967296)), (882015703/4398046511104), by norm_num⟩
  | 9 => ⟨((-21651/1073741824), (393749/8589934592)), (1760873389/8796093022208), by norm_num⟩
  | 10 => ⟨((71573/17179869184), (-155769/34359738368)), (1759737261/8796093022208), by norm_num⟩
  | 11 => ⟨((-5343/8589934592), (22775/68719476736)), (1759366957/8796093022208), by norm_num⟩
  | 12 => ⟨((2571/34359738368), (-2979/274877906944)), (1759257805/8796093022208), by norm_num⟩
  | 13 => ⟨((-2055/274877906944), (-217/137438953472)), (1759228221/8796093022208), by norm_num⟩
  | 14 => ⟨((2717/4398046511104), (859/2199023255552)), (1759220803/8796093022208), by norm_num⟩
  | 15 => ⟨((-11/274877906944), (-465/8796093022208)), (439804769/2199023255552), by norm_num⟩
  | 16 => ⟨((7/4398046511104), (3/549755813888)), (439804675/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile004Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2599/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2599/160))
  have he : value ((15/16), (2599/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-623934801/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-653018303096207/1125899906842624), (-167328229751545/2251799813685248)), (26901013/1125899906842624), by norm_num⟩
  | 1 => ⟨((1425799499/4294967296), (182672143/4294967296)), (61/4294967296), by norm_num⟩
  | 2 => ⟨((-816077649/8589934592), (-209110261/17179869184)), (73/17179869184), by norm_num⟩
  | 3 => ⟨((155698079/8589934592), (159583177/68719476736)), (29/34359738368), by norm_num⟩
  | 4 => ⟨((-712928977/274877906944), (-11417477/34359738368)), (17/137438953472), by norm_num⟩
  | 5 => ⟨((1305777771/4398046511104), (167295067/4398046511104)), (65/4398046511104), by norm_num⟩
  | 6 => ⟨((-996508559/35184372088832), (-127671775/35184372088832)), (13/8796093022208), by norm_num⟩
  | 7 => ⟨((1303695005/562949953421312), (167028225/562949953421312)), (35/281474976710656), by norm_num⟩
  | 8 => ⟨((-1492378635/9007199254740992), (-191202201/9007199254740992)), (41/4503599627370496), by norm_num⟩
  | 9 => ⟨((1518551489/144115188075855872), (194555443/144115188075855872)), (43/72057594037927936), by norm_num⟩
  | 10 => ⟨((-1390665019/2305843009213693952), (-22271343/288230376151711744)), (81/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1157771497/36893488147419103232), (148332637/36893488147419103232)), (35/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-1767114179/1180591620717411303424), (-113200535/590295810358705651712)), (55/590295810358705651712), by norm_num⟩
  | 13 => ⟨((311210525/4722366482869645213696), (39872011/4722366482869645213696)), (5/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-1628580521/604462909807314587353088), (-208652263/604462909807314587353088)), (107/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((124285653/1208925819614629174706176), (127386923/9671406556917033397649408)), (67/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-1138188011/309485009821345068724781056), (-72911809/154742504910672534362390528)), (79/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (-3926290010983/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781131518881949/633825300114114700748351602688), (-582294314049/79228162514264337593543950336)), (23165/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892398981165651/39614081257132168796771975168), (-5240360862435/39614081257132168796771975168)), (6517/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892338962113189/2475880078570760549798248448), (-5567574236421/2475880078570760549798248448)), (27705/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887001951635791/77371252455336267181195264), (-5567226103985/154742504910672534362390528)), (27715/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552189425358325/9671406556917033397649408), (-2609452148815/4835703278458516698824704)), (25993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630546896971473/302231454903657293676544), (-2283085383103/302231454903657293676544)), (22755/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891535244141379/75557863725914323419136), (-7419332140013/75557863725914323419136)), (18497/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325086143341321/1180591620717411303424), (-1390972497797/1180591620717411303424)), (13881/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812650725648995/295147905179352825856), (-3824678828501/295147905179352825856)), (38201/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228535716879813/9223372036854775808), (-9560208226979/73786976294838206464)), (47791/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914030875923563/4611686018427387904), (-10753183484361/9223372036854775808)), (53821/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599300696700847/1152921504606846976), (-2687653652317/288230376151711744)), (53891/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199220493740711/144115188075855872), (-4701945182115/72057594037927936)), (47233/144115188075855872), by norm_num⟩
  | 4 => ⟨((749287755891131/18014398509481984), (-1762502767655/4503599627370496)), (71007/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497892752107853/9007199254740992), (-17614812492463/9007199254740992)), (89035/9007199254740992), by norm_num⟩
  | 2 => ⟨((561276415400061/1125899906842624), (-4399851598667/562949953421312)), (44725/1125899906842624), by norm_num⟩
  | 1 => ⟨((35024362181309/35184372088832), (-3295037912717/140737488355328)), (135213/1125899906842624), by norm_num⟩
  | 0 => ⟨((278815383402655/281474976710656), (-52563639819595/1125899906842624)), (8581/35184372088832), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((278815383402655/281474976710656), (-52563639819595/1125899906842624)), (32733917370545853/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1102269699622507/1125899906842624), (-26033488945635/281474976710656)), (569635/1125899906842624), by norm_num⟩
  | 2 => ⟨((267376034636995/281474976710656), (-6371775560561/35184372088832)), (1220731/1125899906842624), by norm_num⟩
  | 3 => ⟨((489504077275009/562949953421312), (-96841863693255/281474976710656)), (86291/35184372088832), by norm_num⟩
  | 4 => ⟨((718006473528469/1125899906842624), (-673658279435457/1125899906842624)), (209443/35184372088832), by norm_num⟩
  | 5 => ⟨((109632869141847/2251799813685248), (-214801956479919/281474976710656)), (33136809/2251799813685248), by norm_num⟩
  | 6 => ⟨((-653018303096207/1125899906842624), (-167328229751545/2251799813685248)), (26901013/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-623934801/67108864)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((275793511/17592186044416), (61757897/2199023255552)), (857/17592186044416), by norm_num⟩
  | 1 => ⟨((-226804419/17592186044416), (109112541/4398046511104)), (1227/8796093022208), by norm_num⟩
  | 2 => ⟨((-102319793/8796093022208), (149794391/140737488355328)), (28111/140737488355328), by norm_num⟩
  | 3 => ⟨((-527258229/281474976710656), (-696640853/281474976710656)), (13357/70368744177664), by norm_num⟩
  | 4 => ⟨((491288345/2251799813685248), (-152419599/281474976710656)), (304409/2251799813685248), by norm_num⟩
  | 5 => ⟨((363774597/4503599627370496), (-198379249/18014398509481984)), (347749/4503599627370496), by norm_num⟩
  | 6 => ⟨((179889645/36028797018963968), (500166663/72057594037927936)), (2659295/72057594037927936), by norm_num⟩
  | 7 => ⟨((-46115315/144115188075855872), (1311107909/2305843009213693952)), (35056673/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1124673947/36893488147419103232), (-265751377/36893488147419103232)), (203901817/36893488147419103232), by norm_num⟩
  | 9 => ⟨((262202175/295147905179352825856), (-348764589/1180591620717411303424)), (1072469755/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-138115177/2361183241434822606848), (432249155/2361183241434822606848)), (1331419211/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-43959905/2361183241434822606848), (-16158443/4722366482869645213696)), (871982927/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1975093/9444732965739290427392), (-22127511/18889465931478580854784)), (189936129/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((527137/9444732965739290427392), (172101/4722366482869645213696)), (1023341075/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-88467/18889465931478580854784), (49231/18889465931478580854784)), (1815352861/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-2209/18889465931478580854784), (-15313/37778931862957161709568)), (1765127371/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((263/9444732965739290427392), (-25/18889465931478580854784)), (1754911841/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-816861857/1099511627776), (-12612167/137438953472)), (5835/549755813888), by norm_num⟩
  | 1 => ⟨((-164725993/2199023255552), (-1010609853/4398046511104)), (24521/1099511627776), by norm_num⟩
  | 2 => ⟨((-340516231/4398046511104), (-300643389/4398046511104)), (253407/8796093022208), by norm_num⟩
  | 3 => ⟨((164474781/8796093022208), (-111703903/2199023255552)), (272673/8796093022208), by norm_num⟩
  | 4 => ⟨((374809249/35184372088832), (38888499/17592186044416)), (1043475/35184372088832), by norm_num⟩
  | 5 => ⟨((-50823417/1125899906842624), (1155201645/1125899906842624)), (30202997/1125899906842624), by norm_num⟩
  | 6 => ⟨((-343111205/18014398509481984), (637406637/36028797018963968)), (867152451/36028797018963968), by norm_num⟩
  | 7 => ⟨((-16406773/9007199254740992), (415466133/72057594037927936)), (1591197561/72057594037927936), by norm_num⟩
  | 8 => ⟨((-38366489/72057594037927936), (-734687/72057594037927936)), (1506593259/72057594037927936), by norm_num⟩
  | 9 => ⟨((-165859/18014398509481984), (-236539/72057594037927936)), (731793885/36028797018963968), by norm_num⟩
  | 10 => ⟨((-153531/72057594037927936), (-36367/72057594037927936)), (722145493/36028797018963968), by norm_num⟩
  | 11 => ⟨((-413/36028797018963968), (-1919/18014398509481984)), (179564603/9007199254740992), by norm_num⟩
  | 12 => ⟨((-203/72057594037927936), (-7/4503599627370496)), (89604355/4503599627370496), by norm_num⟩
  | 13 => ⟨((3/36028797018963968), (-17/72057594037927936)), (1432713117/72057594037927936), by norm_num⟩
  | 14 => ⟨((-1/36028797018963968), (1/18014398509481984)), (358104011/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1/72057594037927936), (1/72057594037927936)), (716165117/36028797018963968), by norm_num⟩
  | 16 => ⟨(0, 0), (716153529/36028797018963968), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-836466520445/1125899906842624), (-103318861087/1125899906842624)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-84339712801/1125899906842624), (-258716106763/1125899906842624)), (1/33554432), by norm_num⟩
  | 2 => ⟨((-87172154903/1125899906842624), (-76964710473/1125899906842624)), (1/16777216), by norm_num⟩
  | 3 => ⟨((21052772331/1125899906842624), (-57192393517/1125899906842624)), (1/16777216), by norm_num⟩
  | 4 => ⟨((5996946899/562949953421312), (2488862377/1125899906842624)), (1/16777216), by norm_num⟩
  | 5 => ⟨((-50822315/1125899906842624), (1155201559/1125899906842624)), (1/8388608), by norm_num⟩
  | 6 => ⟨((-10722347/562949953421312), (19919233/1125899906842624)), (1/8388608), by norm_num⟩
  | 7 => ⟨((-1025395/562949953421312), (6491657/1125899906842624)), (1/8388608), by norm_num⟩
  | 8 => ⟨((-149883/281474976710656), (-11423/1125899906842624)), (1/8388608), by norm_num⟩
  | 9 => ⟨((-2595/281474976710656), (-3715/1125899906842624)), (1/8388608), by norm_num⟩
  | 10 => ⟨((-2401/1125899906842624), (-563/1125899906842624)), (1/8388608), by norm_num⟩
  | 11 => ⟨((-17/1125899906842624), (-121/1125899906842624)), (1/8388608), by norm_num⟩
  | 12 => ⟨((-3/1125899906842624), (-3/1125899906842624)), (1/8388608), by norm_num⟩
  | 13 => ⟨(0, 0), (1/8388608), by norm_num⟩
  | 14 => ⟨(0, 0), (1/8388608), by norm_num⟩
  | 15 => ⟨(0, 0), (1/8388608), by norm_num⟩
  | 16 => ⟨(0, 0), (1/8388608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨4,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨4,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(163873/524288)) (K:=(674983/1073741824)) (L:=(220941057447884383/295147905179352825856)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile004
