/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile013Gamma
import XiBand97.Tile013Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile013
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-179118523/140737488355328), (754817709/281474976710656)), (181/35184372088832), by norm_num⟩
  | 1 => ⟨((-972095127/281474976710656), (151950281/70368744177664)), (3175/281474976710656), by norm_num⟩
  | 2 => ⟨((-1555272601/562949953421312), (-2676299/281474976710656)), (3489/281474976710656), by norm_num⟩
  | 3 => ⟨((-589694053/562949953421312), (-184043861/281474976710656)), (2571/281474976710656), by norm_num⟩
  | 4 => ⟨((-414655489/2251799813685248), (-12852829/35184372088832)), (11485/2251799813685248), by norm_num⟩
  | 5 => ⟨((66532523/9007199254740992), (-1925660181/18014398509481984)), (41693/18014398509481984), by norm_num⟩
  | 6 => ⟨((116468437/9007199254740992), (-690417599/36028797018963968)), (32465/36028797018963968), by norm_num⟩
  | 7 => ⟨((1088863263/288230376151711744), (-546781135/288230376151711744)), (46453/144115188075855872), by norm_num⟩
  | 8 => ⟨((771254409/1152921504606846976), (49627295/2305843009213693952)), (70221/576460752303423488), by norm_num⟩
  | 9 => ⟨((374726385/4611686018427387904), (423044935/9223372036854775808)), (565201/9223372036854775808), by norm_num⟩
  | 10 => ⟨((239228911/36893488147419103232), (710929465/73786976294838206464)), (1661239/36893488147419103232), by norm_num⟩
  | 11 => ⟨((224512397/1180591620717411303424), (381357155/295147905179352825856)), (24255097/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-351391401/9444732965739290427392), (1216644863/9444732965739290427392)), (379851697/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-152400179/18889465931478580854784), (369744665/37778931862957161709568)), (1512695815/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-37116433/37778931862957161709568), (19879779/37778931862957161709568)), (1511425873/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-3435691/37778931862957161709568), (413365/37778931862957161709568)), (755600695/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-260167/37778931862957161709568), (-62497/37778931862957161709568)), (755582061/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile013Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((945023425/67108864), (12045885/1048576)), (7041/33554432), by norm_num⟩
  | 1 => ⟨((-403014857/33554432), (676708673/67108864)), (14963/67108864), by norm_num⟩
  | 2 => ⟨((921992613/134217728), (-777813169/134217728)), (15427/67108864), by norm_num⟩
  | 3 => ⟨((-365286543/134217728), (287125871/134217728)), (1909/8388608), by norm_num⟩
  | 4 => ⟨((29167943/33554432), (-74905679/134217728)), (236037/1073741824), by norm_num⟩
  | 5 => ⟨((-61533147/268435456), (14122783/134217728)), (454665/2147483648), by norm_num⟩
  | 6 => ⟨((13583391/268435456), (-7128057/536870912)), (1768387/8589934592), by norm_num⟩
  | 7 => ⟨((-5076483/536870912), (583855/1073741824)), (27839919/137438953472), by norm_num⟩
  | 8 => ⟨((3237177/2147483648), (33017/134217728)), (110494651/549755813888), by norm_num⟩
  | 9 => ⟨((-110305/536870912), (-370281/4294967296)), (881111511/4398046511104), by norm_num⟩
  | 10 => ⟨((204055/8589934592), (153993/8589934592)), (1760162733/8796093022208), by norm_num⟩
  | 11 => ⟨((-19439/8589934592), (-198943/68719476736)), (1759489581/8796093022208), by norm_num⟩
  | 12 => ⟨((11111/68719476736), (26837/68719476736)), (1759290157/8796093022208), by norm_num⟩
  | 13 => ⟨((-5635/1099511627776), (-49809/1099511627776)), (1759236117/8796093022208), by norm_num⟩
  | 14 => ⟨((-3553/4398046511104), (10039/2199023255552)), (1759222609/8796093022208), by norm_num⟩
  | 15 => ⟨((445/2199023255552), (-1751/4398046511104)), (879609731/4398046511104), by norm_num⟩
  | 16 => ⟨((-251/8796093022208), (129/4398046511104)), (879609389/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile013Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5149/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5149/256))
  have he : value ((69/80), (5149/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1545132883/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((169710200596765/562949953421312), (1195128041171947/2251799813685248)), (44070061/2251799813685248), by norm_num⟩
  | 1 => ⟨((-741090159/4294967296), (-1304720675/4294967296)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((424174027/8589934592), (746776375/8589934592)), (15/4294967296), by norm_num⟩
  | 3 => ⟨((-647419581/68719476736), (-569904823/34359738368)), (3/4294967296), by norm_num⟩
  | 4 => ⟨((741120543/549755813888), (652387083/274877906944)), (29/274877906944), by norm_num⟩
  | 5 => ⟨((-169676567/1099511627776), (-597445593/2199023255552)), (55/4398046511104), by norm_num⟩
  | 6 => ⟨((517956899/35184372088832), (911885101/35184372088832)), (11/8796093022208), by norm_num⟩
  | 7 => ⟨((-677623705/562949953421312), (-1192985289/562949953421312)), (15/140737488355328), by norm_num⟩
  | 8 => ⟨((775696107/9007199254740992), (682822957/4503599627370496)), (71/9007199254740992), by norm_num⟩
  | 9 => ⟨((-394650007/72057594037927936), (-694798085/72057594037927936)), (19/36028797018963968), by norm_num⟩
  | 10 => ⟨((180707063/576460752303423488), (318142453/576460752303423488)), (9/288230376151711744), by norm_num⟩
  | 11 => ⟨((-300888401/18446744073709551616), (-1059453597/36893488147419103232)), (31/18446744073709551616), by norm_num⟩
  | 12 => ⟨((459247927/590295810358705651712), (101065683/73786976294838206464)), (49/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-647033633/18889465931478580854784), (-1139130169/18889465931478580854784)), (9/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((423244993/302231454903657293676544), (745140771/302231454903657293676544)), (49/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-64600159/1208925819614629174706176), (-909850571/9671406556917033397649408)), (31/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((591597861/309485009821345068724781056), (1041533141/309485009821345068724781056)), (73/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (1373256887221/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445302002051205/158456325028528675187087900672), (1629418474401/633825300114114700748351602688)), (23091/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946242823007137/19807040628566084398385987584), (1833012530705/39614081257132168796771975168)), (25979/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473107947518101/618970019642690137449562112), (486869370577/618970019642690137449562112)), (13803/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887048785529575/77371252455336267181195264), (973683426675/77371252455336267181195264)), (13805/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552278131075495/9671406556917033397649408), (1825538877179/9671406556917033397649408)), (809/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1261172303441697/604462909807314587353088), (1597228964559/604462909807314587353088)), (177/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((945832247104017/37778931862957161709568), (2595276644673/75557863725914323419136)), (36821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300442973668007/4722366482869645213696), (243283075339/590295810358705651712)), (13811/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625439128007897/590295810358705651712), (2675800377021/590295810358705651712)), (37989/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828461394175871/73786976294838206464), (1672140129007/36893488147419103232)), (11875/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828264265908299/9223372036854775808), (3761668689089/9223372036854775808)), (53457/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799754664883267/576460752303423488), (470107543853/144115188075855872)), (26741/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199409927544843/144115188075855872), (1644921653637/72057594037927936)), (5853/18014398509481984), by norm_num⟩
  | 4 => ⟨((1498873412189357/36028797018963968), (2466472832113/18014398509481984)), (35145/18014398509481984), by norm_num⟩
  | 3 => ⟨((749144583469595/4503599627370496), (3081498821889/4503599627370496)), (87959/9007199254740992), by norm_num⟩
  | 2 => ⟨((561492629580287/1125899906842624), (3079109829201/1125899906842624)), (11013/281474976710656), by norm_num⟩
  | 1 => ⟨((1121518106416997/1125899906842624), (9225379884943/1125899906842624)), (33129/281474976710656), by norm_num⟩
  | 0 => ⟨((558548549702245/562949953421312), (9201466833735/562949953421312)), (133239/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558548549702245/562949953421312), (9201466833735/562949953421312)), (508266451122093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((277015579703911/281474976710656), (9129525500235/281474976710656)), (537501/1125899906842624), by norm_num⟩
  | 2 => ⟨((1089322881324995/1125899906842624), (35939547144455/562949953421312)), (1092839/1125899906842624), by norm_num⟩
  | 3 => ⟨((262336316133015/281474976710656), (69543963563691/562949953421312)), (1127105/562949953421312), by norm_num⟩
  | 4 => ⟨((960813679927301/1125899906842624), (259261514807283/1125899906842624)), (2379411/562949953421312), by norm_num⟩
  | 5 => ⟨((380116557996535/562949953421312), (442494059359277/1125899906842624)), (10313743/1125899906842624), by norm_num⟩
  | 6 => ⟨((169710200596765/562949953421312), (1195128041171947/2251799813685248)), (44070061/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1545132883/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-508610813/281474976710656), (74839619/562949953421312)), (1227/281474976710656), by norm_num⟩
  | 1 => ⟨((-649057971/562949953421312), (-708239255/562949953421312)), (6753/562949953421312), by norm_num⟩
  | 2 => ⟨((288395997/2251799813685248), (-1735807473/2251799813685248)), (4651/281474976710656), by norm_num⟩
  | 3 => ⟨((915410267/4503599627370496), (-495135879/4503599627370496)), (68749/4503599627370496), by norm_num⟩
  | 4 => ⟨((813535407/18014398509481984), (180659785/9007199254740992)), (191713/18014398509481984), by norm_num⟩
  | 5 => ⟨((136665649/72057594037927936), (141801271/18014398509481984)), (862437/144115188075855872), by norm_num⟩
  | 6 => ⟨((-380803839/576460752303423488), (470107441/576460752303423488)), (3276271/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-1006960459/9223372036854775808), (-49428691/18446744073709551616)), (21893327/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-201621173/36893488147419103232), (-1076576005/147573952589676412928)), (68135673/147573952589676412928), by norm_num⟩
  | 9 => ⟨((19768041/147573952589676412928), (-1373212279/2361183241434822606848)), (443123141/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((226724879/9444732965739290427392), (-303575191/18889465931478580854784)), (1817997305/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((590125/590295810358705651712), (-3164585/9444732965739290427392)), (650401443/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1404921/18889465931478580854784), (-163851/4722366482869645213696)), (290003979/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((8053/1180591620717411303424), (6477/4722366482869645213696)), (1124837129/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((3327/18889465931478580854784), (3157/9444732965739290427392)), (1116704065/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-47/9444732965739290427392), (23/2361183241434822606848)), (278738219/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((1/4722366482869645213696), (1/18889465931478580854784)), (1114599753/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-949012925/35184372088832), (-664487695/35184372088832)), (18245/35184372088832), by norm_num⟩
  | 1 => ⟨((163423559/8796093022208), (-223327767/4398046511104)), (23601/17592186044416), by norm_num⟩
  | 2 => ⟨((112374139/4398046511104), (24125071/4398046511104)), (4211/2199023255552), by norm_num⟩
  | 3 => ⟨((-61186943/281474976710656), (724632739/140737488355328)), (19267/8796093022208), by norm_num⟩
  | 4 => ⟨((-819160211/4503599627370496), (970147239/4503599627370496)), (9675965/4503599627370496), by norm_num⟩
  | 5 => ⟨((-238192109/4503599627370496), (518408217/4503599627370496)), (17242307/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1746998751/72057594037927936), (-46606273/9007199254740992)), (29506605/18014398509481984), by norm_num⟩
  | 7 => ⟨((50404407/576460752303423488), (-1192524111/576460752303423488)), (6371277/4503599627370496), by norm_num⟩
  | 8 => ⟨((19158065/576460752303423488), (-35242799/1152921504606846976)), (366392595/288230376151711744), by norm_num⟩
  | 9 => ⟨((1642411/576460752303423488), (-2691071/288230376151711744)), (687857103/576460752303423488), by norm_num⟩
  | 10 => ⟨((461373/576460752303423488), (15681/576460752303423488)), (1333173927/1152921504606846976), by norm_num⟩
  | 11 => ⟨((3155/288230376151711744), (9015/1152921504606846976)), (657625157/576460752303423488), by norm_num⟩
  | 12 => ⟨((359/144115188075855872), (91/144115188075855872)), (2555527/2251799813685248), by norm_num⟩
  | 13 => ⟨((1/576460752303423488), (145/1152921504606846976)), (1306059669/1152921504606846976), by norm_num⟩
  | 14 => ⟨((3/1152921504606846976), (-1/576460752303423488)), (652650385/576460752303423488), by norm_num⟩
  | 15 => ⟨((1/1152921504606846976), (-1/1152921504606846976)), (1305075231/1152921504606846976), by norm_num⟩
  | 16 => ⟨(0, 0), (1305012631/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-7592103305/281474976710656), (-21263608299/1125899906842624)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((10459109547/562949953421312), (-57171908631/1125899906842624)), (1/268435456), by norm_num⟩
  | 2 => ⟨((28767780039/1125899906842624), (6176020083/1125899906842624)), (1/268435456), by norm_num⟩
  | 3 => ⟨((-61187045/281474976710656), (1449265513/281474976710656)), (1/134217728), by norm_num⟩
  | 4 => ⟨((-204790041/1125899906842624), (121268449/562949953421312)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-59548049/1125899906842624), (64801015/562949953421312)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-13648421/562949953421312), (-5825767/1125899906842624)), (1/134217728), by norm_num⟩
  | 7 => ⟨((98451/1125899906842624), (-1164577/562949953421312)), (1/134217728), by norm_num⟩
  | 8 => ⟨((37423/1125899906842624), (-17205/562949953421312)), (1/134217728), by norm_num⟩
  | 9 => ⟨((3207/1125899906842624), (-10511/1125899906842624)), (1/134217728), by norm_num⟩
  | 10 => ⟨((901/1125899906842624), (31/1125899906842624)), (1/134217728), by norm_num⟩
  | 11 => ⟨((3/281474976710656), (9/1125899906842624)), (1/134217728), by norm_num⟩
  | 12 => ⟨((3/1125899906842624), (1/1125899906842624)), (1/134217728), by norm_num⟩
  | 13 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | 14 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | 15 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | 16 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨13,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨13,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(88341/1073741824)) (L:=(1214796675355859/36893488147419103232)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile013
