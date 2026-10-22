/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile001Gamma
import XiBand97.Tile001Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile001
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-123672457/1099511627776), (603644055/4398046511104)), (507/4398046511104), by norm_num⟩
  | 1 => ⟨((-463845257/2199023255552), (243627651/4398046511104)), (551/2199023255552), by norm_num⟩
  | 2 => ⟨((-540198169/4398046511104), (-25471189/549755813888)), (303/1099511627776), by norm_num⟩
  | 3 => ⟨((-257955483/8796093022208), (-372938507/8796093022208)), (3603/17592186044416), by norm_num⟩
  | 4 => ⟨((-8387347/35184372088832), (-261170367/17592186044416)), (16247/140737488355328), by norm_num⟩
  | 5 => ⟨((494505215/281474976710656), (-801227803/281474976710656)), (7401/140737488355328), by norm_num⟩
  | 6 => ⟨((76974449/140737488355328), (-157895559/562949953421312)), (45381/2251799813685248), by norm_num⟩
  | 7 => ⟨((855235577/9007199254740992), (16952011/4503599627370496)), (120681/18014398509481984), by norm_num⟩
  | 8 => ⟨((397190715/36028797018963968), (452205493/72057594037927936)), (71619/36028797018963968), by norm_num⟩
  | 9 => ⟨((497274515/576460752303423488), (705607151/576460752303423488)), (318017/576460752303423488), by norm_num⟩
  | 10 => ⟨((77424969/2305843009213693952), (1440236945/9223372036854775808)), (1496993/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-91220501/36893488147419103232), (570378823/36893488147419103232)), (4935307/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-406561397/590295810358705651712), (736632777/590295810358705651712)), (26847717/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-844494341/9444732965739290427392), (772545137/9444732965739290427392)), (387648133/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-331340289/37778931862957161709568), (76865525/18889465931478580854784)), (379552505/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-27226185/37778931862957161709568), (4007281/37778931862957161709568)), (756173757/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-1953547/37778931862957161709568), (-124387/18889465931478580854784)), (377836901/9444732965739290427392), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile001Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-522140293/134217728), (251066245/67108864)), (13837/67108864), by norm_num⟩
  | 1 => ⟨((139704119/67108864), (615741685/67108864)), (14403/67108864), by norm_num⟩
  | 2 => ⟨((33718253/67108864), (-131043739/33554432)), (29419/134217728), by norm_num⟩
  | 3 => ⟨((-61534885/134217728), (72954835/67108864)), (233933/1073741824), by norm_num⟩
  | 4 => ⟨((11973729/67108864), (-14413815/67108864)), (457273/2147483648), by norm_num⟩
  | 5 => ⟨((-1573631/33554432), (7960311/268435456)), (1783907/8589934592), by norm_num⟩
  | 6 => ⟨((2507657/268435456), (-1192773/536870912)), (28020015/137438953472), by norm_num⟩
  | 7 => ⟨((-1581399/1073741824), (-175961/1073741824)), (110884027/549755813888), by norm_num⟩
  | 8 => ⟨((397631/2147483648), (100201/1073741824)), (882496983/4398046511104), by norm_num⟩
  | 9 => ⟨((-38479/2147483648), (-42305/2147483648)), (1761227693/8796093022208), by norm_num⟩
  | 10 => ⟨((9691/8589934592), (12721/4294967296)), (1759851437/8796093022208), by norm_num⟩
  | 11 => ⟨((411/68719476736), (-1513/4294967296)), (1759400621/8796093022208), by norm_num⟩
  | 12 => ⟨((-1983/137438953472), (291/8589934592)), (1759267053/8796093022208), by norm_num⟩
  | 13 => ⟨((2845/1099511627776), (-1409/549755813888)), (1759230549/8796093022208), by norm_num⟩
  | 14 => ⟨((-1385/4398046511104), (289/2199023255552)), (1759221335/8796093022208), by norm_num⟩
  | 15 => ⟨((133/4398046511104), (-7/8796093022208)), (219902399/1099511627776), by norm_num⟩
  | 16 => ⟨((-21/8796093022208), (-7/8796093022208)), (439804681/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile001Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (3717/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (3717/256))
  have he : value ((69/80), (3717/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1115412493/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-37866475543435/140737488355328), (-308432038446091/562949953421312)), (29751547/1125899906842624), by norm_num⟩
  | 1 => ⟨((330710497/2147483648), (673430199/2147483648)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((-189287095/4294967296), (-770895675/8589934592)), (41/8589934592), by norm_num⟩
  | 3 => ⟨((577820253/68719476736), (1176623091/68719476736)), (65/68719476736), by norm_num⟩
  | 4 => ⟨((-41340507/34359738368), (-1346915617/549755813888)), (77/549755813888), by norm_num⟩
  | 5 => ⟨((302871769/2199023255552), (1233483649/4398046511104)), (73/4398046511104), by norm_num⟩
  | 6 => ⟨((-231137577/17592186044416), (-941337065/35184372088832)), (29/17592186044416), by norm_num⟩
  | 7 => ⟨((302388677/281474976710656), (307879049/140737488355328)), (39/281474976710656), by norm_num⟩
  | 8 => ⟨((-86538339/1125899906842624), (-1409753395/9007199254740992)), (23/2251799813685248), by norm_num⟩
  | 9 => ⟨((704448163/144115188075855872), (717238597/72057594037927936)), (3/4503599627370496), by norm_num⟩
  | 10 => ⟨((-161280573/576460752303423488), (-328417783/576460752303423488)), (45/1152921504606846976), by norm_num⟩
  | 11 => ⟨((537084195/36893488147419103232), (1093671713/36893488147419103232)), (77/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-409877553/590295810358705651712), (-417319565/295147905179352825856)), (61/590295810358705651712), by norm_num⟩
  | 13 => ⟨((144368949/4722366482869645213696), (1175921669/18889465931478580854784)), (89/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-188872515/151115727451828646838272), (-769207245/302231454903657293676544)), (15/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((28827735/604462909807314587353088), (117404603/1208925819614629174706176)), (19/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((-527999517/309485009821345068724781056), (-1075172463/309485009821345068724781056)), (89/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-2640765542967/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781204193896335/633825300114114700748351602688), (-1566681442603/316912650057057350374175801344)), (2891/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((59140035063735/1237940039285380274899124224), (-3524865599341/39614081257132168796771975168)), (3253/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((946213350479633/1237940039285380274899124224), (-1872489839431/1237940039285380274899124224)), (27655/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887046082143771/77371252455336267181195264), (-1872382910903/77371252455336267181195264)), (13831/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552272724766521/9671406556917033397649408), (-3510490656305/9671406556917033397649408)), (6485/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((315291808879677/151115727451828646838272), (-3071451934341/604462909807314587353088)), (22705/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472913906581609/18889465931478580854784), (-4990682849649/75557863725914323419136)), (36907/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162554471179583/590295810358705651712), (-935659681017/1180591620717411303424)), (6923/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812714161637891/295147905179352825856), (-5145521097841/590295810358705651712)), (19047/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914223270147275/36893488147419103232), (-6430990036121/73786976294838206464)), (47645/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828245702496623/9223372036854775808), (-7233609705329/9223372036854775808)), (26819/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599488451349063/1152921504606846976), (-7232040602635/1152921504606846976)), (13421/288230376151711744), by norm_num⟩
  | 5 => ⟨((599694527953997/72057594037927936), (-3163134115683/72057594037927936)), (47027/144115188075855872), by norm_num⟩
  | 4 => ⟨((749418451047217/18014398509481984), (-4742931310833/18014398509481984)), (35323/18014398509481984), by norm_num⟩
  | 3 => ⟨((374558608092199/2251799813685248), (-5925561110545/4503599627370496)), (22123/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122916894522391/2251799813685248), (-11841790098501/2251799813685248)), (88771/2251799813685248), by norm_num⟩
  | 1 => ⟨((140172692269969/140737488355328), (-17739274361727/1125899906842624)), (33463/281474976710656), by norm_num⟩
  | 0 => ⟨((69793012611607/70368744177664), (-35384423947375/1125899906842624)), (8453/35184372088832), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((69793012611607/70368744177664), (-35384423947375/1125899906842624)), (32245636120545853/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((553219906573563/562949953421312), (-70189842825061/1125899906842624)), (553569/1125899906842624), by norm_num⟩
  | 2 => ⟨((1082940356128539/1125899906842624), (-17244169776595/140737488355328)), (1157023/1125899906842624), by norm_num⟩
  | 3 => ⟨((1024716920996153/1125899906842624), (-16586205616959/70368744177664)), (2509287/1125899906842624), by norm_num⟩
  | 4 => ⟨((217519025165917/281474976710656), (-483060078716429/1125899906842624)), (2875231/562949953421312), by norm_num⟩
  | 5 => ⟨((232563027190023/562949953421312), (-373300527979015/562949953421312)), (13822115/1125899906842624), by norm_num⟩
  | 6 => ⟨((-37866475543435/140737488355328), (-308432038446091/562949953421312)), (29751547/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1115412493/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((463827745/4398046511104), (13577295/549755813888)), (887/8796093022208), by norm_num⟩
  | 1 => ⟨((117603365/4398046511104), (1522195465/17592186044416)), (4743/17592186044416), by norm_num⟩
  | 2 => ⟨((-54792687/2199023255552), (921502213/35184372088832)), (12935/35184372088832), by norm_num⟩
  | 3 => ⟨((-615956137/70368744177664), (-173154499/70368744177664)), (5959/17592186044416), by norm_num⟩
  | 4 => ⟨((-80352591/281474976710656), (-1768988743/1125899906842624)), (266161/1125899906842624), by norm_num⟩
  | 5 => ⟨((765804685/4503599627370496), (-7908007/70368744177664)), (300053/2251799813685248), by norm_num⟩
  | 6 => ⟨((1062227685/72057594037927936), (848119933/72057594037927936)), (284219/4503599627370496), by norm_num⟩
  | 7 => ⟨((-787830761/1152921504606846976), (582550085/576460752303423488)), (14884009/576460752303423488), by norm_num⟩
  | 8 => ⟨((-130243145/4611686018427387904), (-634394595/9223372036854775808)), (172088787/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1335793049/147573952589676412928), (95004683/73786976294838206464)), (449109549/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-8608751/36893488147419103232), (1063869779/1180591620717411303424)), (68546931/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-308155263/4722366482869645213696), (-69131885/2361183241434822606848)), (686164525/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((17777993/4722366482869645213696), (-17497683/4722366482869645213696)), (1089102235/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((3155053/18889465931478580854784), (1920979/4722366482869645213696)), (1342784619/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-669427/18889465931478580854784), (58783/18889465931478580854784)), (286865989/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((11279/18889465931478580854784), (-24545/9444732965739290427392)), (552426763/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((1561/9444732965739290427392), (509/4722366482869645213696)), (1096129511/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-552691449/1099511627776), (656355017/2199023255552)), (60709/2199023255552), by norm_num⟩
  | 1 => ⟨((-478058711/1099511627776), (860351311/1099511627776)), (117/2147483648), by norm_num⟩
  | 2 => ⟨((-1297097245/2199023255552), (-371849257/2199023255552)), (153189/2199023255552), by norm_num⟩
  | 3 => ⟨((119798837/4398046511104), (-340629035/2199023255552)), (655601/8796093022208), by norm_num⟩
  | 4 => ⟨((332621555/17592186044416), (86709143/70368744177664)), (5212809/70368744177664), by norm_num⟩
  | 5 => ⟨((56649157/281474976710656), (197374981/281474976710656)), (159994277/2251799813685248), by norm_num⟩
  | 6 => ⟨((828984503/9007199254740992), (133184327/4503599627370496)), (608625437/9007199254740992), by norm_num⟩
  | 7 => ⟨((-10959407/18014398509481984), (53122883/4503599627370496)), (36503793/562949953421312), by norm_num⟩
  | 8 => ⟨((-1978131/9007199254740992), (2622061/18014398509481984)), (1137502155/18014398509481984), by norm_num⟩
  | 9 => ⟨((-11867/1125899906842624), (407165/9007199254740992)), (560703473/9007199254740992), by norm_num⟩
  | 10 => ⟨((-52537/18014398509481984), (3201/18014398509481984)), (1114039171/18014398509481984), by norm_num⟩
  | 11 => ⟨((-261/4503599627370496), (623/9007199254740992)), (1111040375/18014398509481984), by norm_num⟩
  | 12 => ⟨((-27/2251799813685248), (-35/9007199254740992)), (138742365/2251799813685248), by norm_num⟩
  | 13 => ⟨((1/18014398509481984), (3/4503599627370496)), (277392437/4503599627370496), by norm_num⟩
  | 14 => ⟨((1/18014398509481984), (-1/18014398509481984)), (1109455811/18014398509481984), by norm_num⟩
  | 15 => ⟨((1/18014398509481984), (1/9007199254740992)), (1109423185/18014398509481984), by norm_num⟩
  | 16 => ⟨(0, 0), (554707233/9007199254740992), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-565956037843/1125899906842624), (42006718511/140737488355328)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-489532117075/1125899906842624), (880999737741/1125899906842624)), (1/8388608), by norm_num⟩
  | 2 => ⟨((-83014223781/140737488355328), (-190386850639/1125899906842624)), (1/4194304), by norm_num⟩
  | 3 => ⟨((3833564821/140737488355328), (-87201019951/562949953421312)), (1/4194304), by norm_num⟩
  | 4 => ⟨((21287761249/1125899906842624), (693665597/562949953421312)), (1/2097152), by norm_num⟩
  | 5 => ⟨((113304255/562949953421312), (394752833/562949953421312)), (1/2097152), by norm_num⟩
  | 6 => ⟨((103616379/1125899906842624), (16648213/562949953421312)), (1/2097152), by norm_num⟩
  | 7 => ⟨((-682969/1125899906842624), (13280403/1125899906842624)), (1/2097152), by norm_num⟩
  | 8 => ⟨((-124121/562949953421312), (41077/281474976710656)), (1/2097152), by norm_num⟩
  | 9 => ⟨((-11763/1125899906842624), (25317/562949953421312)), (1/2097152), by norm_num⟩
  | 10 => ⟨((-829/281474976710656), (7/35184372088832)), (1/2097152), by norm_num⟩
  | 11 => ⟨((-27/562949953421312), (55/1125899906842624)), (1/2097152), by norm_num⟩
  | 12 => ⟨((-13/1125899906842624), (-1/1125899906842624)), (1/2097152), by norm_num⟩
  | 13 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | 14 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | 15 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | 16 => ⟨(0, 0), (1/2097152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨1,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨1,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(825149/536870912)) (L:=(86272697433037201/147573952589676412928)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile001
