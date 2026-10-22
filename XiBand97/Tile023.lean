/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile023Gamma
import XiBand97.Tile023Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile023
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((292033897/2251799813685248), (-990734893/2251799813685248)), (339/562949953421312), by norm_num⟩
  | 1 => ⟨((546061509/1125899906842624), (-985984655/2251799813685248)), (1527/1125899906842624), by norm_num⟩
  | 2 => ⟨((509787649/1125899906842624), (-98225807/1125899906842624)), (443/281474976710656), by norm_num⟩
  | 3 => ⟨((227524073/1125899906842624), (329370209/4503599627370496)), (5523/4503599627370496), by norm_num⟩
  | 4 => ⟨((856542127/18014398509481984), (1031205849/18014398509481984)), (3273/4503599627370496), by norm_num⟩
  | 5 => ⟨((124978757/36028797018963968), (1450026767/72057594037927936)), (25801/72057594037927936), by norm_num⟩
  | 6 => ⟨((-448257631/288230376151711744), (627882839/144115188075855872)), (23505/144115188075855872), by norm_num⟩
  | 7 => ⟨((-192181051/288230376151711744), (339963429/576460752303423488)), (23349/288230376151711744), by norm_num⟩
  | 8 => ⟨((-666920051/4611686018427387904), (78504019/2305843009213693952)), (59967/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-781485115/36893488147419103232), (-199519087/36893488147419103232)), (3183571/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-638564319/295147905179352825856), (-279128329/147573952589676412928)), (12026001/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-311945615/2361183241434822606848), (-23212211/73786976294838206464)), (189658409/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((3735607/2361183241434822606848), (-348541539/9444732965739290427392)), (1512380171/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((31351725/18889465931478580854784), (-61963129/18889465931478580854784)), (755692381/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((9857895/37778931862957161709568), (-4084071/18889465931478580854784)), (755598423/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((1052053/37778931862957161709568), (-321481/37778931862957161709568)), (1511163745/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((88317/37778931862957161709568), (7439/37778931862957161709568)), (755579137/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile023Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-435212029/67108864), (828890069/33554432)), (7145/33554432), by norm_num⟩
  | 1 => ⟨((676324495/67108864), (-281491291/33554432)), (7745/33554432), by norm_num⟩
  | 2 => ⟨((-227598613/33554432), (7258689/1048576)), (16203/67108864), by norm_num⟩
  | 3 => ⟨((454387439/134217728), (-208328739/67108864)), (4015/16777216), by norm_num⟩
  | 4 => ⟨((-84231099/67108864), (31551865/33554432)), (122839/536870912), by norm_num⟩
  | 5 => ⟨((49361903/134217728), (-55933373/268435456)), (466561/2147483648), by norm_num⟩
  | 6 => ⟨((-47580471/536870912), (9134517/268435456)), (1793075/8589934592), by norm_num⟩
  | 7 => ⟨((2420303/134217728), (-1961979/536870912)), (1750923/8589934592), by norm_num⟩
  | 8 => ⟨((-6769029/2147483648), (120321/2147483648)), (110767547/549755813888), by norm_num⟩
  | 9 => ⟨((1027125/2147483648), (370095/4294967296)), (110234043/549755813888), by norm_num⟩
  | 10 => ⟨((-271691/4294967296), (-221291/8589934592)), (1760636845/8796093022208), by norm_num⟩
  | 11 => ⟨((499261/68719476736), (173175/34359738368)), (1759625005/8796093022208), by norm_num⟩
  | 12 => ⟨((-97909/137438953472), (-108461/137438953472)), (1759325741/8796093022208), by norm_num⟩
  | 13 => ⟨((15607/274877906944), (115639/1099511627776)), (1759244773/8796093022208), by norm_num⟩
  | 14 => ⟨((-13601/4398046511104), (-26939/2199023255552)), (1759224549/8796093022208), by norm_num⟩
  | 15 => ⟨((-45/4398046511104), (5549/4398046511104)), (54975621/274877906944), by norm_num⟩
  | 16 => ⟨((281/8796093022208), (-1013/8796093022208)), (1759218859/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile023Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28967/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28967/1280))
  have he : value ((69/80), (28967/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1738507059/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((636534216907899/1125899906842624), (-259062073933479/1125899906842624)), (29038183/2251799813685248), by norm_num⟩
  | 1 => ⟨((-694904081/2147483648), (565635869/4294967296)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((397738735/4294967296), (-161875071/4294967296)), (21/8589934592), by norm_num⟩
  | 3 => ⟨((-1214142445/68719476736), (494141951/68719476736)), (17/34359738368), by norm_num⟩
  | 4 => ⟨((1389865143/549755813888), (-565659059/549755813888)), (41/549755813888), by norm_num⟩
  | 5 => ⟨((-636408067/2199023255552), (64752683/549755813888)), (5/549755813888), by norm_num⟩
  | 6 => ⟨((971353779/35184372088832), (-49416221/4398046511104)), (33/35184372088832), by norm_num⟩
  | 7 => ⟨((-158848243/70368744177664), (8081175/8796093022208)), (23/281474976710656), by norm_num⟩
  | 8 => ⟨((1454706649/9007199254740992), (-296024401/4503599627370496)), (55/9007199254740992), by norm_num⟩
  | 9 => ⟨((-185027353/18014398509481984), (301215981/72057594037927936)), (59/144115188075855872), by norm_num⟩
  | 10 => ⟨((1355560581/2305843009213693952), (-551697497/2305843009213693952)), (7/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1128545971/36893488147419103232), (459305173/36893488147419103232)), (49/36893488147419103232), by norm_num⟩
  | 12 => ⟨((430626767/295147905179352825856), (-350520239/590295810358705651712)), (39/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-606709329/9444732965739290427392), (30865461/1180591620717411303424)), (29/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((793735201/302231454903657293676544), (-323041057/302231454903657293676544)), (5/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-969186567/9671406556917033397649408), (49305967/1208925819614629174706176)), (51/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((1109456829/309485009821345068724781056), (-28221007/19342813113834066795298816)), (61/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-125870174199/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445302307991133/158456325028528675187087900672), (-597397876899/633825300114114700748351602688)), (11533/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892487097459029/39614081257132168796771975168), (-672042550169/39614081257132168796771975168)), (12975/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892433422837369/2475880078570760549798248448), (-714009214849/2475880078570760549798248448)), (6893/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774099305740597/154742504910672534362390528), (-356984361535/77371252455336267181195264)), (27573/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552279865609197/9671406556917033397649408), (-20915708061/302231454903657293676544)), (6463/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630586964705033/302231454903657293676544), (-292798404347/302231454903657293676544)), (22621/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891667339338733/75557863725914323419136), (-118939270427/9444732965739290427392)), (18381/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650222642521189/2361183241434822606848), (-713565059379/4722366482869645213696)), (13787/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625442594554403/590295810358705651712), (-245259325769/147573952589676412928)), (37917/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828466159840379/73786976294838206464), (-1226124668797/73786976294838206464)), (47401/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828270221733563/9223372036854775808), (-689576920161/4611686018427387904)), (26667/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599516028343879/1152921504606846976), (-1378858374715/1152921504606846976)), (53343/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199416623964677/144115188075855872), (-1206168747101/144115188075855872)), (46685/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498885126069905/36028797018963968), (-1808588629163/36028797018963968)), (70047/36028797018963968), by norm_num⟩
  | 3 => ⟨((23411042625817/140737488355328), (-564893327231/2251799813685248)), (87593/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123007193564785/2251799813685248), (-1128915178809/1125899906842624)), (43823/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121561924269381/1125899906842624), (-1691195417451/562949953421312)), (131601/1125899906842624), by norm_num⟩
  | 0 => ⟨((279307074554963/281474976710656), (-13494757836763/2251799813685248)), (65933/281474976710656), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279307074554963/281474976710656), (-13494757836763/2251799813685248)), (251514435888194949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2217166083122205/2251799813685248), (-26781644160777/2251799813685248)), (526563/1125899906842624), by norm_num⟩
  | 2 => ⟨((2182746509619585/2251799813685248), (-52739459984539/2251799813685248)), (524727/562949953421312), by norm_num⟩
  | 3 => ⟨((264321946253755/281474976710656), (-102244321631839/2251799813685248)), (4167405/2251799813685248), by norm_num⟩
  | 4 => ⟨((495267820095559/562949953421312), (-96013572513423/1125899906842624)), (8205337/2251799813685248), by norm_num⟩
  | 5 => ⟨((863258130207745/1125899906842624), (-337880356641377/2251799813685248)), (15837115/2251799813685248), by norm_num⟩
  | 6 => ⟨((636534216907899/1125899906842624), (-259062073933479/1125899906842624)), (29038183/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1738507059/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-125716803/4503599627370496), (-627312927/2251799813685248)), (137/281474976710656), by norm_num⟩
  | 1 => ⟨((426547691/2251799813685248), (-449670605/2251799813685248)), (771/562949953421312), by norm_num⟩
  | 2 => ⟨((1189504279/9007199254740992), (57869917/9007199254740992)), (17687/9007199254740992), by norm_num⟩
  | 3 => ⟨((228180139/9007199254740992), (73382221/2251799813685248)), (68243/36028797018963968), by norm_num⟩
  | 4 => ⟨((-270047597/144115188075855872), (663232345/72057594037927936)), (99635/72057594037927936), by norm_num⟩
  | 5 => ⟨((-416662825/288230376151711744), (465351595/576460752303423488)), (236877/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1015847525/4611686018427387904), (-369102321/4611686018427387904)), (489777/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-363757081/36893488147419103232), (-936467179/36893488147419103232)), (7698601/36893488147419103232), by norm_num⟩
  | 8 => ⟨((351274135/295147905179352825856), (-1383882969/590295810358705651712)), (16470289/147573952589676412928), by norm_num⟩
  | 9 => ⟨((961133673/4722366482869645213696), (-139549467/2361183241434822606848)), (350605555/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((236970181/18889465931478580854784), (127333421/18889465931478580854784)), (1163705705/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((5731179/18889465931478580854784), (6967955/9444732965739290427392)), (1091503089/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-177351/37778931862957161709568), (731121/18889465931478580854784)), (267928543/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((-15869/18889465931478580854784), (69699/37778931862957161709568)), (16667941/295147905179352825856), by norm_num⟩
  | 14 => ⟨((-1675/18889465931478580854784), (203/2361183241434822606848)), (2131195121/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-127/18889465931478580854784), (55/37778931862957161709568)), (2130699307/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-11/37778931862957161709568), (-1/9444732965739290427392)), (1065299699/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((994003977/140737488355328), (78607687/70368744177664)), (5661/70368744177664), by norm_num⟩
  | 1 => ⟨((305729701/281474976710656), (59831123/17592186044416)), (28895/140737488355328), by norm_num⟩
  | 2 => ⟨((752349963/562949953421312), (740496093/562949953421312)), (161293/562949953421312), by norm_num⟩
  | 3 => ⟨((-502504891/1125899906842624), (1329304723/1125899906842624)), (185135/562949953421312), by norm_num⟩
  | 4 => ⟨((-1388924765/4503599627370496), (-270899597/4503599627370496)), (368607/1125899906842624), by norm_num⟩
  | 5 => ⟨((-16582993/18014398509481984), (-1233342899/36028797018963968)), (2692645/9007199254740992), by norm_num⟩
  | 6 => ⟨((-18348877/72057594037927936), (-828131967/576460752303423488)), (151122531/576460752303423488), by norm_num⟩
  | 7 => ⟨((460364363/2305843009213693952), (-1283736493/2305843009213693952)), (265601389/1152921504606846976), by norm_num⟩
  | 8 => ⟨((319905221/4611686018427387904), (90427885/9223372036854775808)), (1924074757/9223372036854775808), by norm_num⟩
  | 9 => ⟨((4419395/9223372036854775808), (3591283/1152921504606846976)), (1808307297/9223372036854775808), by norm_num⟩
  | 10 => ⟨((586925/4611686018427387904), (210509/2305843009213693952)), (437566637/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-16799/4611686018427387904), (212809/9223372036854775808)), (1724457979/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-3941/4611686018427387904), (189/1152921504606846976)), (1714132747/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-85/4611686018427387904), (343/9223372036854775808)), (855187483/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-11/2305843009213693952), (9/9223372036854775808)), (1709119801/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-5/9223372036854775808), (-1/9223372036854775808)), (854366079/4611686018427387904), by norm_num⟩
  | 16 => ⟨(0, (-1/9223372036854775808)), (1708620793/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3976015857/562949953421312), (1257722823/1125899906842624)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((1222918899/1125899906842624), (3829191715/1125899906842624)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((752349987/562949953421312), (740496113/562949953421312)), (1/1073741824), by norm_num⟩
  | 3 => ⟨((-502504911/1125899906842624), (1329304677/1125899906842624)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((-347231165/1125899906842624), (-1058201/17592186044416)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((-1036461/1125899906842624), (-38541975/1125899906842624)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((-286695/1125899906842624), (-1617445/1125899906842624)), (1/1073741824), by norm_num⟩
  | 7 => ⟨((14049/70368744177664), (-626825/1125899906842624)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((78103/1125899906842624), (5519/562949953421312)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((135/281474976710656), (3507/1125899906842624)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((143/1125899906842624), (103/1125899906842624)), (1/1073741824), by norm_num⟩
  | 11 => ⟨((-1/281474976710656), (13/562949953421312)), (1/1073741824), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨23,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨23,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(6261/1073741824)) (L:=(4220979978754681/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile023
