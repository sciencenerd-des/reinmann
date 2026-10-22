/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile016Gamma
import XiBand97.Tile016Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile016
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-920575759/562949953421312), (216811613/562949953421312)), (1589/562949953421312), by norm_num⟩
  | 1 => ⟨((-621004797/281474976710656), (-427359843/562949953421312)), (883/140737488355328), by norm_num⟩
  | 2 => ⟨((-284782987/281474976710656), (-699926633/562949953421312)), (3939/562949953421312), by norm_num⟩
  | 3 => ⟨((-218430313/2251799813685248), (-1620698263/2251799813685248)), (11773/2251799813685248), by norm_num⟩
  | 4 => ⟨((435082847/4503599627370496), (-1009470341/4503599627370496)), (13331/4503599627370496), by norm_num⟩
  | 5 => ⟨((235824851/4503599627370496), (-172741689/4503599627370496)), (24575/18014398509481984), by norm_num⟩
  | 6 => ⟨((1019024099/72057594037927936), (-56790695/36028797018963968)), (39227/72057594037927936), by norm_num⟩
  | 7 => ⟨((1405695343/576460752303423488), (295907813/288230376151711744)), (14845/72057594037927936), by norm_num⟩
  | 8 => ⟨((614779253/2305843009213693952), (766721341/2305843009213693952)), (101703/1152921504606846976), by norm_num⟩
  | 9 => ⟨((13425707/1152921504606846976), (1094700527/18446744073709551616)), (969383/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-152280763/73786976294838206464), (1088938787/147573952589676412928)), (792559/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-342296723/590295810358705651712), (776540993/1180591620717411303424)), (11995377/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-791073773/9444732965739290427392), (174643527/4722366482869645213696)), (189501247/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((-332477959/37778931862957161709568), (172987/18889465931478580854784)), (378015223/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-27353583/37778931862957161709568), (-11441131/37778931862957161709568)), (755657381/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-220291/4722366482869645213696), (-1730755/37778931862957161709568)), (1511183095/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-2521/1180591620717411303424), (-87869/18889465931478580854784)), (755580637/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile016Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((469953329/134217728), (55899605/8388608)), (3537/16777216), by norm_num⟩
  | 1 => ⟨((23641241/67108864), (1042546249/67108864)), (30341/134217728), by norm_num⟩
  | 2 => ⟨((-56370151/134217728), (-1231368887/134217728)), (3931/16777216), by norm_num⟩
  | 3 => ⟨((15432537/134217728), (504798169/134217728)), (124583/536870912), by norm_num⟩
  | 4 => ⟨((8446325/134217728), (-157412811/134217728)), (239765/1073741824), by norm_num⟩
  | 5 => ⟨((-227465/4194304), (39142979/134217728)), (459313/2147483648), by norm_num⟩
  | 6 => ⟨((5763985/268435456), (-31913667/536870912)), (1778115/8589934592), by norm_num⟩
  | 7 => ⟨((-1598539/268435456), (10817423/1073741824)), (1744307/8589934592), by norm_num⟩
  | 8 => ⟨((2787919/2147483648), (-762741/536870912)), (110602427/549755813888), by norm_num⟩
  | 9 => ⟨((-2014383/8589934592), (700943/4294967296)), (881413079/4398046511104), by norm_num⟩
  | 10 => ⟨((155129/4294967296), (-15137/1073741824)), (1760350125/8796093022208), by norm_num⟩
  | 11 => ⟨((-165617/34359738368), (41503/68719476736)), (1759543213/8796093022208), by norm_num⟩
  | 12 => ⟨((19289/34359738368), (10321/137438953472)), (1759304365/8796093022208), by norm_num⟩
  | 13 => ⟨((-62649/1099511627776), (-26459/1099511627776)), (1759239589/8796093022208), by norm_num⟩
  | 14 => ⟨((10925/2199023255552), (8733/2199023255552)), (1759223379/8796093022208), by norm_num⟩
  | 15 => ⟨((-3135/8796093022208), (-2223/4398046511104)), (1759219621/8796093022208), by norm_num⟩
  | 16 => ⟨((5/274877906944), (119/2199023255552)), (219902351/1099511627776), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile016Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53459/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53459/2560))
  have he : value ((69/80), (53459/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1604219437/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1123416021370579/2251799813685248), (197972901035271/562949953421312)), (17108539/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1226432699/4294967296), (-432253831/2147483648)), (5/536870912), by norm_num⟩
  | 2 => ⟨((350983541/4294967296), (494813879/8589934592)), (25/8589934592), by norm_num⟩
  | 3 => ⟨((-1071416931/68719476736), (-755237647/68719476736)), (41/68719476736), by norm_num⟩
  | 4 => ⟨((613241491/274877906944), (432271553/274877906944)), (25/274877906944), by norm_num⟩
  | 5 => ⟨((-280798345/1099511627776), (-791734665/4398046511104)), (3/274877906944), by norm_num⟩
  | 6 => ⟨((857168687/35184372088832), (604214889/35184372088832)), (39/35184372088832), by norm_num⟩
  | 7 => ⟨((-280350461/140737488355328), (-395235909/281474976710656)), (27/281474976710656), by norm_num⟩
  | 8 => ⟨((641851103/4503599627370496), (452438357/4503599627370496)), (33/4503599627370496), by norm_num⟩
  | 9 => ⟨((-20409615/2251799813685248), (-460373075/72057594037927936)), (35/72057594037927936), by norm_num⟩
  | 10 => ⟨((18690797/36028797018963968), (210801127/576460752303423488)), (67/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-995882539/36893488147419103232), (-350996873/18446744073709551616)), (29/18446744073709551616), by norm_num⟩
  | 12 => ⟨((190002751/147573952589676412928), (267864407/295147905179352825856)), (23/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-267694557/4722366482869645213696), (-754787427/18889465931478580854784)), (67/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((350214811/151115727451828646838272), (493730129/302231454903657293676544)), (23/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-213814059/2417851639229258349412352), (-301433405/4835703278458516698824704)), (29/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((489518687/154742504910672534362390528), (690119655/309485009821345068724781056)), (69/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (199952322487/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781208942430443/633825300114114700748351602688), (237250591125/158456325028528675187087900672)), (11537/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892486754056047/39614081257132168796771975168), (66723733263/2475880078570760549798248448)), (3245/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118277064783433/154742504910672534362390528), (283561566089/618970019642690137449562112)), (431/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((443524723831325/38685626227668133590597632), (283545478757/38685626227668133590597632)), (13793/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776139727614413/4835703278458516698824704), (66451698543/604462909807314587353088)), (3233/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630586772357787/302231454903657293676544), (930255413775/604462909807314587353088)), (22633/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945833333098789/37778931862957161709568), (1511536867463/75557863725914323419136)), (18391/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81277796136547/295147905179352825856), (566770249585/2361183241434822606848)), (13795/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((203180221798711/73786976294838206464), (779217975773/295147905179352825856)), (18971/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457116258077919/18446744073709551616), (243471450865/9223372036854775808)), (47435/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828268812619315/9223372036854775808), (1095433628803/4611686018427387904)), (417/72057594037927936), by norm_num⟩
  | 6 => ⟨((399878610874539/288230376151711744), (1095198777717/576460752303423488)), (53389/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199415039628621/144115188075855872), (479017378037/36028797018963968)), (11683/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498882354628305/36028797018963968), (2873047735779/36028797018963968)), (35065/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498302573182253/9007199254740992), (1794730554973/4503599627370496)), (43859/4503599627370496), by norm_num⟩
  | 2 => ⟨((561501001993731/1125899906842624), (448336126829/281474976710656)), (43901/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121551557139719/1125899906842624), (2686552945245/562949953421312)), (131913/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117197256916061/1125899906842624), (2679629227209/281474976710656)), (264667/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117197256916061/1125899906842624), (2679629227209/281474976710656)), (1009624485496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1108459834370065/1125899906842624), (21271336139179/1125899906842624)), (530283/1125899906842624), by norm_num⟩
  | 2 => ⟨((1090888032946827/1125899906842624), (20941845354429/562949953421312)), (66511/70368744177664), by norm_num⟩
  | 3 => ⟨((8245365896159/8796093022208), (81162484679601/1125899906842624)), (2141343/1125899906842624), by norm_num⟩
  | 4 => ⟨((983476622655509/1125899906842624), (76080866986639/562949953421312)), (4323271/1125899906842624), by norm_num⟩
  | 5 => ⟨((1677010661936385/2251799813685248), (531654749470951/2251799813685248)), (8721331/1125899906842624), by norm_num⟩
  | 6 => ⟨((1123416021370579/2251799813685248), (197972901035271/562949953421312)), (17108539/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1604219437/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-535518675/562949953421312), (-6736647/17592186044416)), (1369/562949953421312), by norm_num⟩
  | 1 => ⟨((-162832805/562949953421312), (-131650103/140737488355328)), (7629/1125899906842624), by norm_num⟩
  | 2 => ⟨((571628107/2251799813685248), (-851088847/2251799813685248)), (21319/2251799813685248), by norm_num⟩
  | 3 => ⟨((614857711/4503599627370496), (-52530955/4503599627370496)), (79677/9007199254740992), by norm_num⟩
  | 4 => ⟨((370963279/18014398509481984), (195273157/9007199254740992)), (56173/9007199254740992), by norm_num⟩
  | 5 => ⟨((-49684473/72057594037927936), (1432959959/288230376151711744)), (1023013/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1328342257/2305843009213693952), (789468229/2305843009213693952)), (1972371/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-78279319/1152921504606846976), (-465862937/18446744073709551616)), (13520749/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-38572293/18446744073709551616), (-888243847/147573952589676412928)), (22244151/73786976294838206464), by norm_num⟩
  | 9 => ⟨((526765945/2361183241434822606848), (-464041269/1180591620717411303424)), (324840605/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((456531065/18889465931478580854784), (-66425153/9444732965739290427392)), (1562322463/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((9993253/9444732965739290427392), (4981949/18889465931478580854784)), (156408945/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((1006069/18889465931478580854784), (313339/18889465931478580854784)), (1166503843/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((16775/4722366482869645213696), (49947/18889465931478580854784)), (1145315921/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((1139/18889465931478580854784), (5107/18889465931478580854784)), (285104705/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((-117/18889465931478580854784), (181/18889465931478580854784)), (1139365139/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-3/18889465931478580854784), (1/9444732965739290427392)), (71197055/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54819435/70368744177664), (-1080843859/140737488355328)), (21533/70368744177664), by norm_num⟩
  | 1 => ⟨((47650691/4398046511104), (-707764659/35184372088832)), (2935/4398046511104), by norm_num⟩
  | 2 => ⟨((1036106545/70368744177664), (311969405/70368744177664)), (16711/17592186044416), by norm_num⟩
  | 3 => ⟨((-172500293/281474976710656), (288807605/70368744177664)), (305515/281474976710656), by norm_num⟩
  | 4 => ⟨((-496835481/1125899906842624), (62924795/1125899906842624)), (2469353/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1107991785/36028797018963968), (998708541/36028797018963968)), (36636673/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1005673755/72057594037927936), (-310056895/72057594037927936)), (65364823/72057594037927936), by norm_num⟩
  | 7 => ⟨((125341813/576460752303423488), (-246101239/144115188075855872)), (233952129/288230376151711744), by norm_num⟩
  | 8 => ⟨((178785271/2305843009213693952), (-14165845/1152921504606846976)), (107671075/144115188075855872), by norm_num⟩
  | 9 => ⟨((5411885/2305843009213693952), (-8416925/2305843009213693952)), (819244149/1152921504606846976), by norm_num⟩
  | 10 => ⟨((1508665/2305843009213693952), (109015/1152921504606846976)), (798546749/1152921504606846976), by norm_num⟩
  | 11 => ⟨((177/36028797018963968), (57063/2305843009213693952)), (1579020907/2305843009213693952), by norm_num⟩
  | 12 => ⟨((2511/2305843009213693952), (1385/2305843009213693952)), (1571896861/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-9/1152921504606846976), (151/1152921504606846976)), (196166435/288230376151711744), by norm_num⟩
  | 14 => ⟨((-7/2305843009213693952), (1/1152921504606846976)), (784239989/1152921504606846976), by norm_num⟩
  | 15 => ⟨(0, 0), (1568217627/2305843009213693952), by norm_num⟩
  | 16 => ⟨(0, 0), (1568142175/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-877110879/1125899906842624), (-8646750555/1125899906842624)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((12198576195/1125899906842624), (-5662117041/281474976710656)), (1/536870912), by norm_num⟩
  | 2 => ⟨((4144426051/281474976710656), (2495754911/562949953421312)), (1/268435456), by norm_num⟩
  | 3 => ⟨((-690000937/1125899906842624), (4620921839/1125899906842624)), (1/268435456), by norm_num⟩
  | 4 => ⟨((-248417835/562949953421312), (62924679/1125899906842624)), (1/268435456), by norm_num⟩
  | 5 => ⟨((-34624647/1125899906842624), (31209651/1125899906842624)), (1/268435456), by norm_num⟩
  | 6 => ⟨((-15713697/1125899906842624), (-4844653/1125899906842624)), (1/268435456), by norm_num⟩
  | 7 => ⟨((244831/1125899906842624), (-1922671/1125899906842624)), (1/268435456), by norm_num⟩
  | 8 => ⟨((87293/1125899906842624), (-13829/1125899906842624)), (1/268435456), by norm_num⟩
  | 9 => ⟨((2643/1125899906842624), (-4111/1125899906842624)), (1/268435456), by norm_num⟩
  | 10 => ⟨((23/35184372088832), (53/562949953421312)), (1/268435456), by norm_num⟩
  | 11 => ⟨((3/562949953421312), (7/281474976710656)), (1/268435456), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨16,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨16,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(161751/1048576)) (K:=(39955/1073741824)) (L:=(9113302969934927/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile016
