/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile000Gamma
import XiBand58.Tile000Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile000
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1824869/17179869184), (452398959/2199023255552)), (383/2199023255552), by norm_num⟩
  | 1 => ⟨((-555040255/2199023255552), (556921181/4398046511104)), (1605/4398046511104), by norm_num⟩
  | 2 => ⟨((-91585147/549755813888), (-113596107/4398046511104)), (435/1099511627776), by norm_num⟩
  | 3 => ⟨((-6539779/137438953472), (-99345129/2199023255552)), (1291/4398046511104), by norm_num⟩
  | 4 => ⟨((-36319369/8796093022208), (-1284587057/70368744177664)), (11701/70368744177664), by norm_num⟩
  | 5 => ⟨((397538253/281474976710656), (-1105454569/281474976710656)), (21493/281474976710656), by norm_num⟩
  | 6 => ⟨((661911319/1125899906842624), (-135053227/281474976710656)), (4157/140737488355328), by norm_num⟩
  | 7 => ⟨((1029605713/9007199254740992), (-22865395/1125899906842624)), (44607/4503599627370496), by norm_num⟩
  | 8 => ⟨((529216169/36028797018963968), (80497721/18014398509481984)), (212799/72057594037927936), by norm_num⟩
  | 9 => ⟨((775095137/576460752303423488), (688843365/576460752303423488)), (467973/576460752303423488), by norm_num⟩
  | 10 => ⟨((383311355/4611686018427387904), (198094597/1152921504606846976)), (520581/2305843009213693952), by norm_num⟩
  | 11 => ⟨((120436411/73786976294838206464), (685226933/36893488147419103232)), (5979567/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-124407051/295147905179352825856), (967502487/590295810358705651712)), (28565803/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-366269373/4722366482869645213696), (1139655159/9444732965739290427392)), (12278177/295147905179352825856), by norm_num⟩
  | 14 => ⟨((-165001453/18889465931478580854784), (277512237/37778931862957161709568)), (1521968583/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-1852951/2361183241434822606848), (6566485/18889465931478580854784)), (1512980629/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-2291537/37778931862957161709568), (344959/37778931862957161709568)), (188931071/4722366482869645213696), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile000Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-398807027/268435456), (274258375/67108864)), (1719/8388608), by norm_num⟩
  | 1 => ⟨((2486751/8388608), (274689021/33554432)), (3549/16777216), by norm_num⟩
  | 2 => ⟨((19296961/16777216), (-438043757/134217728)), (57695/268435456), by norm_num⟩
  | 3 => ⟨((-19920589/33554432), (56036743/67108864)), (229557/1073741824), by norm_num⟩
  | 4 => ⟨((51198287/268435456), (-19486609/134217728)), (450769/2147483648), by norm_num⟩
  | 5 => ⟨((-11969751/268435456), (4089413/268435456)), (1768419/8589934592), by norm_num⟩
  | 6 => ⟨((4334263/536870912), (36235/536870912)), (27891503/137438953472), by norm_num⟩
  | 7 => ⟨((-155107/134217728), (-58277/134217728)), (110654139/549755813888), by norm_num⟩
  | 8 => ⟨((138049/1073741824), (243003/2147483648)), (1763554221/8796093022208), by norm_num⟩
  | 9 => ⟨((-86107/8589934592), (-83255/4294967296)), (1760721837/8796093022208), by norm_num⟩
  | 10 => ⟨((8617/34359738368), (88151/34359738368)), (1759690157/8796093022208), by norm_num⟩
  | 11 => ⟨((5573/68719476736), (-9367/34359738368)), (1759354541/8796093022208), by norm_num⟩
  | 12 => ⟨((-5107/274877906944), (787/34359738368)), (1759254573/8796093022208), by norm_num⟩
  | 13 => ⟨((2799/1099511627776), (-1503/1099511627776)), (1759227437/8796093022208), by norm_num⟩
  | 14 => ⟨((-1177/4398046511104), (55/2199023255552)), (1759220627/8796093022208), by norm_num⟩
  | 15 => ⟨((25/1099511627776), (1/137438953472)), (1759219039/8796093022208), by norm_num⟩
  | 16 => ⟨((-13/8796093022208), (-3/2199023255552)), (1759218693/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile000Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (4561/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4561/320))
  have he : value ((15/16), (4561/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-1094946759/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-394152823710841/2251799813685248), (-1256333516526299/2251799813685248)), (55648167/2251799813685248), by norm_num⟩
  | 1 => ⟨((430296437/4294967296), (1371538661/4294967296)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((-492573191/17179869184), (-1570041295/17179869184)), (75/17179869184), by norm_num⟩
  | 3 => ⟨((375908835/68719476736), (1198182129/68719476736)), (15/17179869184), by norm_num⟩
  | 4 => ⟨((-215157039/274877906944), (-342898723/137438953472)), (71/549755813888), by norm_num⟩
  | 5 => ⟨((98518677/1099511627776), (314021133/1099511627776)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((-300739397/35184372088832), (-479292501/17592186044416)), (27/17592186044416), by norm_num⟩
  | 7 => ⟨((1536899/2199023255552), (1254081029/562949953421312)), (73/562949953421312), by norm_num⟩
  | 8 => ⟨((-56298695/1125899906842624), (-717792017/4503599627370496)), (43/4503599627370496), by norm_num⟩
  | 9 => ⟨((229144173/72057594037927936), (1460760843/144115188075855872)), (45/72057594037927936), by norm_num⟩
  | 10 => ⟨((-419693093/2305843009213693952), (-1337741275/2305843009213693952)), (85/2305843009213693952), by norm_num⟩
  | 11 => ⟨((174703719/18446744073709551616), (1113710849/36893488147419103232)), (73/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-8332857/18446744073709551616), (-424966031/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 13 => ⟨((46960593/2361183241434822606848), (74841741/1180591620717411303424)), (21/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-122873587/151115727451828646838272), (-1566602563/604462909807314587353088)), (7/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((150034205/4835703278458516698824704), (956446279/9671406556917033397649408)), (35/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-343497277/309485009821345068724781056), (-17107385/4835703278458516698824704)), (41/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (-2442141233471/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781138604781447/633825300114114700748351602688), (-1448741636891/316912650057057350374175801344)), (11561/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59137730766623/1237940039285380274899124224), (-1629751271761/19807040628566084398385987584)), (813/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((118271775945661/154742504910672534362390528), (-1731515368967/1237940039285380274899124224)), (27/2417851639229258349412352), by norm_num⟩
  | 14 => ⟨((1774013946266835/154742504910672534362390528), (-3462816121055/154742504910672534362390528)), (13827/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776099733706309/4835703278458516698824704), (-3246162026137/9671406556917033397649408)), (6483/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261103207368399/604462909807314587353088), (-1420081810757/302231454903657293676544)), (22697/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472887928908377/18889465931478580854784), (-144213686413/2361183241434822606848)), (18447/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650178977286879/2361183241434822606848), (-865188477061/1180591620717411303424)), (27681/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625321519819431/590295810358705651712), (-594740962495/73786976294838206464)), (19039/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828313323901117/73786976294838206464), (-2973247896867/36893488147419103232)), (23811/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828096229883253/9223372036854775808), (-6688550526743/9223372036854775808)), (53609/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799669736708179/576460752303423488), (-3343488945583/576460752303423488)), (53653/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74953703536659/9007199254740992), (-5849334950553/144115188075855872)), (46995/144115188075855872), by norm_num⟩
  | 4 => ⟨((749321657742463/18014398509481984), (-2192614324653/9007199254740992)), (35295/18014398509481984), by norm_num⟩
  | 3 => ⟨((748997197465033/4503599627370496), (-10956859294921/9007199254740992)), (88409/9007199254740992), by norm_num⟩
  | 2 => ⟨((561339887075167/1125899906842624), (-10947524119865/2251799813685248)), (44333/1125899906842624), by norm_num⟩
  | 1 => ⟨((140129143048135/140737488355328), (-8198944991637/562949953421312)), (133643/1125899906842624), by norm_num⟩
  | 0 => ⟨((34875641428453/35184372088832), (-8175461666879/281474976710656)), (269865/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((34875641428453/35184372088832), (-8175461666879/281474976710656)), (1029453281882857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1105278005148295/1125899906842624), (-64829798613149/1125899906842624)), (34417/70368744177664), by norm_num⟩
  | 2 => ⟨((135162610645653/140737488355328), (-127284761371461/1125899906842624)), (1144589/1125899906842624), by norm_num⟩
  | 3 => ⟨((256019692952793/281474976710656), (-122242771584351/562949953421312)), (2457295/1125899906842624), by norm_num⟩
  | 4 => ⟨((878376615936623/1125899906842624), (-444750822434855/1125899906842624)), (2768663/562949953421312), by norm_num⟩
  | 5 => ⟨((509585427515263/1125899906842624), (-173487323327385/281474976710656)), (3253659/281474976710656), by norm_num⟩
  | 6 => ⟨((-394152823710841/2251799813685248), (-1256333516526299/2251799813685248)), (55648167/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-1094946759/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1173161951/8796093022208), (102268519/4398046511104)), (149/1099511627776), by norm_num⟩
  | 1 => ⟨((169288795/4398046511104), (115830721/1099511627776)), (3119/8796093022208), by norm_num⟩
  | 2 => ⟨((-128107633/4398046511104), (586891347/17592186044416)), (8369/17592186044416), by norm_num⟩
  | 3 => ⟨((-1502716767/140737488355328), (-184491621/70368744177664)), (61359/140737488355328), by norm_num⟩
  | 4 => ⟨((-53326471/140737488355328), (-1047713661/562949953421312)), (171463/562949953421312), by norm_num⟩
  | 5 => ⟨((888821939/4503599627370496), (-591843505/4503599627370496)), (776331/4503599627370496), by norm_num⟩
  | 6 => ⟨((36540685/2251799813685248), (123775565/9007199254740992)), (2958897/36028797018963968), by norm_num⟩
  | 7 => ⟨((-500043085/576460752303423488), (36432543/36028797018963968)), (19501293/576460752303423488), by norm_num⟩
  | 8 => ⟨((-152060449/9223372036854775808), (-847807841/9223372036854775808)), (226931935/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1688998949/147573952589676412928), (211006809/73786976294838206464)), (148576403/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-474009401/1180591620717411303424), (1266735753/1180591620717411303424)), (1440746873/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-172592539/2361183241434822606848), (-14005623/295147905179352825856)), (1729020207/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((26315981/4722366482869645213696), (-17721459/4722366482869645213696)), (19168999/147573952589676412928), by norm_num⟩
  | 13 => ⟨((1167781/9444732965739290427392), (10543113/18889465931478580854784)), (1320817499/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-1732941/37778931862957161709568), (-78097/18889465931478580854784)), (1054664343/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((54041/37778931862957161709568), (-29901/9444732965739290427392)), (1992778655/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((867/4722366482869645213696), (6969/37778931862957161709568)), (1968857657/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-644707319/2199023255552), (70165095/137438953472)), (72241/2199023255552), by norm_num⟩
  | 1 => ⟨((-43880009/68719476736), (151118265/137438953472)), (18069/274877906944), by norm_num⟩
  | 2 => ⟨((-196474635/274877906944), (-126887859/549755813888)), (91429/1099511627776), by norm_num⟩
  | 3 => ⟨((18875147/549755813888), (-192633247/1099511627776)), (779061/8796093022208), by norm_num⟩
  | 4 => ⟨((21812841/1099511627776), (39974471/35184372088832)), (6219147/70368744177664), by norm_num⟩
  | 5 => ⟨((677167737/2251799813685248), (620878985/1125899906842624)), (192467409/2251799813685248), by norm_num⟩
  | 6 => ⟨((514456957/4503599627370496), (331490697/9007199254740992)), (369225819/4503599627370496), by norm_num⟩
  | 7 => ⟨((-6012249/18014398509481984), (110396179/9007199254740992)), (1426525869/18014398509481984), by norm_num⟩
  | 8 => ⟨((-62255/562949953421312), (1854959/9007199254740992)), (1394647045/18014398509481984), by norm_num⟩
  | 9 => ⟨((-106985/9007199254740992), (238255/4503599627370496)), (344429915/4503599627370496), by norm_num⟩
  | 10 => ⟨((-50657/18014398509481984), (7393/18014398509481984)), (1369918573/18014398509481984), by norm_num⟩
  | 11 => ⟨((-9/140737488355328), (1393/18014398509481984)), (1366730157/18014398509481984), by norm_num⟩
  | 12 => ⟨((-163/18014398509481984), (-29/18014398509481984)), (1365556439/18014398509481984), by norm_num⟩
  | 13 => ⟨((1/18014398509481984), (5/18014398509481984)), (1365162703/18014398509481984), by norm_num⟩
  | 14 => ⟨((1/18014398509481984), 0), (341260299/4503599627370496), by norm_num⟩
  | 15 => ⟨(0, (1/18014398509481984)), (1365006443/18014398509481984), by norm_num⟩
  | 16 => ⟨(0, 0), (1364997169/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-330090155983/1125899906842624), (287396221685/562949953421312)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-718930102417/1125899906842624), (154745102183/140737488355328)), (1/4194304), by norm_num⟩
  | 2 => ⟨((-804760102447/1125899906842624), (-129933184501/562949953421312)), (1/4194304), by norm_num⟩
  | 3 => ⟨((19328154419/562949953421312), (-197256436107/1125899906842624)), (1/2097152), by norm_num⟩
  | 4 => ⟨((22336344221/1125899906842624), (1279179643/1125899906842624)), (1/2097152), by norm_num⟩
  | 5 => ⟨((169292475/562949953421312), (620879567/1125899906842624)), (1/2097152), by norm_num⟩
  | 6 => ⟨((64306841/562949953421312), (41435565/1125899906842624)), (1/2097152), by norm_num⟩
  | 7 => ⟨((-46947/140737488355328), (13799663/1125899906842624)), (1/2097152), by norm_num⟩
  | 8 => ⟨((-124629/1125899906842624), (57923/281474976710656)), (1/2097152), by norm_num⟩
  | 9 => ⟨((-13293/1125899906842624), (29761/562949953421312)), (1/2097152), by norm_num⟩
  | 10 => ⟨((-787/281474976710656), (465/1125899906842624)), (1/2097152), by norm_num⟩
  | 11 => ⟨((-69/1125899906842624), (3/35184372088832)), (1/2097152), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨0,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨0,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(173423/1048576)) (K:=(2221353/1073741824)) (L:=(695029413851404525/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile000
