/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile004Gamma
import XiBand97.Tile004Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile004
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
  | 0 => ⟨((-793015019/17592186044416), (-161952567/4398046511104)), (1351/17592186044416), by norm_num⟩
  | 1 => ⟨((-44625887/2199023255552), (-626830915/8796093022208)), (3159/17592186044416), by norm_num⟩
  | 2 => ⟨((32279587/2199023255552), (-1547194729/35184372088832)), (3627/17592186044416), by norm_num⟩
  | 3 => ⟨((1056217979/70368744177664), (-819275557/70368744177664)), (2757/17592186044416), by norm_num⟩
  | 4 => ⟨((1607791241/281474976710656), (-135213569/281474976710656)), (25157/281474976710656), by norm_num⟩
  | 5 => ⟨((679816225/562949953421312), (350527231/562949953421312)), (23059/562949953421312), by norm_num⟩
  | 6 => ⟨((624516255/4503599627370496), (1009797901/4503599627370496)), (71027/4503599627370496), by norm_num⟩
  | 7 => ⟨((27769427/18014398509481984), (776609699/18014398509481984)), (94865/18014398509481984), by norm_num⟩
  | 8 => ⟨((-24171385/9007199254740992), (788321185/144115188075855872)), (226601/144115188075855872), by norm_num⟩
  | 9 => ⟨((-21700343/36028797018963968), (265112339/576460752303423488)), (510613/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-1521032469/18446744073709551616), (170225489/9223372036854775808)), (1256085/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-622658197/73786976294838206464), (-229101649/147573952589676412928)), (9011735/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-805334353/1180591620717411303424), (-250952527/590295810358705651712)), (26131413/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-406468515/9444732965739290427392), (-1045520043/18889465931478580854784)), (192699971/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-69731393/37778931862957161709568), (-51245603/9444732965739290427392)), (758272299/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-104851/18889465931478580854784), (-16668661/37778931862957161709568)), (378013901/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((343131/37778931862957161709568), (-582609/18889465931478580854784)), (94456191/2361183241434822606848), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile004Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-245166013/16777216), (547220825/33554432)), (13913/67108864), by norm_num⟩
  | 1 => ⟨((883927987/67108864), (228060935/134217728)), (29037/134217728), by norm_num⟩
  | 2 => ⟨((-1405125433/268435456), (-465760597/268435456)), (29665/134217728), by norm_num⟩
  | 3 => ⟨((100950549/67108864), (117791683/134217728)), (117771/536870912), by norm_num⟩
  | 4 => ⟨((-5264501/16777216), (-40204677/134217728)), (459353/2147483648), by norm_num⟩
  | 5 => ⟨((794257/16777216), (2586469/33554432)), (1788003/8589934592), by norm_num⟩
  | 6 => ⟨((-1180499/268435456), (-8463061/536870912)), (1752899/8589934592), by norm_num⟩
  | 7 => ⟨((-17279/268435456), (1411645/536870912)), (110921403/549755813888), by norm_num⟩
  | 8 => ⟨((270399/2147483648), (-774149/2147483648)), (882599383/4398046511104), by norm_num⟩
  | 9 => ⟨((-133573/4294967296), (172031/4294967296)), (1761280941/8796093022208), by norm_num⟩
  | 10 => ⟨((89635/17179869184), (-58189/17179869184)), (1759865773/8796093022208), by norm_num⟩
  | 11 => ⟨((-23751/34359738368), (11219/68719476736)), (1759403821/8796093022208), by norm_num⟩
  | 12 => ⟨((20725/274877906944), (2505/274877906944)), (1759267469/8796093022208), by norm_num⟩
  | 13 => ⟨((-7451/1099511627776), (-3893/1099511627776)), (1759230573/8796093022208), by norm_num⟩
  | 14 => ⟨((2105/4398046511104), (2415/4398046511104)), (1759221341/8796093022208), by norm_num⟩
  | 15 => ⟨((-47/2199023255552), (-69/1099511627776)), (879609595/4398046511104), by norm_num⟩
  | 16 => ⟨((-1/2199023255552), (13/2199023255552)), (439804681/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile004Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10277/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10277/640))
  have he : value ((69/80), (10277/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-19274775/2097152)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1337055039370011/2251799813685248), (-79623995863579/562949953421312)), (57653267/2251799813685248), by norm_num⟩
  | 1 => ⟨((1459662307/4294967296), (347701903/4294967296)), (65/4294967296), by norm_num⟩
  | 2 => ⟨((-1670919067/17179869184), (-49753095/2147483648)), (77/17179869184), by norm_num⟩
  | 3 => ⟨((1275167329/68719476736), (75938473/17179869184)), (61/68719476736), by norm_num⟩
  | 4 => ⟨((-1459722151/549755813888), (-173858079/274877906944)), (9/68719476736), by norm_num⟩
  | 5 => ⟨((1336790057/4398046511104), (159216431/2199023255552)), (69/4398046511104), by norm_num⟩
  | 6 => ⟨((-1020175687/35184372088832), (-60753269/8796093022208)), (55/35184372088832), by norm_num⟩
  | 7 => ⟨((667328913/281474976710656), (158962475/281474976710656)), (75/562949953421312), by norm_num⟩
  | 8 => ⟨((-1527822701/9007199254740992), (-22746137/562949953421312)), (11/1125899906842624), by norm_num⟩
  | 9 => ⟨((1554617161/144115188075855872), (185160411/72057594037927936)), (23/36028797018963968), by norm_num⟩
  | 10 => ⟨((-1423693381/2305843009213693952), (-169566925/1152921504606846976)), (87/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1185268627/36893488147419103232), (35292423/4611686018427387904)), (75/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-452270807/295147905179352825856), (-215468221/590295810358705651712)), (59/590295810358705651712), by norm_num⟩
  | 13 => ⟨((637203581/9444732965739290427392), (303572815/18889465931478580854784)), (85/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-1667259389/604462909807314587353088), (-397152999/604462909807314587353088)), (57/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((1017899547/9671406556917033397649408), (60617721/2417851639229258349412352)), (71/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-1165220033/309485009821345068724781056), (-277563667/309485009821345068724781056)), (21/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-7397774859/19807040628566084398385987584)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781198666590675/633825300114114700748351602688), (-4494195093493/633825300114114700748351602688)), (23161/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892474566358099/39614081257132168796771975168), (-157991041525/1237940039285380274899124224)), (26063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473104831593955/618970019642690137449562112), (-5245528255/2417851639229258349412352)), (6925/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774084329393101/154742504910672534362390528), (-5371111873133/154742504910672534362390528)), (27709/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776132445274105/4835703278458516698824704), (-314693046699/604462909807314587353088)), (25987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261159891657969/604462909807314587353088), (-4405373730315/604462909807314587353088)), (22749/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891642776009213/75557863725914323419136), (-3579057482535/37778931862957161709568)), (4623/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((81276583119021/295147905179352825856), (-671005678811/590295810358705651712)), (27755/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406353166585773/147573952589676412928), (-7380182525219/590295810358705651712)), (38189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828425015861357/73786976294838206464), (-9223906227943/73786976294838206464)), (47775/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828218802737457/9223372036854775808), (-10375073580401/9223372036854775808)), (53801/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399864549271101/288230376151711744), (-5186396257333/576460752303423488)), (13467/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199358811619383/144115188075855872), (-9073620507767/144115188075855872)), (47211/144115188075855872), by norm_num⟩
  | 4 => ⟨((187347999636489/4503599627370496), (-13605268032953/36028797018963968)), (70969/36028797018963968), by norm_num⟩
  | 3 => ⟨((749077560005523/4503599627370496), (-16997512410539/9007199254740992)), (88977/9007199254740992), by norm_num⟩
  | 2 => ⟨((35088057293669/70368744177664), (-4245956965091/562949953421312)), (89377/2251799813685248), by norm_num⟩
  | 1 => ⟨((140147956892589/140737488355328), (-25441266281423/1125899906842624)), (135067/1125899906842624), by norm_num⟩
  | 0 => ⟨((558047878856417/562949953421312), (-50743049582295/1125899906842624)), (274149/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558047878856417/562949953421312), (-50743049582295/1125899906842624)), (1045795444968795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1104090048989969/1125899906842624), (-25150593773043/281474976710656)), (142059/281474976710656), by norm_num⟩
  | 2 => ⟨((536856780543931/562949953421312), (-3082925060905/17592186044416)), (1216005/1125899906842624), by norm_num⟩
  | 3 => ⟨((989369189733547/1125899906842624), (-188161859893587/562949953421312)), (2745481/1125899906842624), by norm_num⟩
  | 4 => ⟨((743611262805253/1125899906842624), (-661378674002135/1125899906842624)), (6660423/1125899906842624), by norm_num⟩
  | 5 => ⟨((25654136536435/281474976710656), (-218406906323661/281474976710656)), (16622841/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1337055039370011/2251799813685248), (-79623995863579/562949953421312)), (57653267/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-19274775/2097152)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((758486393/35184372088832), (248407979/8796093022208)), (2061/35184372088832), by norm_num⟩
  | 1 => ⟨((-182403513/17592186044416), (510524207/17592186044416)), (5909/35184372088832), by norm_num⟩
  | 2 => ⟨((-881882849/70368744177664), (196920227/70368744177664)), (16865/70368744177664), by norm_num⟩
  | 3 => ⟨((-166168353/70368744177664), (-688965523/281474976710656)), (64015/281474976710656), by norm_num⟩
  | 4 => ⟨((388270495/2251799813685248), (-1380984841/2251799813685248)), (182151/1125899906842624), by norm_num⟩
  | 5 => ⟨((1551424281/18014398509481984), (-364754091/18014398509481984)), (1662371/18014398509481984), by norm_num⟩
  | 6 => ⟨((213724127/36028797018963968), (1014757471/144115188075855872)), (6347111/144115188075855872), by norm_num⟩
  | 7 => ⟨((-361059283/1152921504606846976), (714370863/1152921504606846976)), (20889941/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1171497987/36893488147419103232), (-81320023/9223372036854775808)), (30338885/4611686018427387904), by norm_num⟩
  | 9 => ⟨((24141719/18446744073709551616), (-51486911/147573952589676412928)), (637360857/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-56995845/1180591620717411303424), (535347429/2361183241434822606848)), (394325747/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-102212883/4722366482869645213696), (-6592183/2361183241434822606848)), (2046809945/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((2352023/9444732965739290427392), (-25743629/18889465931478580854784)), (1750737811/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((653701/9444732965739290427392), (887095/18889465931478580854784)), (289982927/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-13695/2361183241434822606848), (65775/18889465931478580854784)), (2044194815/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-2945/18889465931478580854784), (-18775/37778931862957161709568)), (1984284551/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((1307/37778931862957161709568), (-29/18889465931478580854784)), (986042527/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-213190505/274877906944), (-134389849/2199023255552)), (26687/2199023255552), by norm_num⟩
  | 1 => ⟨((-11791809/137438953472), (-405847897/2199023255552)), (6873/274877906944), by norm_num⟩
  | 2 => ⟨((-246782503/2199023255552), (-72442665/1099511627776)), (290473/8796093022208), by norm_num⟩
  | 3 => ⟨((296783331/17592186044416), (-262525179/4398046511104)), (78835/2199023255552), by norm_num⟩
  | 4 => ⟨((1635827181/140737488355328), (16303101/8796093022208)), (4837885/140737488355328), by norm_num⟩
  | 5 => ⟨((-21746911/1125899906842624), (582449137/562949953421312)), (34829159/1125899906842624), by norm_num⟩
  | 6 => ⟨((-731616367/72057594037927936), (1198024775/72057594037927936)), (247400965/9007199254740992), by norm_num⟩
  | 7 => ⟨((-108494269/72057594037927936), (29524759/4503599627370496)), (1795726773/72057594037927936), by norm_num⟩
  | 8 => ⟨((-38073693/72057594037927936), (405835/72057594037927936)), (842976743/36028797018963968), by norm_num⟩
  | 9 => ⟨((-604221/72057594037927936), (4795/4503599627370496)), (50930617/2251799813685248), by norm_num⟩
  | 10 => ⟨((-83237/36028797018963968), (-26277/72057594037927936)), (1604508815/72057594037927936), by norm_num⟩
  | 11 => ⟨((-1419/72057594037927936), (-463/4503599627370496)), (1594332649/72057594037927936), by norm_num⟩
  | 12 => ⟨((-203/72057594037927936), (-93/72057594037927936)), (795308379/36028797018963968), by norm_num⟩
  | 13 => ⟨((-11/72057594037927936), (-63/72057594037927936)), (1589374133/72057594037927936), by norm_num⟩
  | 14 => ⟨((9/36028797018963968), 0), (1588990475/72057594037927936), by norm_num⟩
  | 15 => ⟨(0, (3/72057594037927936)), (1588880375/72057594037927936), by norm_num⟩
  | 16 => ⟨(0, 0), (397212709/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-873228323149/1125899906842624), (-68807629637/1125899906842624)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-24149626821/281474976710656), (-103897066873/562949953421312)), (1/16777216), by norm_num⟩
  | 2 => ⟨((-31588156585/281474976710656), (-74181294201/1125899906842624)), (1/16777216), by norm_num⟩
  | 3 => ⟨((9497060545/562949953421312), (-16801611185/281474976710656)), (1/8388608), by norm_num⟩
  | 4 => ⟨((13086627739/1125899906842624), (2086792877/1125899906842624)), (1/8388608), by norm_num⟩
  | 5 => ⟨((-2718855/140737488355328), (1164901561/1125899906842624)), (1/8388608), by norm_num⟩
  | 6 => ⟨((-2857367/281474976710656), (2339633/140737488355328)), (1/8388608), by norm_num⟩
  | 7 => ⟨((-1695477/1125899906842624), (7382327/1125899906842624)), (1/8388608), by norm_num⟩
  | 8 => ⟨((-297433/562949953421312), (1505/281474976710656)), (1/8388608), by norm_num⟩
  | 9 => ⟨((-9415/1125899906842624), (1331/1125899906842624)), (1/8388608), by norm_num⟩
  | 10 => ⟨((-2623/1125899906842624), (-429/1125899906842624)), (1/8388608), by norm_num⟩
  | 11 => ⟨((-19/1125899906842624), (-111/1125899906842624)), (1/8388608), by norm_num⟩
  | 12 => ⟨((-1/281474976710656), (-1/562949953421312)), (1/8388608), by norm_num⟩
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
    (r:=(326799/1048576)) (K:=(651127/1073741824)) (L:=(57405278779422723/73786976294838206464)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile004
