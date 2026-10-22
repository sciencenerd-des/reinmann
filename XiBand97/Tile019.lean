/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile019Gamma
import XiBand97.Tile019Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile019
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-258432759/281474976710656), (-290864919/562949953421312)), (2041/1125899906842624), by norm_num⟩
  | 1 => ⟨((-199446331/281474976710656), (-729569075/562949953421312)), (1157/281474976710656), by norm_num⟩
  | 2 => ⟨((59276061/1125899906842624), (-576231467/562949953421312)), (2637/562949953421312), by norm_num⟩
  | 3 => ⟨((296689309/1125899906842624), (-437223541/1125899906842624)), (8021/2251799813685248), by norm_num⟩
  | 4 => ⟨((650626763/4503599627370496), (-608756239/9007199254740992)), (9201/4503599627370496), by norm_num⟩
  | 5 => ⟨((192486439/4503599627370496), (70009595/18014398509481984)), (34373/36028797018963968), by norm_num⟩
  | 6 => ⟨((562921283/72057594037927936), (785385473/144115188075855872)), (14029/36028797018963968), by norm_num⟩
  | 7 => ⟨((113439325/144115188075855872), (58084021/36028797018963968)), (89503/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1735355/144115188075855872), (1349527521/4611686018427387904)), (339067/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-48531855/2305843009213693952), (1346432647/36893488147419103232)), (1797955/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-333990359/73786976294838206464), (437777995/147573952589676412928)), (3103741/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-1470455201/2361183241434822606848), (94682427/1180591620717411303424)), (2984433/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-598085281/9444732965739290427392), (-380248605/18889465931478580854784)), (378632503/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-45651653/9444732965739290427392), (-10152443/2361183241434822606848)), (377946073/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-1177551/4722366482869645213696), (-19946765/37778931862957161709568)), (1511266327/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-102175/37778931862957161709568), (-1855569/37778931862957161709568)), (755587555/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((22805/18889465931478580854784), (-34933/9444732965739290427392)), (755580015/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile019Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-696725059/134217728), (1383059021/134217728)), (7091/33554432), by norm_num⟩
  | 1 => ⟨((177640417/16777216), (179720845/16777216)), (15259/67108864), by norm_num⟩
  | 2 => ⟨((-464092169/67108864), (-830119425/134217728)), (31739/134217728), by norm_num⟩
  | 3 => ⟨((397548805/134217728), (182465729/67108864)), (15715/67108864), by norm_num⟩
  | 4 => ⟨((-59231353/67108864), (-128402323/134217728)), (241457/1073741824), by norm_num⟩
  | 5 => ⟨((26275419/134217728), (73793183/268435456)), (461313/2147483648), by norm_num⟩
  | 6 => ⟨((-8793089/268435456), (-35271357/536870912)), (1782147/8589934592), by norm_num⟩
  | 7 => ⟨((2077827/536870912), (3564943/268435456)), (1746067/8589934592), by norm_num⟩
  | 8 => ⟨((-214029/1073741824), (-4942447/2147483648)), (110645179/549755813888), by norm_num⟩
  | 9 => ⟨((-375593/8589934592), (370439/1073741824)), (881527255/4398046511104), by norm_num⟩
  | 10 => ⟨((17681/1073741824), (-770965/17179869184)), (1760419757/8796093022208), by norm_num⟩
  | 11 => ⟨((-115655/34359738368), (173177/34359738368)), (1759562925/8796093022208), by norm_num⟩
  | 12 => ⟨((145755/274877906944), (-65831/137438953472)), (1759309453/8796093022208), by norm_num⟩
  | 13 => ⟨((-76979/1099511627776), (39907/1099511627776)), (1759240797/8796093022208), by norm_num⟩
  | 14 => ⟨((35203/4398046511104), (-7641/4398046511104)), (1759223657/8796093022208), by norm_num⟩
  | 15 => ⟨((-883/1099511627776), (-205/4398046511104)), (439804921/2199023255552), by norm_num⟩
  | 16 => ⟨((311/4398046511104), (109/4398046511104)), (1759218821/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile019Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5507/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5507/256))
  have he : value ((69/80), (5507/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1652562981/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1330429218765757/2251799813685248), (345128908721629/2251799813685248)), (26074747/2251799813685248), by norm_num⟩
  | 1 => ⟨((-726214451/2147483648), (-188388527/2147483648)), (31/4294967296), by norm_num⟩
  | 2 => ⟨((415659693/4294967296), (215653977/8589934592)), (19/8589934592), by norm_num⟩
  | 3 => ⟨((-1268848195/68719476736), (-164577035/34359738368)), (31/68719476736), by norm_num⟩
  | 4 => ⟨((726244225/274877906944), (376792501/549755813888)), (19/274877906944), by norm_num⟩
  | 5 => ⟨((-665082775/2199023255552), (-345060509/4398046511104)), (19/2199023255552), by norm_num⟩
  | 6 => ⟨((253780043/8796093022208), (263334051/35184372088832)), (31/35184372088832), by norm_num⟩
  | 7 => ⟨((-1328043885/562949953421312), (-86127531/140737488355328)), (43/562949953421312), by norm_num⟩
  | 8 => ⟨((1520251525/9007199254740992), (394371035/9007199254740992)), (13/2251799813685248), by norm_num⟩
  | 9 => ⟨((-1546913205/144115188075855872), (-401287387/144115188075855872)), (7/18014398509481984), by norm_num⟩
  | 10 => ⟨((708319111/1152921504606846976), (91873133/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-589697495/18446744073709551616), (-305948861/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 12 => ⟨((112507391/73786976294838206464), (116742935/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-1268091795/18889465931478580854784), (-164478925/9444732965739290427392)), (7/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((829498615/302231454903657293676544), (215181647/302231454903657293676544)), (19/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-63303457/604462909807314587353088), (-32843315/1208925819614629174706176)), (3/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((579722873/154742504910672534362390528), (150386897/154742504910672534362390528)), (57/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (41328111743/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445302335013917/158456325028528675187087900672), (392298276675/633825300114114700748351602688)), (5765/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946243612830461/19807040628566084398385987584), (220657923709/19807040628566084398385987584)), (25943/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892433567054857/2475880078570760549798248448), (234437227117/1237940039285380274899124224)), (13783/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443524864740023/38685626227668133590597632), (117211967031/38685626227668133590597632)), (13783/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776140009407829/4835703278458516698824704), (439516630573/9671406556917033397649408)), (6461/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261174073027275/604462909807314587353088), (384548808149/604462909807314587353088)), (22615/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891667590641157/75557863725914323419136), (624838861143/75557863725914323419136)), (36751/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162555686149955/590295810358705651712), (468582817425/4722366482869645213696)), (6891/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812721450372437/295147905179352825856), (644226098985/590295810358705651712)), (37903/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914233290389239/36893488147419103232), (201292431635/18446744073709551616)), (23691/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828270747795507/9223372036854775808), (905660733531/9223372036854775808)), (53309/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599516620011411/1152921504606846976), (452733379855/576460752303423488)), (53315/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199417215442061/144115188075855872), (396032622677/72057594037927936)), (46657/144115188075855872), by norm_num⟩
  | 4 => ⟨((374721540181905/9007199254740992), (1187661657109/36028797018963968)), (69999/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498308279183761/9007199254740992), (1483813989881/9007199254740992)), (87521/9007199254740992), by norm_num⟩
  | 2 => ⟨((2246018261966807/4503599627370496), (1482669942645/2251799813685248)), (175111/4503599627370496), by norm_num⟩
  | 1 => ⟨((2243131589244533/2251799813685248), (1110573403777/562949953421312)), (32855/281474976710656), by norm_num⟩
  | 0 => ⟨((139654985859557/140737488355328), (2215436626183/562949953421312)), (526375/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((139654985859557/140737488355328), (2215436626183/562949953421312)), (2007961281783293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2217258078811457/2251799813685248), (8793585115607/1125899906842624)), (1048797/2251799813685248), by norm_num⟩
  | 2 => ⟨((2183108840147133/2251799813685248), (34634779736279/2251799813685248)), (2081801/2251799813685248), by norm_num⟩
  | 3 => ⟨((1057990282040939/1125899906842624), (67156497091165/2251799813685248)), (4100633/2251799813685248), by norm_num⟩
  | 4 => ⟨((993175264800851/1125899906842624), (31552947498509/562949953421312)), (7951191/2251799813685248), by norm_num⟩
  | 5 => ⟨((1745119164959991/2251799813685248), (55666772501935/562949953421312)), (14919077/2251799813685248), by norm_num⟩
  | 6 => ⟨((1330429218765757/2251799813685248), (345128908721629/2251799813685248)), (26074747/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1652562981/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-1043195921/2251799813685248), (-1004281847/2251799813685248)), (769/562949953421312), by norm_num⟩
  | 1 => ⟨((101657391/2251799813685248), (-1393937267/2251799813685248)), (4351/1125899906842624), by norm_num⟩
  | 2 => ⟨((536006711/2251799813685248), (-95326097/562949953421312)), (24713/4503599627370496), by norm_num⟩
  | 3 => ⟨((1550147375/18014398509481984), (104510927/4503599627370496)), (93839/18014398509481984), by norm_num⟩
  | 4 => ⟨((586042157/72057594037927936), (324355367/18014398509481984)), (134041/36028797018963968), by norm_num⟩
  | 5 => ⟨((-431495303/288230376151711744), (436448525/144115188075855872)), (9645/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1035530601/2305843009213693952), (121257439/1152921504606846976)), (2412995/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-377535339/9223372036854775808), (-569690751/18446744073709551616)), (2118277/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-82912683/295147905179352825856), (-1378909307/295147905179352825856)), (14676921/73786976294838206464), by norm_num⟩
  | 9 => ⟨((289909595/1180591620717411303424), (-73587927/295147905179352825856)), (117671279/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((399438463/18889465931478580854784), (-3352213/9444732965739290427392)), (1253794575/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1998089/2361183241434822606848), (1371307/2361183241434822606848)), (2129507707/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1151489/37778931862957161709568), (691989/18889465931478580854784)), (2026379303/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((54513/37778931862957161709568), (53075/18889465931478580854784)), (500147843/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-711/37778931862957161709568), (7815/37778931862957161709568)), (997315671/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-271/37778931862957161709568), (33/4722366482869645213696)), (31146087/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-3/9444732965739290427392), (1/18889465931478580854784)), (498272897/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((985246993/140737488355328), (-43253717/17592186044416)), (30023/140737488355328), by norm_num⟩
  | 1 => ⟨((846797251/140737488355328), (-845311019/140737488355328)), (61375/140737488355328), by norm_num⟩
  | 2 => ⟨((1134884437/140737488355328), (112961507/35184372088832)), (44851/70368744177664), by norm_num⟩
  | 3 => ⟨((-22937979/35184372088832), (1657483073/562949953421312)), (1631/2199023255552), by norm_num⟩
  | 4 => ⟨((-1034927035/2251799813685248), (-19498843/1125899906842624)), (1692595/2251799813685248), by norm_num⟩
  | 5 => ⟨((-296192219/18014398509481984), (-53657057/4503599627370496)), (6236695/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1059229185/144115188075855872), (-29315369/9007199254740992)), (21907445/36028797018963968), by norm_num⟩
  | 7 => ⟨((143458239/576460752303423488), (-1479776355/1152921504606846976)), (76842703/144115188075855872), by norm_num⟩
  | 8 => ⟨((202082379/2305843009213693952), (-960217/1152921504606846976)), (1110795297/2305843009213693952), by norm_num⟩
  | 9 => ⟨((7728789/4611686018427387904), (-270831/2305843009213693952)), (1042776231/2305843009213693952), by norm_num⟩
  | 10 => ⟨((2137863/4611686018427387904), (522971/4611686018427387904)), (2018125867/4611686018427387904), by norm_num⟩
  | 11 => ⟨((3561/4611686018427387904), (134845/4611686018427387904)), (1988552479/4611686018427387904), by norm_num⟩
  | 12 => ⟨((343/2305843009213693952), (137/288230376151711744)), (494222509/1152921504606846976), by norm_num⟩
  | 13 => ⟨((-47/4611686018427387904), (239/2305843009213693952)), (493176305/1152921504606846976), by norm_num⟩
  | 14 => ⟨((-1/4611686018427387904), (1/288230376151711744)), (1971326041/4611686018427387904), by norm_num⟩
  | 15 => ⟨((1/4611686018427387904), (9/4611686018427387904)), (985452705/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-1/4611686018427387904), (1/2305843009213693952)), (492696487/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((7881975799/1125899906842624), (-2768237403/1125899906842624)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((6774378455/1125899906842624), (-6762487475/1125899906842624)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((9079074793/1125899906842624), (3614768565/1125899906842624)), (1/536870912), by norm_num⟩
  | 3 => ⟨((-734015269/1125899906842624), (3314966051/1125899906842624)), (1/536870912), by norm_num⟩
  | 4 => ⟨((-517463641/1125899906842624), (-9749425/562949953421312)), (1/536870912), by norm_num⟩
  | 5 => ⟨((-18511953/1125899906842624), (-13414297/1125899906842624)), (1/536870912), by norm_num⟩
  | 6 => ⟨((-8275249/1125899906842624), (-3664407/1125899906842624)), (1/536870912), by norm_num⟩
  | 7 => ⟨((280197/1125899906842624), (-1445103/1125899906842624)), (1/536870912), by norm_num⟩
  | 8 => ⟨((6167/70368744177664), (-117/140737488355328)), (1/536870912), by norm_num⟩
  | 9 => ⟨((59/35184372088832), (-133/1125899906842624)), (1/536870912), by norm_num⟩
  | 10 => ⟨((261/562949953421312), (1/8796093022208)), (1/536870912), by norm_num⟩
  | 11 => ⟨((1/1125899906842624), (33/1125899906842624)), (1/536870912), by norm_num⟩
  | 12 => ⟨(0, (1/1125899906842624)), (1/536870912), by norm_num⟩
  | 13 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | 14 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | 15 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | 16 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨19,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨19,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(2279/134217728)) (L:=(8759764040410507/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile019
