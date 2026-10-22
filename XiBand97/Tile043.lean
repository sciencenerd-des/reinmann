/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile043Gamma
import XiBand97.Tile043Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile043
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((840860747/144115188075855872), (-909040939/144115188075855872)), (3817/72057594037927936), by norm_num⟩
  | 1 => ⟨((896623261/72057594037927936), (-141774351/36028797018963968)), (1251/18014398509481984), by norm_num⟩
  | 2 => ⟨((694394651/72057594037927936), (292171215/144115188075855872)), (10571/144115188075855872), by norm_num⟩
  | 3 => ⟨((267524757/72057594037927936), (931445491/288230376151711744)), (18795/288230376151711744), by norm_num⟩
  | 4 => ⟨((363199693/576460752303423488), (992457067/576460752303423488)), (31321/576460752303423488), by norm_num⟩
  | 5 => ⟨((-91889339/1152921504606846976), (309497825/576460752303423488)), (107335/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-732544433/9223372036854775808), (61544381/576460752303423488)), (196047/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-925132161/36893488147419103232), (441639323/36893488147419103232)), (1506421/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1488497027/295147905179352825856), (-12488207/73786976294838206464)), (11877581/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-836575191/1180591620717411303424), (-462616877/1180591620717411303424)), (5912325/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-621832437/9444732965739290427392), (-905249837/9444732965739290427392)), (377931337/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-2600591/1180591620717411303424), (-282169627/18889465931478580854784)), (1511280439/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((4997251/9444732965739290427392), (-1008431/590295810358705651712)), (1511181913/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((4947361/37778931862957161709568), (-2720251/18889465931478580854784)), (755580927/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((85053/4722366482869645213696), (-291477/37778931862957161709568)), (755579035/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((69301/37778931862957161709568), (941/37778931862957161709568)), (1511157405/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((5535/37778931862957161709568), (621/9444732965739290427392)), (1511157295/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile043Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((43546167/4194304), (1021732421/16777216)), (3715/16777216), by norm_num⟩
  | 1 => ⟨((-77238533/8388608), (-1218849833/33554432)), (8351/33554432), by norm_num⟩
  | 2 => ⟨((388215961/67108864), (374879905/16777216)), (17739/67108864), by norm_num⟩
  | 3 => ⟨((-305441/131072), (-1341188769/134217728)), (4347/16777216), by norm_num⟩
  | 4 => ⟨((182771559/268435456), (954254877/268435456)), (16257/67108864), by norm_num⟩
  | 5 => ⟨((-18329097/134217728), (-281407883/268435456)), (241281/1073741824), by norm_num⟩
  | 6 => ⟨((7084059/536870912), (35233517/134217728)), (455853/2147483648), by norm_num⟩
  | 7 => ⟨((2864051/1073741824), (-30469297/536870912)), (1763387/8589934592), by norm_num⟩
  | 8 => ⟨((-1859227/1073741824), (23029193/2147483648)), (27764655/137438953472), by norm_num⟩
  | 9 => ⟨((567079/1073741824), (-3836843/2147483648)), (110330555/549755813888), by norm_num⟩
  | 10 => ⟨((-2065819/17179869184), (4534401/17179869184)), (880548567/4398046511104), by norm_num⟩
  | 11 => ⟨((1556447/68719476736), (-1190131/34359738368)), (1759751469/8796093022208), by norm_num⟩
  | 12 => ⟨((-506431/137438953472), (17289/4294967296)), (1759358125/8796093022208), by norm_num⟩
  | 13 => ⟨((582681/1099511627776), (-450145/1099511627776)), (1759252429/8796093022208), by norm_num⟩
  | 14 => ⟨((-300547/4398046511104), (155365/4398046511104)), (1759226249/8796093022208), by norm_num⟩
  | 15 => ⟨((70123/8796093022208), (-10395/4398046511104)), (3435977/17179869184), by norm_num⟩
  | 16 => ⟨((-7441/8796093022208), (171/2199023255552)), (109951183/549755813888), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile043Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35769/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35769/1280))
  have he : value ((69/80), (35769/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-33129281/67108864), (-1073370715/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1318438225409529/2251799813685248), (388428299317741/2251799813685248)), (58302337/1125899906842624), by norm_num⟩
  | 1 => ⟨((1439338341/4294967296), (-424046977/4294967296)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((-1647653615/17179869184), (30338703/1073741824)), (19/2147483648), by norm_num⟩
  | 3 => ⟨((1257412223/68719476736), (-2894135/536870912)), (119/68719476736), by norm_num⟩
  | 4 => ⟨((-1439397351/549755813888), (212032181/274877906944)), (69/274877906944), by norm_num⟩
  | 5 => ⟨((1318176933/4398046511104), (-388351319/4398046511104)), (129/4398046511104), by norm_num⟩
  | 6 => ⟨((-251492755/8796093022208), (148185787/17592186044416)), (25/8796093022208), by norm_num⟩
  | 7 => ⟨((658037195/281474976710656), (-96932971/140737488355328)), (133/562949953421312), by norm_num⟩
  | 8 => ⟨((-1506549687/9007199254740992), (443848275/9007199254740992)), (155/9007199254740992), by norm_num⟩
  | 9 => ⟨((383242767/36028797018963968), (-451632343/144115188075855872)), (161/144115188075855872), by norm_num⟩
  | 10 => ⟨((-1403870237/2305843009213693952), (6462463/36028797018963968)), (75/1152921504606846976), by norm_num⟩
  | 11 => ⟨((18261957/576460752303423488), (-172166389/18446744073709551616)), (127/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-445973503/295147905179352825856), (262778681/590295810358705651712)), (99/590295810358705651712), by norm_num⟩
  | 13 => ⟨((78541415/1180591620717411303424), (-370228443/18889465931478580854784)), (71/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-411011223/151115727451828646838272), (60544509/75557863725914323419136)), (189/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((250931643/2417851639229258349412352), (-295710331/9671406556917033397649408)), (117/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-1148995805/309485009821345068724781056), (169254227/154742504910672534362390528)), (137/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98958294602637/633825300114114700748351602688), (232441757889/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445299763156277/158456325028528675187087900672), (2206403757699/316912650057057350374175801344)), (46317/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946237512107485/19807040628566084398385987584), (4964158018515/39614081257132168796771975168)), (6515/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((59138120044485/77371252455336267181195264), (5274148519077/2475880078570760549798248448)), (27697/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774084876588303/154742504910672534362390528), (5273845215373/154742504910672534362390528)), (13853/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552265437695111/9671406556917033397649408), (2471953693099/4835703278458516698824704)), (203/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((315290101139231/151115727451828646838272), (540699523317/75557863725914323419136)), (11373/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945821836739971/37778931862957161709568), (7028488017089/75557863725914323419136)), (73959/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300426059003317/4722366482869645213696), (5270835369949/4722366482869645213696)), (27751/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625413759823631/590295810358705651712), (3623267625901/295147905179352825856)), (76365/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114276657445261/4611686018427387904), (9056872090219/73786976294838206464)), (95533/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828220681406385/9223372036854775808), (5093597336465/4611686018427387904)), (53791/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599460310023189/1152921504606846976), (10184957007337/1152921504606846976)), (53857/576460752303423488), by norm_num⟩
  | 5 => ⟨((149920115481543/18014398509481984), (8909313646403/144115188075855872)), (94399/144115188075855872), by norm_num⟩
  | 4 => ⟨((23418557686059/562949953421312), (13358907111123/36028797018963968)), (141897/36028797018963968), by norm_num⟩
  | 3 => ⟨((93635041190043/562949953421312), (8344868651397/4503599627370496)), (88947/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122824751568889/2251799813685248), (16676321106863/2251799813685248)), (22335/281474976710656), by norm_num⟩
  | 1 => ⟨((560598737263703/562949953421312), (780646625505/35184372088832)), (269987/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116137130293867/1125899906842624), (49824734173873/1125899906842624)), (547859/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116137130293867/1125899906842624), (49824734173873/1125899906842624)), (2089916233543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1104254101034325/1125899906842624), (24696349773415/281474976710656)), (1134707/1125899906842624), by norm_num⟩
  | 2 => ⟨((537178552562981/562949953421312), (193772432893067/1125899906842624)), (2424901/1125899906842624), by norm_num⟩
  | 3 => ⟨((991824785488173/1125899906842624), (369803370248097/1125899906842624)), (682807/140737488355328), by norm_num⟩
  | 4 => ⟨((752253257429389/1125899906842624), (651532425111729/1125899906842624)), (1651531/140737488355328), by norm_num⟩
  | 5 => ⟨((62789978701419/562949953421312), (1741246752513233/2251799813685248)), (65892767/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1318438225409529/2251799813685248), (388428299317741/2251799813685248)), (58302337/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-33129281/67108864), (-1073370715/67108864)), (1/33554432), by norm_num⟩, -3, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-671041645/288230376151711744), (1354586161/288230376151711744)), (11755/288230376151711744), by norm_num⟩
  | 1 => ⟨((-1520180997/288230376151711744), (253708407/144115188075855872)), (5537/72057594037927936), by norm_num⟩
  | 2 => ⟨((-747065641/288230376151711744), (-187660693/144115188075855872)), (13477/144115188075855872), by norm_num⟩
  | 3 => ⟨((-358587467/1152921504606846976), (-1085614393/1152921504606846976)), (53039/576460752303423488), by norm_num⟩
  | 4 => ⟨((258109827/2305843009213693952), (-1029015665/4611686018427387904)), (372967/4611686018427387904), by norm_num⟩
  | 5 => ⟨((430799733/9223372036854775808), (-72561201/4611686018427387904)), (159417/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1053810921/147573952589676412928), (511204155/147573952589676412928)), (4504821/73786976294838206464), by norm_num⟩
  | 7 => ⟨((107858911/295147905179352825856), (593805075/590295810358705651712)), (66977351/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-467960243/9444732965739290427392), (1064560093/9444732965739290427392)), (517734335/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-212641759/18889465931478580854784), (91181419/18889465931478580854784)), (510837081/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-38030199/37778931862957161709568), (-1634841/4722366482869645213696)), (2034076287/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-1541415/37778931862957161709568), (-2665303/37778931862957161709568)), (1015641817/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1053/1180591620717411303424), (-206559/37778931862957161709568)), (1015260139/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((9221/37778931862957161709568), (-4407/18889465931478580854784)), (1015164519/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((349/18889465931478580854784), (-59/18889465931478580854784)), (2030284775/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((17/18889465931478580854784), (13/37778931862957161709568)), (2030275247/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((1/37778931862957161709568), (1/37778931862957161709568)), (2030273329/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-698915573/2251799813685248), (-418794215/4503599627370496)), (10051/2251799813685248), by norm_num⟩
  | 1 => ⟨((16989963/562949953421312), (-294562657/1125899906842624)), (11981/1125899906842624), by norm_num⟩
  | 2 => ⟨((209064965/4503599627370496), (-375198337/18014398509481984)), (284317/18014398509481984), by norm_num⟩
  | 3 => ⟨((59540257/4503599627370496), (-646034571/36028797018963968)), (663203/36028797018963968), by norm_num⟩
  | 4 => ⟨((327983387/36028797018963968), (183358979/72057594037927936)), (1343511/72057594037927936), by norm_num⟩
  | 5 => ⟨((-32722393/1152921504606846976), (1678097017/1152921504606846976)), (10056723/576460752303423488), by norm_num⟩
  | 6 => ⟨((-110504483/4611686018427387904), (652443829/9223372036854775808)), (4569611/288230376151711744), by norm_num⟩
  | 7 => ⟨((-238337433/18446744073709551616), (997787749/36893488147419103232)), (535330621/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-662363345/147573952589676412928), (-128176649/147573952589676412928)), (2009214109/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-2189787/73786976294838206464), (-41087285/147573952589676412928)), (1934804473/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-1070799/147573952589676412928), (-1487187/147573952589676412928)), (949071073/73786976294838206464), by norm_num⟩
  | 11 => ⟨((409/576460752303423488), (-5825/2305843009213693952)), (1882009445/147573952589676412928), by norm_num⟩
  | 12 => ⟨((12369/73786976294838206464), (347/147573952589676412928)), (1875577665/147573952589676412928), by norm_num⟩
  | 13 => ⟨((439/147573952589676412928), (61/73786976294838206464)), (1873229361/147573952589676412928), by norm_num⟩
  | 14 => ⟨((41/73786976294838206464), (15/73786976294838206464)), (1872437719/147573952589676412928), by norm_num⟩
  | 15 => ⟨((-1/147573952589676412928), (5/147573952589676412928)), (1872190065/147573952589676412928), by norm_num⟩
  | 16 => ⟨(0, 0), (1872118311/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-21841111/70368744177664), (-6543659/70368744177664)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((2123745/70368744177664), (-294562647/1125899906842624)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((13066559/281474976710656), (-23449895/1125899906842624)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((14885063/1125899906842624), (-10094291/562949953421312)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((10249481/1125899906842624), (358123/140737488355328)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-7989/281474976710656), (819383/562949953421312)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((-13489/562949953421312), (19911/281474976710656)), (1/34359738368), by norm_num⟩
  | 7 => ⟨((-14547/1125899906842624), (15225/562949953421312)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-5053/1125899906842624), (-489/562949953421312)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((-33/1125899906842624), (-313/1125899906842624)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((-1/140737488355328), (-11/1125899906842624)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1/1125899906842624), (-3/1125899906842624)), (1/34359738368), by norm_num⟩
  | 12 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 13 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 14 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 15 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 16 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨43,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨43,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(457/1073741824)) (L:=(382525529536843/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile043
