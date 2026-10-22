/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile041Gamma
import XiBand97.Tile041Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile041
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2626785/18014398509481984), (-1885521517/144115188075855872)), (8933/144115188075855872), by norm_num⟩
  | 1 => ⟨((722177319/72057594037927936), (-1226622495/72057594037927936)), (6415/72057594037927936), by norm_num⟩
  | 2 => ⟨((925131381/72057594037927936), (-266229725/36028797018963968)), (213/2251799813685248), by norm_num⟩
  | 3 => ⟨((2120234691/288230376151711744), (-22703357/288230376151711744)), (23281/288230376151711744), by norm_num⟩
  | 4 => ⟨((690125769/288230376151711744), (373020233/288230376151711744)), (36339/576460752303423488), by norm_num⟩
  | 5 => ⟨((125392103/288230376151711744), (774367595/1152921504606846976)), (58209/1152921504606846976), by norm_num⟩
  | 6 => ⟨((144383047/9223372036854775808), (1790730039/9223372036854775808)), (405903/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-589910645/36893488147419103232), (683880911/18446744073709551616)), (1524545/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-208213893/36893488147419103232), (677807375/147573952589676412928)), (5959781/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-1337646315/1180591620717411303424), (35691563/147573952589676412928)), (47342207/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1508718043/9444732965739290427392), (-392224165/9444732965739290427392)), (94503425/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-152227479/9444732965739290427392), (-261855031/18889465931478580854784)), (1511351855/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-37923445/37778931862957161709568), (-86390679/37778931862957161709568)), (1511196229/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((240411/37778931862957161709568), (-10181395/37778931862957161709568)), (1511164523/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((110771/9444732965739290427392), (-915111/37778931862957161709568)), (188894817/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((72045/37778931862957161709568), (-61031/37778931862957161709568)), (1511157481/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((7841/37778931862957161709568), (-2393/37778931862957161709568)), (1511157307/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile041Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83786523/8388608), (494916095/8388608)), (229/1048576), by norm_num⟩
  | 1 => ⟨((520313169/33554432), (-1122238939/33554432)), (8149/33554432), by norm_num⟩
  | 2 => ⟨((-175670863/16777216), (20673619/1048576)), (8647/33554432), by norm_num⟩
  | 3 => ⟨((694206647/134217728), (-140501779/16777216)), (34089/134217728), by norm_num⟩
  | 4 => ⟨((-266914059/134217728), (374382809/134217728)), (2005/8388608), by norm_num⟩
  | 5 => ⟨((84777203/134217728), (-203100181/268435456)), (239473/1073741824), by norm_num⟩
  | 6 => ⟨((-91711487/536870912), (91607919/536870912)), (454181/2147483648), by norm_num⟩
  | 7 => ⟨((21496647/536870912), (-34731779/1073741824)), (1760659/8589934592), by norm_num⟩
  | 8 => ⟨((-17682047/2147483648), (2769219/536870912)), (27748463/137438953472), by norm_num⟩
  | 9 => ⟨((6440279/4294967296), (-2924005/4294967296)), (110308283/549755813888), by norm_num⟩
  | 10 => ⟨((-4186201/17179869184), (301195/4294967296)), (880495063/4398046511104), by norm_num⟩
  | 11 => ⟨((2442283/68719476736), (-301365/68719476736)), (1759720877/8796093022208), by norm_num⟩
  | 12 => ⟨((-1284151/274877906944), (-29053/137438953472)), (1759349933/8796093022208), by norm_num⟩
  | 13 => ⟨((609745/1099511627776), (138215/1099511627776)), (1759250429/8796093022208), by norm_num⟩
  | 14 => ⟨((-130621/2199023255552), (-56705/2199023255552)), (1759225789/8796093022208), by norm_num⟩
  | 15 => ⟨((50237/8796093022208), (17353/4398046511104)), (1759220123/8796093022208), by norm_num⟩
  | 16 => ⟨((-4279/8796093022208), (-4471/8796093022208)), (1759218907/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile041Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35053/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35053/1280))
  have he : value ((69/80), (35053/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-33129281/67108864), (-1051884695/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1373687124972181/2251799813685248), (-23127800465017/1125899906842624)), (109075019/2251799813685248), by norm_num⟩
  | 1 => ⟨((46864173/134217728), (789019/67108864)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((-858349111/8589934592), (-7225709/2147483648)), (141/17179869184), by norm_num⟩
  | 3 => ⟨((40940745/2147483648), (44114587/68719476736)), (55/34359738368), by norm_num⟩
  | 4 => ⟨((-374928755/137438953472), (-25249643/274877906944)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((1373414883/4398046511104), (23123217/2199023255552)), (15/549755813888), by norm_num⟩
  | 6 => ⟨((-524063021/17592186044416), (-35293117/35184372088832)), (93/35184372088832), by norm_num⟩
  | 7 => ⟨((685612117/281474976710656), (46172669/562949953421312)), (31/140737488355328), by norm_num⟩
  | 8 => ⟨((-1569681361/9007199254740992), (-26427617/4503599627370496)), (9/562949953421312), by norm_num⟩
  | 9 => ⟨((1597209925/144115188075855872), (3361387/9007199254740992)), (37/36028797018963968), by norm_num⟩
  | 10 => ⟨((-1462699149/2305843009213693952), (-24626433/1152921504606846976)), (69/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1217742131/36893488147419103232), (41004529/36893488147419103232)), (117/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-464661937/295147905179352825856), (-7823185/147573952589676412928)), (181/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((654661423/9444732965739290427392), (44088289/18889465931478580854784)), (129/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-1712938277/604462909807314587353088), (-57679065/604462909807314587353088)), (171/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((1045787541/9671406556917033397649408), (35214373/9671406556917033397649408)), (53/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-1197144253/309485009821345068724781056), (-40310945/309485009821345068724781056)), (123/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98958294602637/633825300114114700748351602688), (-2024214726293/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111324820916771/39614081257132168796771975168), (-1200901630973/158456325028528675187087900672)), (181/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((473118187353803/9903520314283042199192993792), (-5403778903215/39614081257132168796771975168)), (52143/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892417282477065/2475880078570760549798248448), (-1435305284175/618970019642690137449562112)), (13855/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110880134869827/9671406556917033397649408), (-1435222527619/38685626227668133590597632)), (55439/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776131359630037/4835703278458516698824704), (-2690866222423/4835703278458516698824704)), (12999/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((315289464068785/151115727451828646838272), (-2354331748855/302231454903657293676544)), (22759/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945819607244783/37778931862957161709568), (-7650916689571/75557863725914323419136)), (18501/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300422436545619/4722366482869645213696), (-5737607949933/4722366482869645213696)), (27769/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101588020435273/36893488147419103232), (-986033463791/73786976294838206464)), (19105/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1828419050289495/73786976294838206464), (-4929458657875/36893488147419103232)), (95609/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828211347387555/9223372036854775808), (-11089329116729/9223372036854775808)), (107675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599449812042727/1152921504606846976), (-5543440986489/576460752303423488)), (26955/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199350429370783/144115188075855872), (-1212282544679/18014398509481984)), (94505/144115188075855872), by norm_num⟩
  | 4 => ⟨((374692333616605/9007199254740992), (-14541846986805/36028797018963968)), (142083/36028797018963968), by norm_num⟩
  | 3 => ⟨((749066569376717/4503599627370496), (-18167560748665/9007199254740992)), (178173/9007199254740992), by norm_num⟩
  | 2 => ⟨((70174398697033/140737488355328), (-18152845355641/2251799813685248)), (44757/562949953421312), by norm_num⟩
  | 1 => ⟨((1121128814169025/1125899906842624), (-27192153187681/1125899906842624)), (270685/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115931576103619/1125899906842624), (-54233893563133/1125899906842624)), (274981/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1115931576103619/1125899906842624), (-54233893563133/1125899906842624)), (1048969270946311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1103439088842331/1125899906842624), (-107507450625631/1125899906842624)), (1143169/1125899906842624), by norm_num⟩
  | 2 => ⟨((1071160911832055/1125899906842624), (-105362761504065/562949953421312)), (2459041/1125899906842624), by norm_num⟩
  | 3 => ⟨((979643435696635/1125899906842624), (-50120117694269/140737488355328)), (5599453/1125899906842624), by norm_num⟩
  | 4 => ⟨((88699224015833/140737488355328), (-697750753822865/1125899906842624)), (13732357/1125899906842624), by norm_num⟩
  | 5 => ⟨((29606957533309/2251799813685248), (-1759018187515001/2251799813685248)), (34330153/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1373687124972181/2251799813685248), (-23127800465017/1125899906842624)), (109075019/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-33129281/67108864), (-1051884695/67108864)), (1/33554432), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-51551197/144115188075855872), (1149811181/144115188075855872)), (2863/72057594037927936), by norm_num⟩
  | 1 => ⟨((-902001081/144115188075855872), (25274865/4503599627370496)), (5779/72057594037927936), by norm_num⟩
  | 2 => ⟨((-1251781675/288230376151711744), (-79261903/288230376151711744)), (28833/288230376151711744), by norm_num⟩
  | 3 => ⟨((-139349249/144115188075855872), (-642330571/576460752303423488)), (13931/144115188075855872), by norm_num⟩
  | 4 => ⟨((16113813/576460752303423488), (-1692187595/4611686018427387904)), (93621/1152921504606846976), by norm_num⟩
  | 5 => ⟨((504376181/9223372036854775808), (-430934549/9223372036854775808)), (37657/576460752303423488), by norm_num⟩
  | 6 => ⟨((210669691/18446744073709551616), (129005961/147573952589676412928)), (8037223/147573952589676412928), by norm_num⟩
  | 7 => ⟨((591681197/590295810358705651712), (678749389/590295810358705651712)), (14369319/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-42544035/4722366482869645213696), (204008455/1180591620717411303424)), (435728295/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-231667395/18889465931478580854784), (441565123/37778931862957161709568)), (213285141/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-27307273/18889465931478580854784), (1115605/37778931862957161709568)), (1694004637/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-3140595/37778931862957161709568), (-2630471/37778931862957161709568)), (1690316337/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-12769/9444732965739290427392), (-267297/37778931862957161709568)), (1689310181/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((7047/37778931862957161709568), (-911/2361183241434822606848)), (1689058447/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((377/18889465931478580854784), (-113/9444732965739290427392)), (422250055/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((45/37778931862957161709568), (-1/37778931862957161709568)), (844493843/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/18889465931478580854784), (1/37778931862957161709568)), (844492581/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1051911645/2251799813685248), (-113483703/1125899906842624)), (10273/2251799813685248), by norm_num⟩
  | 1 => ⟨((-32877315/4503599627370496), (-652209605/2251799813685248)), (54471/4503599627370496), by norm_num⟩
  | 2 => ⟨((-465439/140737488355328), (-1719329487/36028797018963968)), (650903/36028797018963968), by norm_num⟩
  | 3 => ⟨((21063915/1125899906842624), (-771572997/18014398509481984)), (191649/9007199254740992), by norm_num⟩
  | 4 => ⟨((943120951/72057594037927936), (159042509/72057594037927936)), (1543421/72057594037927936), by norm_num⟩
  | 5 => ⟨((87025029/288230376151711744), (5903941/4503599627370496)), (5683039/288230376151711744), by norm_num⟩
  | 6 => ⟨((577087451/4611686018427387904), (591573017/4611686018427387904)), (80661763/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-299540381/18446744073709551616), (922808757/18446744073709551616)), (287848963/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-842178837/147573952589676412928), (-5135843/9223372036854775808)), (1058003617/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-226305/2305843009213693952), (-3466943/18446744073709551616)), (2009970279/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-3870795/147573952589676412928), (-1058217/73786976294838206464)), (1957300689/147573952589676412928), by norm_num⟩
  | 11 => ⟨((11959/18446744073709551616), (-267835/73786976294838206464)), (1933936983/147573952589676412928), by norm_num⟩
  | 12 => ⟨((11459/73786976294838206464), (-3427/147573952589676412928)), (1924550105/147573952589676412928), by norm_num⟩
  | 13 => ⟨((83/18446744073709551616), (-687/147573952589676412928)), (1921098433/147573952589676412928), by norm_num⟩
  | 14 => ⟨((33/36893488147419103232), (1/4611686018427387904)), (959963829/73786976294838206464), by norm_num⟩
  | 15 => ⟨((1/73786976294838206464), (1/18446744073709551616)), (1919559337/147573952589676412928), by norm_num⟩
  | 16 => ⟨(0, (1/147573952589676412928)), (239931469/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-262977903/562949953421312), (-113483715/1125899906842624)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((-2054829/281474976710656), (-326104795/1125899906842624)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((-1861757/562949953421312), (-53729043/1125899906842624)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((10531959/562949953421312), (-48223313/1125899906842624)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((14736263/1125899906842624), (1242521/562949953421312)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((169971/562949953421312), (92249/70368744177664)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((140891/1125899906842624), (144427/1125899906842624)), (1/34359738368), by norm_num⟩
  | 7 => ⟨((-18283/1125899906842624), (14081/281474976710656)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-6425/1125899906842624), (-627/1125899906842624)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((-111/1125899906842624), (-53/281474976710656)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((-15/562949953421312), (-1/70368744177664)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1/1125899906842624), (-1/281474976710656)), (1/34359738368), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨41,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨41,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(459/1073741824)) (L:=(70524539399643/147573952589676412928)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile041
