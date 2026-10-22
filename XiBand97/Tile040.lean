/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile040Gamma
import XiBand97.Tile040Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile040
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-403670487/72057594037927936), (-272746485/18014398509481984)), (611/9007199254740992), by norm_num⟩
  | 1 => ⟨((292886239/72057594037927936), (-1726227087/72057594037927936)), (7347/72057594037927936), by norm_num⟩
  | 2 => ⟨((414503681/36028797018963968), (-1012801923/72057594037927936)), (7853/72057594037927936), by norm_num⟩
  | 3 => ⟨((603532363/72057594037927936), (-235450953/72057594037927936)), (13167/144115188075855872), by norm_num⟩
  | 4 => ⟨((59168639/18014398509481984), (32278517/72057594037927936)), (9921/144115188075855872), by norm_num⟩
  | 5 => ⟨((899973883/1152921504606846976), (666192461/1152921504606846976)), (61197/1152921504606846976), by norm_num⟩
  | 6 => ⟨((230440465/2305843009213693952), (491776227/2305843009213693952)), (103745/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-90337353/36893488147419103232), (1792065629/36893488147419103232)), (1536535/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-163296049/36893488147419103232), (277665861/36893488147419103232)), (2986897/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-86248743/73786976294838206464), (438134073/590295810358705651712)), (740181/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1846056897/9444732965739290427392), (186503773/9444732965739290427392)), (378069471/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-446228957/18889465931478580854784), (-331347085/37778931862957161709568)), (1511400265/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-19350321/9444732965739290427392), (-80067303/37778931862957161709568)), (377801481/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-3895241/37778931862957161709568), (-5659359/18889465931478580854784)), (1511166329/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((28337/9444732965739290427392), (-592301/18889465931478580854784)), (755579425/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((53893/37778931862957161709568), (-95953/37778931862957161709568)), (377789383/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((7557/37778931862957161709568), (-5785/37778931862957161709568)), (1511157315/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile040Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-307919735/16777216), (893359999/16777216)), (1841/8388608), by norm_num⟩
  | 1 => ⟨((210538563/8388608), (-866316849/33554432)), (1027/4194304), by norm_num⟩
  | 2 => ⟨((-275404545/16777216), (954236251/67108864)), (8665/33554432), by norm_num⟩
  | 3 => ⟨((1037918191/134217728), (-756819895/134217728)), (16991/67108864), by norm_num⟩
  | 4 => ⟨((-379187759/134217728), (233322275/134217728)), (3987/16777216), by norm_num⟩
  | 5 => ⟨((227382543/268435456), (-114705429/268435456)), (238165/1073741824), by norm_num⟩
  | 6 => ⟨((-57762769/268435456), (2810565/33554432)), (452449/2147483648), by norm_num⟩
  | 7 => ⟨((50730009/1073741824), (-13581213/1073741824)), (1757027/8589934592), by norm_num⟩
  | 8 => ⟨((-19515803/2147483648), (2712695/2147483648)), (27722863/137438953472), by norm_num⟩
  | 9 => ⟨((13280619/8589934592), (-18603/8589934592)), (110268923/549755813888), by norm_num⟩
  | 10 => ⟨((-125719/536870912), (-598477/17179869184)), (880387799/4398046511104), by norm_num⟩
  | 11 => ⟨((2178115/68719476736), (346685/34359738368)), (1759654701/8796093022208), by norm_num⟩
  | 12 => ⟨((-527195/137438953472), (-68487/34359738368)), (1759331245/8796093022208), by norm_num⟩
  | 13 => ⟨((454461/1099511627776), (352691/1099511627776)), (1759245621/8796093022208), by norm_num⟩
  | 14 => ⟨((-86119/2199023255552), (-195949/4398046511104)), (1759224647/8796093022208), by norm_num⟩
  | 15 => ⟨((27817/8796093022208), (48249/8796093022208)), (54975621/274877906944), by norm_num⟩
  | 16 => ⟨((-219/1099511627776), (-5341/8796093022208)), (1759218855/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile040Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6939/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6939/256))
  have he : value ((69/80), (6939/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-33129281/67108864), (-1041141685/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-674375001944927/1125899906842624), (-132315272114489/1125899906842624)), (28555395/562949953421312), by norm_num⟩
  | 1 => ⟨((736214847/2147483648), (288897031/4294967296)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((-421383569/4294967296), (-330709065/17179869184)), (37/4294967296), by norm_num⟩
  | 3 => ⟨((1286320973/68719476736), (63095425/17179869184)), (115/68719476736), by norm_num⟩
  | 4 => ⟨((-1472490061/549755813888), (-288908875/549755813888)), (67/274877906944), by norm_num⟩
  | 5 => ⟨((84280169/274877906944), (264578099/4398046511104)), (125/4398046511104), by norm_num⟩
  | 6 => ⟨((-128637371/4398046511104), (-100956819/17592186044416)), (97/35184372088832), by norm_num⟩
  | 7 => ⟨((673165911/281474976710656), (264156087/562949953421312)), (129/562949953421312), by norm_num⟩
  | 8 => ⟨((-1541186273/9007199254740992), (-302387367/9007199254740992)), (75/4503599627370496), by norm_num⟩
  | 9 => ⟨((1568215099/144115188075855872), (307690539/144115188075855872)), (155/144115188075855872), by norm_num⟩
  | 10 => ⟨((-1436146153/2305843009213693952), (-281778045/2305843009213693952)), (145/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1195635943/36893488147419103232), (234588909/36893488147419103232)), (123/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-912453465/590295810358705651712), (-89513645/295147905179352825856)), (3/18446744073709551616), by norm_num⟩
  | 13 => ⟨((1285554155/18889465931478580854784), (15764453/1180591620717411303424)), (69/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-1681842585/604462909807314587353088), (-82496185/151115727451828646838272)), (183/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((513401459/4835703278458516698824704), (201463143/9671406556917033397649408)), (57/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-1175411987/309485009821345068724781056), (-230620881/309485009821345068724781056)), (133/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98958294602637/633825300114114700748351602688), (-3839903050049/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890599183931085/316912650057057350374175801344), (-2278091239869/316912650057057350374175801344)), (11581/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946237106024671/19807040628566084398385987584), (-1281361186323/9903520314283042199192993792)), (52129/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892418927809129/2475880078570760549798248448), (-1361376667871/618970019642690137449562112)), (55403/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774083905947745/154742504910672534362390528), (-21270286021/604462909807314587353088)), (55423/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776132233569365/4835703278458516698824704), (-1276133833789/2417851639229258349412352)), (25989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157644936843731/75557863725914323419136), (-1116533701465/151115727451828646838272)), (45501/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891642081496829/75557863725914323419136), (-7256842893633/75557863725914323419136)), (9247/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1300424765685325/4722366482869645213696), (-5442083632669/4722366482869645213696)), (55515/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812705910070793/295147905179352825856), (-7481972417389/590295810358705651712)), (38193/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828423852541477/73786976294838206464), (-146111321085/1152921504606846976)), (95561/73786976294838206464), by norm_num⟩
  | 7 => ⟨((457054337224907/2305843009213693952), (-5259083930425/4611686018427387904)), (3363/288230376151711744), by norm_num⟩
  | 6 => ⟨((1599456561947663/1152921504606846976), (-2628963415505/288230376151711744)), (107753/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199357177023563/144115188075855872), (-9198761435997/144115188075855872)), (47219/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498781137772277/36028797018963968), (-862056470133/2251799813685248)), (141965/36028797018963968), by norm_num⟩
  | 3 => ⟨((374537708372841/2251799813685248), (-17231922251849/9007199254740992)), (44499/2251799813685248), by norm_num⟩
  | 2 => ⟨((561406239790477/1125899906842624), (-17218032546859/2251799813685248)), (22351/281474976710656), by norm_num⟩
  | 1 => ⟨((1121172960614727/1125899906842624), (-25792048634097/1125899906842624)), (135121/562949953421312), by norm_num⟩
  | 0 => ⟨((1116063740387501/1125899906842624), (-51442445007857/1125899906842624)), (274315/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116063740387501/1125899906842624), (-51442445007857/1125899906842624)), (1046428682567405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1103963096457641/1125899906842624), (-50993029878785/562949953421312)), (1137809/1125899906842624), by norm_num⟩
  | 2 => ⟨((1073215615892547/1125899906842624), (-49999491802613/281474976710656)), (2437411/1125899906842624), by norm_num⟩
  | 3 => ⟨((493735084509031/562949953421312), (-381278904550127/1125899906842624)), (5512649/1125899906842624), by norm_num⟩
  | 4 => ⟨((736942712760693/1125899906842624), (-668801093296053/1125899906842624)), (13403383/1125899906842624), by norm_num⟩
  | 5 => ⟨((170156616791483/2251799813685248), (-437754803065103/562949953421312)), (66939247/2251799813685248), by norm_num⟩
  | 6 => ⟨((-674375001944927/1125899906842624), (-132315272114489/1125899906842624)), (28555395/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-33129281/67108864), (-1041141685/67108864)), (1/33554432), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((56786213/36028797018963968), (1401803857/144115188075855872)), (7157/144115188075855872), by norm_num⟩
  | 1 => ⟨((-13853095/2251799813685248), (1196717217/144115188075855872)), (14831/144115188075855872), by norm_num⟩
  | 2 => ⟨((-760890269/144115188075855872), (207683383/288230376151711744)), (18759/144115188075855872), by norm_num⟩
  | 3 => ⟨((-818785071/576460752303423488), (-159066579/144115188075855872)), (72209/576460752303423488), by norm_num⟩
  | 4 => ⟨((-119135883/2305843009213693952), (-127855879/288230376151711744)), (237243/2305843009213693952), by norm_num⟩
  | 5 => ⟨((500679975/9223372036854775808), (-312567127/4611686018427387904)), (738849/9223372036854775808), by norm_num⟩
  | 6 => ⟨((252129185/18446744073709551616), (-109879893/73786976294838206464)), (4769039/73786976294838206464), by norm_num⟩
  | 7 => ⟨((840152539/590295810358705651712), (334448401/295147905179352825856)), (16655727/295147905179352825856), by norm_num⟩
  | 8 => ⟨((30397089/1180591620717411303424), (479905089/2361183241434822606848)), (249426699/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-111346623/9444732965739290427392), (605320103/37778931862957161709568)), (971780541/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-974185/590295810358705651712), (12198987/37778931862957161709568)), (1926184233/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-2038361/18889465931478580854784), (-1182063/18889465931478580854784)), (240120141/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-109409/37778931862957161709568), (-289245/37778931862957161709568)), (1919535429/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((2449/18889465931478580854784), (-8747/18889465931478580854784)), (1919178547/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((729/37778931862957161709568), (-81/4722366482869645213696)), (959547983/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((3/2361183241434822606848), (-11/37778931862957161709568)), (959539093/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/18889465931478580854784), (1/37778931862957161709568)), (479768651/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-38482769/70368744177664), (-106506491/1125899906842624)), (6797/1125899906842624), by norm_num⟩
  | 1 => ⟨((-173690905/4503599627370496), (-622743997/2251799813685248)), (71327/4503599627370496), by norm_num⟩
  | 2 => ⟨((-411281919/9007199254740992), (-1159696673/18014398509481984)), (214883/9007199254740992), by norm_num⟩
  | 3 => ⟨((188087713/9007199254740992), (-1052636263/18014398509481984)), (504971/18014398509481984), by norm_num⟩
  | 4 => ⟨((1061702155/72057594037927936), (116860405/72057594037927936)), (2014567/72057594037927936), by norm_num⟩
  | 5 => ⟨((19616525/36028797018963968), (145792779/144115188075855872)), (913221/36028797018963968), by norm_num⟩
  | 6 => ⟨((1087827993/4611686018427387904), (742889419/4611686018427387904)), (101861049/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-316705421/18446744073709551616), (1166706409/18446744073709551616)), (178770545/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-224089601/36893488147419103232), (-18961229/73786976294838206464)), (1298307763/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-10398213/73786976294838206464), (-7248559/73786976294838206464)), (1224479667/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-2816013/73786976294838206464), (-597131/36893488147419103232)), (1188285439/73786976294838206464), by norm_num⟩
  | 11 => ⟨((9995/18446744073709551616), (-303709/73786976294838206464)), (586216867/36893488147419103232), by norm_num⟩
  | 12 => ⟨((305/2305843009213693952), (-2975/73786976294838206464)), (1166145173/73786976294838206464), by norm_num⟩
  | 13 => ⟨((373/73786976294838206464), (-605/73786976294838206464)), (581931023/36893488147419103232), by norm_num⟩
  | 14 => ⟨((75/73786976294838206464), (11/73786976294838206464)), (1163097475/73786976294838206464), by norm_num⟩
  | 15 => ⟨((1/36893488147419103232), (3/73786976294838206464)), (581429987/36893488147419103232), by norm_num⟩
  | 16 => ⟨(0, 0), (1162791427/73786976294838206464), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-307862143/562949953421312), (-53253257/562949953421312)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((-43422711/1125899906842624), (-311371983/1125899906842624)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-51410243/1125899906842624), (-72481047/1125899906842624)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((23510971/1125899906842624), (-32894881/562949953421312)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((16589093/1125899906842624), (228243/140737488355328)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((306509/562949953421312), (569503/562949953421312)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((132791/562949953421312), (90685/562949953421312)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((-9665/562949953421312), (35605/562949953421312)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-6839/1125899906842624), (-289/1125899906842624)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((-159/1125899906842624), (-111/1125899906842624)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-43/1125899906842624), (-9/562949953421312)), (1/17179869184), by norm_num⟩
  | 11 => ⟨((1/1125899906842624), (-5/1125899906842624)), (1/17179869184), by norm_num⟩
  | 12 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 13 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 14 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 15 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 16 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨40,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨40,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(253/536870912)) (L:=(327610800893747/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile040
