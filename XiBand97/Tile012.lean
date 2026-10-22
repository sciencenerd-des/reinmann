/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile012Gamma
import XiBand97.Tile012Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile012
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15469473/35184372088832), (254957267/70368744177664)), (1389/281474976710656), by norm_num⟩
  | 1 => ⟨((-447697927/140737488355328), (540244963/140737488355328)), (3003/281474976710656), by norm_num⟩
  | 2 => ⟨((-225209517/70368744177664), (9153131/8796093022208)), (51/4398046511104), by norm_num⟩
  | 3 => ⟨((-1635674753/1125899906842624), (-404241985/1125899906842624)), (9583/1125899906842624), by norm_num⟩
  | 4 => ⟨((-781498211/2251799813685248), (-788715851/2251799813685248)), (5355/1125899906842624), by norm_num⟩
  | 5 => ⟨((-278652479/9007199254740992), (-1122536509/9007199254740992)), (9747/4503599627370496), by norm_num⟩
  | 6 => ⟨((276572469/36028797018963968), (-952770979/36028797018963968)), (30483/36028797018963968), by norm_num⟩
  | 7 => ⟨((1029661077/288230376151711744), (-126219979/36028797018963968)), (43931/144115188075855872), by norm_num⟩
  | 8 => ⟨((436283793/576460752303423488), (-124421057/576460752303423488)), (134741/1152921504606846976), by norm_num⟩
  | 9 => ⟨((246107063/2305843009213693952), (25409051/1152921504606846976)), (553527/9223372036854775808), by norm_num⟩
  | 10 => ⟨((195247933/18446744073709551616), (307616829/36893488147419103232)), (1650275/36893488147419103232), by norm_num⟩
  | 11 => ⟨((196798639/295147905179352825856), (199160159/147573952589676412928)), (24217087/590295810358705651712), by norm_num⟩
  | 12 => ⟨((24487199/4722366482869645213696), (1449646597/9444732965739290427392)), (189864869/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((-24778435/4722366482869645213696), (31772135/2361183241434822606848)), (1512604959/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-4099873/4722366482869645213696), (34616979/37778931862957161709568)), (755705039/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-1761367/18889465931478580854784), (836971/18889465931478580854784)), (755599407/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-37373/4722366482869645213696), (13705/18889465931478580854784)), (755581863/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile012Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((547727693/33554432), (1022596837/67108864)), (7027/33554432), by norm_num⟩
  | 1 => ⟨((-244478137/16777216), (12201081/2097152)), (3721/16777216), by norm_num⟩
  | 2 => ⟨((276420693/33554432), (-221503883/67108864)), (1915/8388608), by norm_num⟩
  | 3 => ⟨((-106126997/33554432), (148520409/134217728)), (30353/134217728), by norm_num⟩
  | 4 => ⟨((64240211/67108864), (-30741593/134217728)), (235053/1073741824), by norm_num⟩
  | 5 => ⟨((-63465689/268435456), (1421635/67108864)), (453553/2147483648), by norm_num⟩
  | 6 => ⟨((26065977/536870912), (2331979/536870912)), (1766371/8589934592), by norm_num⟩
  | 7 => ⟨((-4497815/536870912), (-2716543/1073741824)), (27826351/137438953472), by norm_num⟩
  | 8 => ⟨((2614895/2147483648), (1488391/2147483648)), (110475451/549755813888), by norm_num⟩
  | 9 => ⟨((-633405/4294967296), (-599635/4294967296)), (881063383/4398046511104), by norm_num⟩
  | 10 => ⟨((245539/17179869184), (98217/4294967296)), (1760133037/8796093022208), by norm_num⟩
  | 11 => ⟨((-32847/34359738368), (-217897/68719476736)), (1759481389/8796093022208), by norm_num⟩
  | 12 => ⟨((891/137438953472), (52087/137438953472)), (1759288205/8796093022208), by norm_num⟩
  | 13 => ⟨((11813/1099511627776), (-21573/549755813888)), (1759235661/8796093022208), by norm_num⟩
  | 14 => ⟨((-4803/2199023255552), (15347/4398046511104)), (1759222511/8796093022208), by norm_num⟩
  | 15 => ⟨((41/137438953472), (-2269/8796093022208)), (879609721/4398046511104), by norm_num⟩
  | 16 => ⟨((-145/4398046511104), (63/4398046511104)), (879609387/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile012Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25387/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25387/1280))
  have he : value ((69/80), (25387/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-95227929/8388608)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((59957148843673/281474976710656), (1288054676302029/2251799813685248)), (47405637/2251799813685248), by norm_num⟩
  | 1 => ⟨((-523641511/4294967296), (-1406168635/4294967296)), (55/4294967296), by norm_num⟩
  | 2 => ⟨((74928511/2147483648), (804841631/8589934592)), (33/8589934592), by norm_num⟩
  | 3 => ⟨((-228727749/34359738368), (-1228435025/68719476736)), (13/17179869184), by norm_num⟩
  | 4 => ⟨((130915745/137438953472), (703113143/274877906944)), (31/274877906944), by norm_num⟩
  | 5 => ⟨((-479562131/4398046511104), (-1287799405/4398046511104)), (59/4398046511104), by norm_num⟩
  | 6 => ⟨((182989701/17592186044416), (982788311/35184372088832)), (47/35184372088832), by norm_num⟩
  | 7 => ⟨((-478797211/562949953421312), (-321436329/140737488355328)), (1/8796093022208), by norm_num⟩
  | 8 => ⟨((548093477/9007199254740992), (1471831089/9007199254740992)), (19/2251799813685248), by norm_num⟩
  | 9 => ⟨((-557705763/144115188075855872), (-1497643587/144115188075855872)), (5/9007199254740992), by norm_num⟩
  | 10 => ⟨((127684491/576460752303423488), (685758949/1152921504606846976)), (19/576460752303423488), by norm_num⟩
  | 11 => ⟨((-425205099/36893488147419103232), (-1141830929/36893488147419103232)), (65/36893488147419103232), by norm_num⟩
  | 12 => ⟨((20281041/36893488147419103232), (871391993/590295810358705651712)), (13/147573952589676412928), by norm_num⟩
  | 13 => ⟨((-228591397/9444732965739290427392), (-306925679/4722366482869645213696)), (75/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((74764401/75557863725914323419136), (200769713/75557863725914323419136)), (51/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-365162855/9671406556917033397649408), (-980595587/9671406556917033397649408)), (1/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((418012833/309485009821345068724781056), (1122517075/309485009821345068724781056)), (19/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (1581783280053/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781207546239361/633825300114114700748351602688), (1876842507037/633825300114114700748351602688)), (2887/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1892485098098425/39614081257132168796771975168), (1055675688895/19807040628566084398385987584)), (25987/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892431173709327/2475880078570760549798248448), (2243197508457/2475880078570760549798248448)), (13807/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774096916223029/154742504910672534362390528), (2243069999587/154742504910672534362390528)), (13809/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552277476295233/9671406556917033397649408), (1051371318059/4835703278458516698824704)), (3237/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315292922411139/151115727451828646838272), (229970538313/75557863725914323419136)), (2833/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((7389310235085/295147905179352825856), (747340727683/18889465931478580854784)), (36835/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650221050566485/2361183241434822606848), (1120899915997/2361183241434822606848)), (27633/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625437819400159/590295810358705651712), (3082113402367/590295810358705651712)), (19003/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914229797578425/36893488147419103232), (3852099622297/73786976294838206464)), (11881/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828262017609521/9223372036854775808), (4332866514361/9223372036854775808)), (53487/9223372036854775808), by norm_num⟩
  | 6 => ⟨((6248073441733/4503599627370496), (4331934367057/1152921504606846976)), (53515/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299851849919669/36028797018963968), (947348408931/36028797018963968)), (46857/144115188075855872), by norm_num⟩
  | 4 => ⟨((749434495130829/18014398509481984), (1420497977325/9007199254740992)), (70349/36028797018963968), by norm_num⟩
  | 3 => ⟨((749141268862505/4503599627370496), (3549407960811/4503599627370496)), (88047/9007199254740992), by norm_num⟩
  | 2 => ⟨((17546515298139/35184372088832), (7093301955645/2251799813685248)), (88213/2251799813685248), by norm_num⟩
  | 1 => ⟨((280375391395589/281474976710656), (664134842703/70368744177664)), (132735/1125899906842624), by norm_num⟩
  | 0 => ⟨((279261893399469/281474976710656), (10598535094451/562949953421312)), (267137/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279261893399469/281474976710656), (10598535094451/562949953421312)), (1019046787742232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((553932884404555/562949953421312), (42060818511475/1125899906842624)), (540133/1125899906842624), by norm_num⟩
  | 2 => ⟨((1088549205659057/1125899906842624), (41387107995799/562949953421312)), (137915/140737488355328), by norm_num⟩
  | 3 => ⟨((261588040630465/281474976710656), (80028256969471/562949953421312)), (1147833/562949953421312), by norm_num⟩
  | 4 => ⟨((474835619872443/562949953421312), (297496213416299/1125899906842624)), (4919641/1125899906842624), by norm_num⟩
  | 5 => ⟨((180604745958835/281474976710656), (125465681317423/281474976710656)), (2724761/281474976710656), by norm_num⟩
  | 6 => ⟨((59957148843673/281474976710656), (1288054676302029/2251799813685248)), (47405637/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-95227929/8388608)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-152428731/70368744177664), (292889383/562949953421312)), (1115/281474976710656), by norm_num⟩
  | 1 => ⟨((-919603333/562949953421312), (-365840461/281474976710656)), (6077/562949953421312), by norm_num⟩
  | 2 => ⟨((451991/35184372088832), (-133746057/140737488355328)), (16581/1125899906842624), by norm_num⟩
  | 3 => ⟨((504034841/2251799813685248), (-751704455/4503599627370496)), (60833/4503599627370496), by norm_num⟩
  | 4 => ⟨((1025791419/18014398509481984), (294739351/18014398509481984)), (169123/18014398509481984), by norm_num⟩
  | 5 => ⟨((248852123/72057594037927936), (1293772667/144115188075855872)), (380295/72057594037927936), by norm_num⟩
  | 6 => ⟨((-752588317/1152921504606846976), (1205326027/1152921504606846976)), (723329/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1160584743/9223372036854775808), (103747341/9223372036854775808)), (9697299/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-517391447/73786976294838206464), (-279367961/36893488147419103232)), (30375669/73786976294838206464), by norm_num⟩
  | 9 => ⟨((200467595/2361183241434822606848), (-763742449/1180591620717411303424)), (400337781/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((426588605/18889465931478580854784), (-89359381/4722366482869645213696)), (837332251/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((15844945/18889465931478580854784), (-2793753/4722366482869645213696)), (1216508479/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((92135/1180591620717411303424), (-292497/4722366482869645213696)), (545843073/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((308553/37778931862957161709568), (23061/37778931862957161709568)), (2120959843/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((8101/37778931862957161709568), (13371/37778931862957161709568)), (526631605/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-93/18889465931478580854784), (161/18889465931478580854784)), (1051709093/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((15/37778931862957161709568), (-3/37778931862957161709568)), (1051395675/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-190378487/4398046511104), (-431266545/17592186044416)), (12097/17592186044416), by norm_num⟩
  | 1 => ⟨((381363451/17592186044416), (-145777307/2199023255552)), (897/549755813888), by norm_num⟩
  | 2 => ⟨((1053032823/35184372088832), (195436869/35184372088832)), (9659/4398046511104), by norm_num⟩
  | 3 => ⟨((18934569/281474976710656), (1478085599/281474976710656)), (42937/17592186044416), by norm_num⟩
  | 4 => ⟨((41108681/4503599627370496), (665414805/2251799813685248)), (5327267/2251799813685248), by norm_num⟩
  | 5 => ⟨((-555533209/9007199254740992), (1434183183/9007199254740992)), (4787217/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1021386511/36028797018963968), (-94994917/18014398509481984)), (67167635/36028797018963968), by norm_num⟩
  | 7 => ⟨((6321245/576460752303423488), (-1219038075/576460752303423488)), (59866793/36028797018963968), by norm_num⟩
  | 8 => ⟨((7966353/1152921504606846976), (-21787209/576460752303423488)), (1769785903/1152921504606846976), by norm_num⟩
  | 9 => ⟨((3316573/1152921504606846976), (-1671313/144115188075855872)), (846118913/576460752303423488), by norm_num⟩
  | 10 => ⟨((936097/1152921504606846976), (-11001/1152921504606846976)), (1656143529/1152921504606846976), by norm_num⟩
  | 11 => ⟨((15063/1152921504606846976), (-731/576460752303423488)), (205142181/144115188075855872), by norm_num⟩
  | 12 => ⟨((1721/576460752303423488), (697/1152921504606846976)), (1635484833/1152921504606846976), by norm_num⟩
  | 13 => ⟨((3/576460752303423488), (137/1152921504606846976)), (1633534507/1152921504606846976), by norm_num⟩
  | 14 => ⟨((7/1152921504606846976), 0), (1632912691/1152921504606846976), by norm_num⟩
  | 15 => ⟨(0, (1/576460752303423488)), (1632728193/1152921504606846976), by norm_num⟩
  | 16 => ⟨(0, 0), (1632676943/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6092111659/140737488355328), (-13800529191/562949953421312)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((6101814797/281474976710656), (-37318990731/562949953421312)), (1/268435456), by norm_num⟩
  | 2 => ⟨((8424262747/281474976710656), (6253978205/1125899906842624)), (1/134217728), by norm_num⟩
  | 3 => ⟨((75738343/1125899906842624), (5912343285/1125899906842624)), (1/134217728), by norm_num⟩
  | 4 => ⟨((5138497/562949953421312), (20794181/70368744177664)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-17360375/281474976710656), (179273065/1125899906842624)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-31918377/1125899906842624), (-742153/140737488355328)), (1/134217728), by norm_num⟩
  | 7 => ⟨((12373/1125899906842624), (-1190455/562949953421312)), (1/134217728), by norm_num⟩
  | 8 => ⟨((1943/281474976710656), (-2659/70368744177664)), (1/134217728), by norm_num⟩
  | 9 => ⟨((3237/1125899906842624), (-6527/562949953421312)), (1/134217728), by norm_num⟩
  | 10 => ⟨((57/70368744177664), (-5/562949953421312)), (1/134217728), by norm_num⟩
  | 11 => ⟨((15/1125899906842624), (-1/562949953421312)), (1/134217728), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨12,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨12,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(110191/1073741824)) (L:=(58730583468177393/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile012
