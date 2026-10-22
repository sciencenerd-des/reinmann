/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile014Gamma
import XiBand97.Tile014Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile014
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-943389723/562949953421312), (977943683/562949953421312)), (1137/281474976710656), by norm_num⟩
  | 1 => ⟨((-227571943/70368744177664), (54913941/70368744177664)), (157/17592186044416), by norm_num⟩
  | 2 => ⟨((-605116765/281474976710656), (-405446971/562949953421312)), (5541/562949953421312), by norm_num⟩
  | 3 => ⟨((-11473409/17592186044416), (-440367193/562949953421312)), (1023/140737488355328), by norm_num⟩
  | 4 => ⟨((-229711659/4503599627370496), (-1510288413/4503599627370496)), (9151/2251799813685248), by norm_num⟩
  | 5 => ⟨((602102781/18014398509481984), (-1492707063/18014398509481984)), (16649/9007199254740992), by norm_num⟩
  | 6 => ⟨((550196683/36028797018963968), (-215286493/18014398509481984)), (1631/2251799813685248), by norm_num⟩
  | 7 => ⟨((1016382199/288230376151711744), (-156761549/288230376151711744)), (76213/288230376151711744), by norm_num⟩
  | 8 => ⟨((1234104739/2305843009213693952), (221162349/1152921504606846976)), (30289/288230376151711744), by norm_num⟩
  | 9 => ⟨((498737347/9223372036854775808), (1082121049/18446744073709551616)), (1050471/18446744073709551616), by norm_num⟩
  | 10 => ⟨((406772519/147573952589676412928), (1417911317/147573952589676412928)), (6494367/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-111861305/590295810358705651712), (1316794691/1180591620717411303424)), (48249623/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-621096075/9444732965739290427392), (114067873/1180591620717411303424)), (23714645/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-177705635/18889465931478580854784), (112018291/18889465931478580854784)), (756192201/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-36581005/37778931862957161709568), (49033/295147905179352825856)), (188921433/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((-375139/4722366482869645213696), (-624523/37778931862957161709568)), (1511192443/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-100613/18889465931478580854784), (-127247/37778931862957161709568)), (1511162731/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile014Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((723179203/67108864), (289831719/33554432)), (3523/16777216), by norm_num⟩
  | 1 => ⟨((-68670031/8388608), (896033277/67108864)), (7501/33554432), by norm_num⟩
  | 2 => ⟨((315011971/67108864), (-130329075/16777216)), (15489/67108864), by norm_num⟩
  | 3 => ⟨((-258472197/134217728), (201834219/67108864)), (15337/67108864), by norm_num⟩
  | 4 => ⟨((44548707/67108864), (-57430021/67108864)), (236909/1073741824), by norm_num⟩
  | 5 => ⟨((-6418269/33554432), (25144861/134217728)), (455777/2147483648), by norm_num⟩
  | 6 => ⟨((386799/8388608), (-17142099/536870912)), (1770915/8589934592), by norm_num⟩
  | 7 => ⟨((-10077623/1073741824), (2196581/536870912)), (27858351/137438953472), by norm_num⟩
  | 8 => ⟨((437805/268435456), (-174459/536870912)), (110525115/549755813888), by norm_num⟩
  | 9 => ⟨((-1048053/4294967296), (-35623/4294967296)), (881199575/4398046511104), by norm_num⟩
  | 10 => ⟨((135463/4294967296), (77389/8589934592)), (1760218541/8796093022208), by norm_num⟩
  | 11 => ⟨((-60205/17179869184), (-71225/34359738368)), (1759506221/8796093022208), by norm_num⟩
  | 12 => ⟨((90105/274877906944), (46415/137438953472)), (1759294765/8796093022208), by norm_num⟩
  | 13 => ⟨((-3331/137438953472), (-24663/549755813888)), (1759237269/8796093022208), by norm_num⟩
  | 14 => ⟨((1203/1099511627776), (1399/274877906944)), (1759222869/8796093022208), by norm_num⟩
  | 15 => ⟨((11/274877906944), (-2207/4398046511104)), (439804879/2199023255552), by norm_num⟩
  | 16 => ⟨((-151/8796093022208), (189/4398046511104)), (1759218789/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile014Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26103/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26103/1280))
  have he : value ((69/80), (26103/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1566618903/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((860665113361555/2251799813685248), (1071639600063069/2251799813685248)), (20283377/1125899906842624), by norm_num⟩
  | 1 => ⟨((-939587667/4294967296), (-1169908407/4294967296)), (47/4294967296), by norm_num⟩
  | 2 => ⟨((268893521/4294967296), (669614559/8589934592)), (29/8589934592), by norm_num⟩
  | 3 => ⟨((-410413933/34359738368), (-127754633/8589934592)), (47/68719476736), by norm_num⟩
  | 4 => ⟨((469813095/274877906944), (292489093/137438953472)), (7/68719476736), by norm_num⟩
  | 5 => ⟨((-860494545/4398046511104), (-267856805/1099511627776)), (27/2199023255552), by norm_num⟩
  | 6 => ⟨((656689215/35184372088832), (817663173/35184372088832)), (43/35184372088832), by norm_num⟩
  | 7 => ⟨((-859122023/562949953421312), (-1069718253/562949953421312)), (59/562949953421312), by norm_num⟩
  | 8 => ⟨((3841651/35184372088832), (612269227/4503599627370496)), (35/4503599627370496), by norm_num⟩
  | 9 => ⟨((-500355153/72057594037927936), (-623007007/72057594037927936)), (37/72057594037927936), by norm_num⟩
  | 10 => ⟨((229108599/576460752303423488), (35658737/72057594037927936)), (71/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-762959885/36893488147419103232), (-949983929/36893488147419103232)), (61/36893488147419103232), by norm_num⟩
  | 12 => ⟨((291127661/295147905179352825856), (362491665/295147905179352825856)), (49/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-410169273/9444732965739290427392), (-1021427797/18889465931478580854784)), (71/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((134152293/75557863725914323419136), (334073979/151115727451828646838272)), (49/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-163806015/2417851639229258349412352), (-815838865/9671406556917033397649408)), (31/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((187513641/77371252455336267181195264), (933915131/309485009821345068724781056)), (73/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (1164730484683/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781208404971865/633825300114114700748351602688), (690997215125/316912650057057350374175801344)), (23085/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946243058300651/19807040628566084398385987584), (97167091831/2475880078570760549798248448)), (6493/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236554039930847/309485009821345068724781056), (825878601829/1237940039285380274899124224)), (13799/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774098133476811/154742504910672534362390528), (825831712397/77371252455336267181195264)), (27601/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776139346722609/4835703278458516698824704), (1548334820027/9671406556917033397649408)), (25879/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157646603826547/75557863725914323419136), (1354693326045/604462909807314587353088)), (22647/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((461832377113/18446744073709551616), (1100594912721/37778931862957161709568)), (36807/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300443723060531/4722366482869645213696), (1650728891767/4722366482869645213696)), (13805/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625440251929531/590295810358705651712), (1134743286271/295147905179352825856)), (9493/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1828462939296481/73786976294838206464), (2836459729991/73786976294838206464)), (47477/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914133098450791/4611686018427387904), (1595234634977/4611686018427387904)), (53427/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799755750786827/576460752303423488), (1594892174733/576460752303423488)), (6681/144115188075855872), by norm_num⟩
  | 5 => ⟨((1199412098651501/144115188075855872), (348786344121/18014398509481984)), (46791/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498877210049807/36028797018963968), (2091947490489/18014398509481984)), (8779/4503599627370496), by norm_num⟩
  | 3 => ⟨((1498294860577063/9007199254740992), (653396452607/1125899906842624)), (87871/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122992370689621/2251799813685248), (2611562886949/1125899906842624)), (43997/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121532312916651/1125899906842624), (3912286696007/562949953421312)), (132297/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117139636086523/1125899906842624), (15608681877893/1125899906842624)), (265819/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117139636086523/1125899906842624), (15608681877893/1125899906842624)), (1014019016746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1108231138471861/1125899906842624), (15487235665343/562949953421312)), (534873/1125899906842624), by norm_num⟩
  | 2 => ⟨((1089987512163423/1125899906842624), (60976776741431/1125899906842624)), (1082389/1125899906842624), by norm_num⟩
  | 3 => ⟨((1051918205315191/1125899906842624), (118063648067123/1125899906842624)), (1106485/562949953421312), by norm_num⟩
  | 4 => ⟨((30325544455551/35184372088832), (220611619261981/1125899906842624)), (1149807/281474976710656), by norm_num⟩
  | 5 => ⟨((793179288906051/1125899906842624), (11884124737343/35184372088832)), (4865277/562949953421312), by norm_num⟩
  | 6 => ⟨((860665113361555/2251799813685248), (1071639600063069/2251799813685248)), (20283377/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1566618903/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-825981861/562949953421312), (-150361301/1125899906842624)), (3973/1125899906842624), by norm_num⟩
  | 1 => ⟨((-432152853/562949953421312), (-655477479/562949953421312)), (5491/562949953421312), by norm_num⟩
  | 2 => ⟨((452133695/2251799813685248), (-171717113/281474976710656)), (30411/2251799813685248), by norm_num⟩
  | 3 => ⟨((809176929/4503599627370496), (-147017137/2251799813685248)), (56331/4503599627370496), by norm_num⟩
  | 4 => ⟨((1258243179/36028797018963968), (393311543/18014398509481984)), (314575/36028797018963968), by norm_num⟩
  | 5 => ⟨((50340269/72057594037927936), (976187269/144115188075855872)), (708673/144115188075855872), by norm_num⟩
  | 6 => ⟨((-371477809/576460752303423488), (711900225/1152921504606846976)), (2699911/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-860257261/9223372036854775808), (-15372115/1152921504606846976)), (18174873/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-301531079/73786976294838206464), (-254753297/36893488147419103232)), (28846671/73786976294838206464), by norm_num⟩
  | 9 => ⟨((205970379/1180591620717411303424), (-606055537/1180591620717411303424)), (392782901/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((232925939/9444732965739290427392), (-242857893/18889465931478580854784)), (1726411019/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((20346407/18889465931478580854784), (-1797021/18889465931478580854784)), (651077157/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((80561/1180591620717411303424), (-14439/1180591620717411303424)), (1186588535/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((104923/18889465931478580854784), (4677/2361183241434822606848)), (1157693455/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((79/590295810358705651712), (5905/18889465931478580854784)), (1151009729/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-25/4722366482869645213696), (193/18889465931478580854784)), (574785055/9444732965739290427392), by norm_num⟩
  | 16 => ⟨(0, (1/9444732965739290427392)), (1149279763/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1031446139/70368744177664), (-496544473/35184372088832)), (7119/17592186044416), by norm_num⟩
  | 1 => ⟨((548137667/35184372088832), (-1325585751/35184372088832)), (36203/35184372088832), by norm_num⟩
  | 2 => ⟨((1501608351/70368744177664), (366832669/70368744177664)), (52351/35184372088832), by norm_num⟩
  | 3 => ⟨((-118007393/281474976710656), (1369505343/281474976710656)), (483333/281474976710656), by norm_num⟩
  | 4 => ⟨((-355766235/1125899906842624), (664035857/4503599627370496)), (7697849/4503599627370496), by norm_num⟩
  | 5 => ⟨((-399784721/9007199254740992), (87567177/1125899906842624)), (13910035/9007199254740992), by norm_num⟩
  | 6 => ⟨((-365391311/18014398509481984), (-89016481/18014398509481984)), (24074189/18014398509481984), by norm_num⟩
  | 7 => ⟨((85260497/576460752303423488), (-1135692901/576460752303423488)), (670300315/576460752303423488), by norm_num⟩
  | 8 => ⟨((3887273/72057594037927936), (-27127167/1152921504606846976)), (18890029/18014398509481984), by norm_num⟩
  | 9 => ⟨((3146397/1152921504606846976), (-8235935/1152921504606846976)), (1136174659/1152921504606846976), by norm_num⟩
  | 10 => ⟨((881195/1152921504606846976), (66221/1152921504606846976)), (1101160341/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1307/144115188075855872), (17919/1152921504606846976)), (33943337/36028797018963968), by norm_num⟩
  | 12 => ⟨((2329/1152921504606846976), (209/288230376151711744)), (1080407525/1152921504606846976), by norm_num⟩
  | 13 => ⟨((5/576460752303423488), (47/288230376151711744)), (1078371483/1152921504606846976), by norm_num⟩
  | 14 => ⟨((-3/1152921504606846976), (5/576460752303423488)), (1077710975/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-1/1152921504606846976), (1/576460752303423488)), (269378065/288230376151711744), by norm_num⟩
  | 16 => ⟨((-1/1152921504606846976), 0), (1077456493/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-16503138127/1125899906842624), (-15889423943/1125899906842624)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((548137725/35184372088832), (-42418744105/1125899906842624)), (1/536870912), by norm_num⟩
  | 2 => ⟨((24025733725/1125899906842624), (5869323749/1125899906842624)), (1/268435456), by norm_num⟩
  | 3 => ⟨((-472029751/1125899906842624), (2739010681/562949953421312)), (1/268435456), by norm_num⟩
  | 4 => ⟨((-88941563/281474976710656), (41502263/281474976710656)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-49973113/1125899906842624), (87567113/1125899906842624)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-11418465/562949953421312), (-695437/140737488355328)), (1/134217728), by norm_num⟩
  | 7 => ⟨((41629/281474976710656), (-2218165/1125899906842624)), (1/134217728), by norm_num⟩
  | 8 => ⟨((60749/1125899906842624), (-3311/140737488355328)), (1/134217728), by norm_num⟩
  | 9 => ⟨((3071/1125899906842624), (-4021/562949953421312)), (1/134217728), by norm_num⟩
  | 10 => ⟨((215/281474976710656), (65/1125899906842624)), (1/134217728), by norm_num⟩
  | 11 => ⟨((5/562949953421312), (17/1125899906842624)), (1/134217728), by norm_num⟩
  | 12 => ⟨((1/562949953421312), (1/1125899906842624)), (1/134217728), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨14,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨14,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(34575/536870912)) (L:=(12010971924676839/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile014
