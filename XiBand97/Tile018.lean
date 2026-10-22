/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile018Gamma
import XiBand97.Tile018Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile018
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1435906345/1125899906842624), (-131253731/562949953421312)), (2191/1125899906842624), by norm_num⟩
  | 1 => ⟨((-375969605/281474976710656), (-687708953/562949953421312)), (2453/562949953421312), by norm_num⟩
  | 2 => ⟨((-12000297/35184372088832), (-677316811/562949953421312)), (5549/1125899906842624), by norm_num⟩
  | 3 => ⟨((42863207/281474976710656), (-1236762915/2251799813685248)), (8387/2251799813685248), by norm_num⟩
  | 4 => ⟨((628274889/4503599627370496), (-18720587/140737488355328)), (9577/4503599627370496), by norm_num⟩
  | 5 => ⟨((113084169/2251799813685248), (-53396413/4503599627370496)), (2227/2251799813685248), by norm_num⟩
  | 6 => ⟨((1574023063/144115188075855872), (232984269/72057594037927936)), (28955/72057594037927936), by norm_num⟩
  | 7 => ⟨((860142965/576460752303423488), (878924851/576460752303423488)), (91713/576460752303423488), by norm_num⟩
  | 8 => ⟨((219670233/2305843009213693952), (191887667/576460752303423488)), (171957/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-46103515/4611686018427387904), (894431969/18446744073709551616)), (451919/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-289807109/73786976294838206464), (730925487/147573952589676412928)), (194267/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-775268813/1180591620717411303424), (93433227/295147905179352825856)), (23883377/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-724254357/9444732965739290427392), (21398981/18889465931478580854784)), (378658423/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-64516691/9444732965739290427392), (-54943559/18889465931478580854784)), (1511804203/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-2186675/4722366482869645213696), (-9056827/18889465931478580854784)), (1511269919/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-791513/37778931862957161709568), (-61153/1180591620717411303424)), (1511175719/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-691/9444732965739290427392), (-83087/18889465931478580854784)), (23611877/590295810358705651712), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile018Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-230636409/134217728), (529198089/67108864)), (7097/33554432), by norm_num⟩
  | 1 => ⟨((437714687/67108864), (232766287/16777216)), (15235/67108864), by norm_num⟩
  | 2 => ⟨((-143698815/33554432), (-1098497203/134217728)), (15793/67108864), by norm_num⟩
  | 3 => ⟨((237285125/134217728), (467057855/134217728)), (977/4194304), by norm_num⟩
  | 4 => ⟨((-63072965/134217728), (-38633215/33554432)), (240469/1073741824), by norm_num⟩
  | 5 => ⟨((5498051/67108864), (82696467/268435456)), (460145/2147483648), by norm_num⟩
  | 6 => ⟨((-3719819/536870912), (-2294095/33554432)), (1779939/8589934592), by norm_num⟩
  | 7 => ⟨((-70183/67108864), (13751983/1073741824)), (27921583/137438953472), by norm_num⟩
  | 8 => ⟨((638459/1073741824), (-2197849/1073741824)), (110624187/549755813888), by norm_num⟩
  | 9 => ⟨((-82013/536870912), (1202325/4294967296)), (881471959/4398046511104), by norm_num⟩
  | 10 => ⟨((499195/17179869184), (-139547/4294967296)), (1760385965/8796093022208), by norm_num⟩
  | 11 => ⟨((-77983/17179869184), (213137/68719476736)), (1759552557/8796093022208), by norm_num⟩
  | 12 => ⟨((41675/68719476736), (-30187/137438953472)), (1759306701/8796093022208), by norm_num⟩
  | 13 => ⟨((-9703/137438953472), (6729/1099511627776)), (1759240125/8796093022208), by norm_num⟩
  | 14 => ⟨((3963/549755813888), (183/137438953472)), (1759223501/8796093022208), by norm_num⟩
  | 15 => ⟨((-2829/4398046511104), (-699/2199023255552)), (1759219649/8796093022208), by norm_num⟩
  | 16 => ⟨((27/549755813888), (397/8796093022208)), (879609407/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile018Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27177/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27177/1280))
  have he : value ((69/80), (27177/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1631076961/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((629202324333777/1125899906842624), (276393564502219/1125899906842624)), (29656813/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1373799715/4294967296), (-150869357/1073741824)), (35/4294967296), by norm_num⟩
  | 2 => ⟨((196578699/2147483648), (86352331/2147483648)), (11/4294967296), by norm_num⟩
  | 3 => ⟨((-300039349/17179869184), (-263600251/34359738368)), (9/17179869184), by norm_num⟩
  | 4 => ⟨((1373856039/549755813888), (603502171/549755813888)), (11/137438953472), by norm_num⟩
  | 5 => ⟨((-629077627/2199023255552), (-552677577/4398046511104)), (43/4398046511104), by norm_num⟩
  | 6 => ⟨((30005165/1099511627776), (421777693/35184372088832)), (35/35184372088832), by norm_num⟩
  | 7 => ⟨((-39254639/17592186044416), (-551796035/562949953421312)), (3/35184372088832), by norm_num⟩
  | 8 => ⟨((718975335/4503599627370496), (157914353/2251799813685248)), (29/4503599627370496), by norm_num⟩
  | 9 => ⟨((-182896123/18014398509481984), (-642735215/144115188075855872)), (31/72057594037927936), by norm_num⟩
  | 10 => ⟨((334986653/576460752303423488), (73575821/288230376151711744)), (15/576460752303423488), by norm_num⟩
  | 11 => ⟨((-278886715/9223372036854775808), (-61254139/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | 12 => ⟨((212833305/147573952589676412928), (186985183/295147905179352825856)), (21/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-1199441945/18889465931478580854784), (-526886221/18889465931478580854784)), (61/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((784592595/302231454903657293676544), (172326401/151115727451828646838272)), (21/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-958023031/9671406556917033397649408), (-210418327/4835703278458516698824704)), (27/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((1096677595/309485009821345068724781056), (481744295/309485009821345068724781056)), (1/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (539151296481/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((445302301020591/158456325028528675187087900672), (639722320827/633825300114114700748351602688)), (23067/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892487064389279/39614081257132168796771975168), (179913852133/9903520314283042199192993792)), (25951/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892433385636391/2475880078570760549798248448), (764595325319/2475880078570760549798248448)), (13787/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774099266217547/154742504910672534362390528), (764551963109/154742504910672534362390528)), (27575/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776139913044755/4835703278458516698824704), (89590174467/1208925819614629174706176)), (25853/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261173892363931/604462909807314587353088), (19596411081/18889465931478580854784)), (22623/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891667274515141/75557863725914323419136), (1018927007571/75557863725914323419136)), (9191/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300445232379907/4722366482869645213696), (764119689497/4722366482869645213696)), (3447/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625442515572415/590295810358705651712), (1050541789973/590295810358705651712)), (1185/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1828466051259185/73786976294838206464), (164124135471/9223372036854775808)), (23703/36893488147419103232), by norm_num⟩
  | 7 => ⟨((914135043017813/4611686018427387904), (184608005239/1152921504606846976)), (53339/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399878968930739/288230376151711744), (1476547621259/1152921504606846976)), (13337/288230376151711744), by norm_num⟩
  | 5 => ⟨((599708235696407/72057594037927936), (1291623265495/144115188075855872)), (46691/144115188075855872), by norm_num⟩
  | 4 => ⟨((374721214794875/9007199254740992), (484180816833/9007199254740992)), (70057/36028797018963968), by norm_num⟩
  | 3 => ⟨((374576581984329/2251799813685248), (2419659124447/9007199254740992)), (87609/9007199254740992), by norm_num⟩
  | 2 => ⟨((2246013387614033/4503599627370496), (151112029593/140737488355328)), (87665/2251799813685248), by norm_num⟩
  | 1 => ⟨((560780462955509/562949953421312), (3622024842407/1125899906842624)), (131639/1125899906842624), by norm_num⟩
  | 0 => ⟨((2234450617851963/2251799813685248), (14450821532403/2251799813685248)), (527689/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((2234450617851963/2251799813685248), (14450821532403/2251799813685248)), (2012973793990325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2217142352989779/2251799813685248), (14339483867663/1125899906842624)), (1054021/2251799813685248), by norm_num⟩
  | 2 => ⟨((2182653049512013/2251799813685248), (56475139237139/2251799813685248)), (1051223/1125899906842624), by norm_num⟩
  | 3 => ⟨((2114213201483855/2251799813685248), (109481876788881/2251799813685248)), (4181231/2251799813685248), by norm_num⟩
  | 4 => ⟨((1979710253500587/2251799813685248), (205584908412853/2251799813685248)), (8258091/2251799813685248), by norm_num⟩
  | 5 => ⟨((1721728330238753/2251799813685248), (180743664990281/1125899906842624)), (8014197/1125899906842624), by norm_num⟩
  | 6 => ⟨((629202324333777/1125899906842624), (276393564502219/1125899906842624)), (29656813/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1631076961/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-738005423/1125899906842624), (-499196753/1125899906842624)), (893/562949953421312), by norm_num⟩
  | 1 => ⟨((-160755899/2251799813685248), (-852103521/1125899906842624)), (5007/1125899906842624), by norm_num⟩
  | 2 => ⟨((569669405/2251799813685248), (-140907509/562949953421312)), (14123/2251799813685248), by norm_num⟩
  | 3 => ⟨((966560371/9007199254740992), (25975019/2251799813685248)), (53295/9007199254740992), by norm_num⟩
  | 4 => ⟨((232719315/18014398509481984), (718488585/36028797018963968)), (151527/36028797018963968), by norm_num⟩
  | 5 => ⟨((-359538955/288230376151711744), (552290517/144115188075855872)), (695039/288230376151711744), by norm_num⟩
  | 6 => ⟨((-586204945/1152921504606846976), (112983535/576460752303423488)), (2706605/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-960609623/18446744073709551616), (-68012371/2305843009213693952)), (9460297/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-145353031/147573952589676412928), (-1560047131/295147905179352825856)), (65093827/295147905179352825856), by norm_num⟩
  | 9 => ⟨((568478881/2361183241434822606848), (-45867073/147573952589676412928)), (32297199/295147905179352825856), by norm_num⟩
  | 10 => ⟨((107470327/4722366482869645213696), (-59262245/18889465931478580854784)), (1364161001/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((18109287/18889465931478580854784), (8712681/18889465931478580854784)), (576614657/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((384877/9444732965739290427392), (35237/1180591620717411303424)), (1095755465/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((43663/18889465931478580854784), (53291/18889465931478580854784)), (270348073/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((251/18889465931478580854784), (2233/9444732965739290427392)), (1078073253/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-129/18889465931478580854784), (39/4722366482869645213696)), (1077359311/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-5/18889465931478580854784), (1/9444732965739290427392)), (269303887/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((40661477/8796093022208), (-155058031/35184372088832)), (34855/140737488355328), by norm_num⟩
  | 1 => ⟨((560609141/70368744177664), (-791540079/70368744177664)), (8791/17592186044416), by norm_num⟩
  | 2 => ⟨((189148941/17592186044416), (529426073/140737488355328)), (101865/140737488355328), by norm_num⟩
  | 3 => ⟨((-92460679/140737488355328), (975107943/281474976710656)), (236097/281474976710656), by norm_num⟩
  | 4 => ⟨((-525363869/1125899906842624), (10902395/1125899906842624)), (3857627/4503599627370496), by norm_num⟩
  | 5 => ⟨((-401902765/18014398509481984), (189892929/72057594037927936)), (57510989/72057594037927936), by norm_num⟩
  | 6 => ⟨((-181114567/18014398509481984), (-134633469/36028797018963968)), (102402293/144115188075855872), by norm_num⟩
  | 7 => ⟨((278983423/1152921504606846976), (-1704002603/1152921504606846976)), (728346061/1152921504606846976), by norm_num⟩
  | 8 => ⟨((197390377/2305843009213693952), (-3142491/576460752303423488)), (1331369303/2305843009213693952), by norm_num⟩
  | 9 => ⟨((4587885/2305843009213693952), (-3547427/2305843009213693952)), (1259753385/2305843009213693952), by norm_num⟩
  | 10 => ⟨((1272827/2305843009213693952), (250993/2305843009213693952)), (1224485251/2305843009213693952), by norm_num⟩
  | 11 => ⟨((5767/2305843009213693952), (16227/576460752303423488)), (302286257/576460752303423488), by norm_num⟩
  | 12 => ⟨((649/1152921504606846976), (1301/2305843009213693952)), (75197025/144115188075855872), by norm_num⟩
  | 13 => ⟨((-3/288230376151711744), (5/36028797018963968)), (1201022409/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-1/144115188075855872), (17/2305843009213693952)), (1200326631/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-1/576460752303423488), (1/1152921504606846976)), (150014501/288230376151711744), by norm_num⟩
  | 16 => ⟨((-1/2305843009213693952), 0), (75003533/144115188075855872), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((5204669069/1125899906842624), (-4961857057/1125899906842624)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((8969746343/1125899906842624), (-12664641547/1125899906842624)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((1513191549/140737488355328), (1058852125/281474976710656)), (1/536870912), by norm_num⟩
  | 3 => ⟨((-739685331/1125899906842624), (1950215945/562949953421312)), (1/536870912), by norm_num⟩
  | 4 => ⟨((-65670493/140737488355328), (2725607/281474976710656)), (1/268435456), by norm_num⟩
  | 5 => ⟨((-6279729/281474976710656), (2967073/1125899906842624)), (1/268435456), by norm_num⟩
  | 6 => ⟨((-5659835/562949953421312), (-4207297/1125899906842624)), (1/268435456), by norm_num⟩
  | 7 => ⟨((272453/1125899906842624), (-832035/562949953421312)), (1/268435456), by norm_num⟩
  | 8 => ⟨((48191/562949953421312), (-3067/562949953421312)), (1/268435456), by norm_num⟩
  | 9 => ⟨((2239/1125899906842624), (-1733/1125899906842624)), (1/268435456), by norm_num⟩
  | 10 => ⟨((311/562949953421312), (61/562949953421312)), (1/268435456), by norm_num⟩
  | 11 => ⟨((3/1125899906842624), (1/35184372088832)), (1/268435456), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨18,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨18,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(3423/134217728)) (L:=(7540173279334735/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile018
