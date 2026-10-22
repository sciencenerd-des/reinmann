/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile010Gamma
import XiBand97.Tile010Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile010
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((768671727/281474976710656), (1348538947/281474976710656)), (1361/281474976710656), by norm_num⟩
  | 1 => ⟨((-60875355/140737488355328), (1048567227/140737488355328)), (727/70368744177664), by norm_num⟩
  | 2 => ⟨((-823779183/281474976710656), (568475653/140737488355328)), (197/17592186044416), by norm_num⟩
  | 3 => ⟨((-1146062973/562949953421312), (461600107/562949953421312)), (2309/281474976710656), by norm_num⟩
  | 4 => ⟨((-396837307/562949953421312), (-270208125/2251799813685248)), (10297/2251799813685248), by norm_num⟩
  | 5 => ⟨((-628835795/4503599627370496), (-539736505/4503599627370496)), (9355/4503599627370496), by norm_num⟩
  | 6 => ⟨((-229589895/18014398509481984), (-663333679/18014398509481984)), (29231/36028797018963968), by norm_num⟩
  | 7 => ⟨((45306435/36028797018963968), (-495284481/72057594037927936)), (42269/144115188075855872), by norm_num⟩
  | 8 => ⟨((196298813/288230376151711744), (-972601389/1152921504606846976)), (130969/1152921504606846976), by norm_num⟩
  | 9 => ⟨((312982321/2305843009213693952), (-68212111/1152921504606846976)), (546005/9223372036854775808), by norm_num⟩
  | 10 => ⟨((1330522379/73786976294838206464), (66966675/73786976294838206464)), (1643525/36893488147419103232), by norm_num⟩
  | 11 => ⟨((1035780705/590295810358705651712), (34638569/36893488147419103232)), (24194915/590295810358705651712), by norm_num⟩
  | 12 => ⟨((289931501/2361183241434822606848), (748289681/4722366482869645213696)), (189831083/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((2822751/590295810358705651712), (680329265/37778931862957161709568)), (1512556817/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-7321903/37778931862957161709568), (60425707/37778931862957161709568)), (377850509/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-571971/9444732965739290427392), (1091891/9444732965739290427392)), (94449847/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((-277089/37778931862957161709568), (254537/37778931862957161709568)), (1511163539/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile010Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((283536005/16777216), (400280191/16777216)), (3509/16777216), by norm_num⟩
  | 1 => ⟨((-255818397/16777216), (-253117289/67108864)), (14721/67108864), by norm_num⟩
  | 2 => ⟨((1117784339/134217728), (68400297/33554432)), (15085/67108864), by norm_num⟩
  | 3 => ⟨((-199782209/67108864), (-126652979/134217728)), (119547/536870912), by norm_num⟩
  | 4 => ⟨((108908555/134217728), (6142547/16777216)), (232109/1073741824), by norm_num⟩
  | 5 => ⟨((-46999973/268435456), (-30892411/268435456)), (449833/2147483648), by norm_num⟩
  | 6 => ⟨((16237347/536870912), (3944871/134217728)), (1758403/8589934592), by norm_num⟩
  | 7 => ⟨((-4413745/1073741824), (-6664635/1073741824)), (27767599/137438953472), by norm_num⟩
  | 8 => ⟨((432633/1073741824), (1184607/1073741824)), (110380475/549755813888), by norm_num⟩
  | 9 => ⟨((-71395/4294967296), (-718187/4294967296)), (1761577901/8796093022208), by norm_num⟩
  | 10 => ⟨((-31205/8589934592), (93423/4294967296)), (1759955885/8796093022208), by norm_num⟩
  | 11 => ⟨((39327/34359738368), (-166463/68719476736)), (1759428525/8796093022208), by norm_num⟩
  | 12 => ⟨((-55449/274877906944), (62337/274877906944)), (1759273773/8796093022208), by norm_num⟩
  | 13 => ⟨((3779/137438953472), (-18533/1099511627776)), (1759232045/8796093022208), by norm_num⟩
  | 14 => ⟨((-13761/4398046511104), (3495/4398046511104)), (1759221655/8796093022208), by norm_num⟩
  | 15 => ⟨((335/1099511627776), (161/8796093022208)), (219902407/1099511627776), by norm_num⟩
  | 16 => ⟨((-223/8796093022208), (-89/8796093022208)), (1759218735/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile010Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (24671/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (24671/1280))
  have he : value ((69/80), (24671/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1480674825/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((12474943834407/562949953421312), (42923736447195/70368744177664)), (52073/2199023255552), by norm_num⟩
  | 1 => ⟨((-54475559/4294967296), (-187439285/536870912)), (61/4294967296), by norm_num⟩
  | 2 => ⟨((7794975/2147483648), (1716538811/17179869184)), (9/2147483648), by norm_num⟩
  | 3 => ⟨((-47590085/68719476736), (-1309982185/68719476736)), (57/68719476736), by norm_num⟩
  | 4 => ⟨((54477793/549755813888), (749787879/274877906944)), (17/137438953472), by norm_num⟩
  | 5 => ⟨((-24944943/2199023255552), (-1373287349/4398046511104)), (65/4398046511104), by norm_num⟩
  | 6 => ⟨((38073629/35184372088832), (524014357/17592186044416)), (51/35184372088832), by norm_num⟩
  | 7 => ⟨((-24905155/281474976710656), (-1371096903/562949953421312)), (69/562949953421312), by norm_num⟩
  | 8 => ⟨((28509675/4503599627370496), (784767801/4503599627370496)), (41/4503599627370496), by norm_num⟩
  | 9 => ⟨((-58019337/144115188075855872), (-798530805/72057594037927936)), (43/72057594037927936), by norm_num⟩
  | 10 => ⟨((53133175/2305843009213693952), (365640831/576460752303423488)), (81/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-22117503/18446744073709551616), (-1217629053/36893488147419103232)), (69/36893488147419103232), by norm_num⟩
  | 12 => ⟨((33758089/590295810358705651712), (464618789/295147905179352825856)), (27/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-47561715/18889465931478580854784), (-81825079/1180591620717411303424)), (39/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((62223219/604462909807314587353088), (107048701/37778931862957161709568)), (13/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((-18994341/4835703278458516698824704), (-522845215/4835703278458516698824704)), (65/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((10871695/77371252455336267181195264), (1197033087/309485009821345068724781056)), (19/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (1998836075423/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781206426713123/633825300114114700748351602688), (148230661489/39614081257132168796771975168)), (23109/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892483770280169/39614081257132168796771975168), (2668028358493/39614081257132168796771975168)), (26001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892429680017513/2475880078570760549798248448), (2834636713293/2475880078570760549798248448)), (27631/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443523832323989/38685626227668133590597632), (1417237668517/77371252455336267181195264)), (6909/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776137944751863/4835703278458516698824704), (10379488819/37778931862957161709568)), (12957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261170202171581/604462909807314587353088), (1162416986283/302231454903657293676544)), (2835/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1891660817392231/75557863725914323419136), (3777533531847/75557863725914323419136)), (36863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325109996659175/1180591620717411303424), (2832868616387/4722366482869645213696)), (3457/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625434648128753/590295810358705651712), (3894736729557/590295810358705651712)), (38041/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828455235427497/73786976294838206464), (2433867130849/36893488147419103232)), (47571/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828256569101441/9223372036854775808), (5475256537721/9223372036854775808)), (26773/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799750336549431/576460752303423488), (5474075360887/1152921504606846976)), (26791/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199401273678281/144115188075855872), (1197121592563/36028797018963968)), (11731/36028797018963968), by norm_num⟩
  | 4 => ⟨((749429137114137/18014398509481984), (3590034274965/18014398509481984)), (35233/18014398509481984), by norm_num⟩
  | 3 => ⟨((374566618153903/2251799813685248), (4485212369327/4503599627370496)), (88223/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122956913353951/2251799813685248), (2240856237817/562949953421312)), (88433/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121461481162219/1125899906842624), (1678451093431/140737488355328)), (133175/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116927555885493/1125899906842624), (3348116002775/140737488355328)), (134229/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116927555885493/1125899906842624), (3348116002775/140737488355328)), (512043001415061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((69211843630023/70368744177664), (3321434703985/70368744177664)), (545411/1125899906842624), by norm_num⟩
  | 2 => ⟨((1086675040408845/1125899906842624), (104538512168593/1125899906842624)), (140547/140737488355328), by norm_num⟩
  | 3 => ⟨((259777608962151/281474976710656), (12612066050975/70368744177664)), (2379203/1125899906842624), by norm_num⟩
  | 4 => ⟨((922844076809863/1125899906842624), (186237932825577/562949953421312)), (163889/35184372088832), by norm_num⟩
  | 5 => ⟨((316592494269617/562949953421312), (610599830911685/1125899906842624)), (754201/70368744177664), by norm_num⟩
  | 6 => ⟨((12474943834407/562949953421312), (42923736447195/70368744177664)), (52073/2199023255552), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1480674825/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-50347005/17592186044416), (498760231/281474976710656)), (57/17592186044416), by norm_num⟩
  | 1 => ⟨((-205211137/70368744177664), (-156633167/140737488355328)), (1207/140737488355328), by norm_num⟩
  | 2 => ⟨((-440012505/1125899906842624), (-1518764645/1125899906842624)), (13091/1125899906842624), by norm_num⟩
  | 3 => ⟨((138218035/562949953421312), (-91376643/281474976710656)), (23889/2251799813685248), by norm_num⟩
  | 4 => ⟨((765554197/9007199254740992), (8757037/9007199254740992)), (129/17592186044416), by norm_num⟩
  | 5 => ⟨((70833875/9007199254740992), (198469593/18014398509481984)), (36981/9007199254740992), by norm_num⟩
  | 6 => ⟨((-77437473/144115188075855872), (925417029/576460752303423488)), (1122265/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1478062205/9223372036854775808), (464542235/9223372036854775808)), (469621/576460752303423488), by norm_num⟩
  | 8 => ⟨((-779623029/73786976294838206464), (-569093867/73786976294838206464)), (23586687/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-76470483/2361183241434822606848), (-448644387/590295810358705651712)), (313344913/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((327212493/18889465931478580854784), (-211196043/9444732965739290427392)), (663905319/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((7585157/37778931862957161709568), (-658563/590295810358705651712)), (1948474683/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((357635/4722366482869645213696), (-622373/4722366482869645213696)), (877817591/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((26257/2361183241434822606848), (-193/147573952589676412928)), (853679809/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((5005/18889465931478580854784), (15255/37778931862957161709568)), (1696178565/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-139/18889465931478580854784), (45/18889465931478580854784)), (846883519/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((39/37778931862957161709568), (-9/18889465931478580854784)), (1693279989/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-398649703/4398046511104), (-168597379/4398046511104)), (1211/1099511627776), by norm_num⟩
  | 1 => ⟨((242686971/8796093022208), (-920160395/8796093022208)), (19971/8796093022208), by norm_num⟩
  | 2 => ⟨((1351125519/35184372088832), (167875639/35184372088832)), (104145/35184372088832), by norm_num⟩
  | 3 => ⟨((264535167/281474976710656), (1302130245/281474976710656)), (28091/8796093022208), by norm_num⟩
  | 4 => ⟨((338016585/562949953421312), (554555869/1125899906842624)), (3480871/1125899906842624), by norm_num⟩
  | 5 => ⟨((-177986475/2251799813685248), (603891569/2251799813685248)), (12850657/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1315152349/36028797018963968), (-178102839/36028797018963968)), (47034609/18014398509481984), by norm_num⟩
  | 7 => ⟨((-54742661/288230376151711744), (-1151882649/576460752303423488)), (1401108465/576460752303423488), by norm_num⟩
  | 8 => ⟨((-36114285/576460752303423488), (-7453045/144115188075855872)), (1337747865/576460752303423488), by norm_num⟩
  | 9 => ⟨((185215/72057594037927936), (-9210549/576460752303423488)), (652300307/288230376151711744), by norm_num⟩
  | 10 => ⟨((423393/576460752303423488), (-3569/36028797018963968)), (1289310211/576460752303423488), by norm_num⟩
  | 11 => ⟨((1075/72057594037927936), (-14139/576460752303423488)), (1282981233/576460752303423488), by norm_num⟩
  | 12 => ⟨((549/144115188075855872), (25/576460752303423488)), (640300571/288230376151711744), by norm_num⟩
  | 13 => ⟨((35/576460752303423488), (33/576460752303423488)), (1279780317/576460752303423488), by norm_num⟩
  | 14 => ⟨((5/288230376151711744), (-1/576460752303423488)), (1279518719/576460752303423488), by norm_num⟩
  | 15 => ⟨(0, (1/576460752303423488)), (639720607/288230376151711744), by norm_num⟩
  | 16 => ⟨(0, 0), (159927469/72057594037927936), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-12756790137/140737488355328), (-21580462935/562949953421312)), (1/536870912), by norm_num⟩
  | 1 => ⟨((31063927237/1125899906842624), (-58890263401/562949953421312)), (1/268435456), by norm_num⟩
  | 2 => ⟨((5404502119/140737488355328), (2686008707/562949953421312)), (1/134217728), by norm_num⟩
  | 3 => ⟨((1058140067/1125899906842624), (1302130665/281474976710656)), (1/134217728), by norm_num⟩
  | 4 => ⟨((84504155/140737488355328), (277277261/562949953421312)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-88993033/1125899906842624), (150973239/562949953421312)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-41098677/1125899906842624), (-5565941/1125899906842624)), (1/134217728), by norm_num⟩
  | 7 => ⟨((-213759/1125899906842624), (-2249689/1125899906842624)), (1/134217728), by norm_num⟩
  | 8 => ⟨((-70571/1125899906842624), (-58243/1125899906842624)), (1/134217728), by norm_num⟩
  | 9 => ⟨((363/140737488355328), (-4497/281474976710656)), (1/134217728), by norm_num⟩
  | 10 => ⟨((825/1125899906842624), (-7/70368744177664)), (1/134217728), by norm_num⟩
  | 11 => ⟨((9/562949953421312), (-7/281474976710656)), (1/134217728), by norm_num⟩
  | 12 => ⟨((1/281474976710656), 0), (1/134217728), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨10,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨10,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(160979/1073741824)) (L:=(116188419234522335/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile010
