/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile001Gamma
import XiBand58.Tile001Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile001
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-574828437/4398046511104), (9075201/68719476736)), (265/2199023255552), by norm_num⟩
  | 1 => ⟨((-247635049/1099511627776), (41356935/1099511627776)), (1143/4398046511104), by norm_num⟩
  | 2 => ⟨((-1089063763/8796093022208), (-131360089/2199023255552)), (313/1099511627776), by norm_num⟩
  | 3 => ⟨((-117808265/4398046511104), (-824957557/17592186044416)), (29/137438953472), by norm_num⟩
  | 4 => ⟨((36798605/35184372088832), (-546383917/35184372088832)), (8353/70368744177664), by norm_num⟩
  | 5 => ⟨((584736981/281474976710656), (-796393873/281474976710656)), (7599/140737488355328), by norm_num⟩
  | 6 => ⟨((670892011/1125899906842624), (-561634303/2251799813685248)), (11639/562949953421312), by norm_num⟩
  | 7 => ⟨((1790902595/18014398509481984), (205553039/18014398509481984)), (61865/9007199254740992), by norm_num⟩
  | 8 => ⟨((802008601/72057594037927936), (536717909/72057594037927936)), (18343/9007199254740992), by norm_num⟩
  | 9 => ⟨((472577479/576460752303423488), (195573877/144115188075855872)), (162637/288230376151711744), by norm_num⟩
  | 10 => ⟨((222009421/9223372036854775808), (774154665/4611686018427387904)), (95275/576460752303423488), by norm_num⟩
  | 11 => ⟨((-277176631/73786976294838206464), (1198015085/73786976294838206464)), (2491373/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-486268917/590295810358705651712), (94289855/73786976294838206464)), (26923373/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-956416923/9444732965739290427392), (5958397/73786976294838206464)), (387870731/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-365116075/37778931862957161709568), (140390921/37778931862957161709568)), (94897601/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((-29436551/37778931862957161709568), (1165339/18889465931478580854784)), (756185815/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-2077075/37778931862957161709568), (-407461/37778931862957161709568)), (755675599/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile001Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-136734619/33554432), (150971687/33554432)), (27543/134217728), by norm_num⟩
  | 1 => ⟨((41001065/16777216), (1158944013/134217728)), (28455/134217728), by norm_num⟩
  | 2 => ⟨((37735795/134217728), (-498575029/134217728)), (115703/536870912), by norm_num⟩
  | 3 => ⟨((-25121417/67108864), (70438553/67108864)), (230165/1073741824), by norm_num⟩
  | 4 => ⟨((20896699/134217728), (-28498935/134217728)), (451753/2147483648), by norm_num⟩
  | 5 => ⟨((-11346653/268435456), (8239879/268435456)), (1770787/8589934592), by norm_num⟩
  | 6 => ⟨((4628057/536870912), (-1437773/536870912)), (27912495/137438953472), by norm_num⟩
  | 7 => ⟨((-1492503/1073741824), (-29769/536870912)), (110695099/549755813888), by norm_num⟩
  | 8 => ⟨((385625/2147483648), (79911/1073741824)), (881917399/4398046511104), by norm_num⟩
  | 9 => ⟨((-155811/8589934592), (-73455/4294967296)), (1760818093/8796093022208), by norm_num⟩
  | 10 => ⟨((10913/8589934592), (22989/8589934592)), (1759723437/8796093022208), by norm_num⟩
  | 11 => ⟨((-727/34359738368), (-22539/68719476736)), (1759363757/8796093022208), by norm_num⟩
  | 12 => ⟨((-2967/274877906944), (4467/137438953472)), (1759257101/8796093022208), by norm_num⟩
  | 13 => ⟨((151/68719476736), (-2809/1099511627776)), (1759228061/8796093022208), by norm_num⟩
  | 14 => ⟨((-155/549755813888), (311/2199023255552)), (1759220769/8796093022208), by norm_num⟩
  | 15 => ⟨((123/4398046511104), (-1/549755813888)), (1759219069/8796093022208), by norm_num⟩
  | 16 => ⟨((-5/2199023255552), (-7/8796093022208)), (1759218699/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile001Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (4659/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4659/320))
  have he : value ((15/16), (4659/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-1118473351/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-75900713242969/281474976710656), (-1168345661119137/2251799813685248)), (57211241/2251799813685248), by norm_num⟩
  | 1 => ⟨((662886161/4294967296), (318870591/1073741824)), (65/4294967296), by norm_num⟩
  | 2 => ⟨((-5928325/134217728), (-730041391/8589934592)), (39/8589934592), by norm_num⟩
  | 3 => ⟨((144775057/17179869184), (1114266931/68719476736)), (31/34359738368), by norm_num⟩
  | 4 => ⟨((-331456669/274877906944), (-1275534657/549755813888)), (73/549755813888), by norm_num⟩
  | 5 => ⟨((75885671/549755813888), (584057057/2199023255552)), (69/4398046511104), by norm_num⟩
  | 6 => ⟨((-57912397/4398046511104), (-891450091/35184372088832)), (55/35184372088832), by norm_num⟩
  | 7 => ⟨((606117043/562949953421312), (1166250927/562949953421312)), (37/281474976710656), by norm_num⟩
  | 8 => ⟨((-346920147/4503599627370496), (-1335042291/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 9 => ⟨((706008641/144115188075855872), (1358455831/144115188075855872)), (91/144115188075855872), by norm_num⟩
  | 10 => ⟨((-646551353/2305843009213693952), (-1244051991/2305843009213693952)), (85/2305843009213693952), by norm_num⟩
  | 11 => ⟨((134568483/9223372036854775808), (64731977/2305843009213693952)), (73/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-410785505/590295810358705651712), (-395203353/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 13 => ⟨((9043047/295147905179352825856), (1113602681/18889465931478580854784)), (21/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-378581803/302231454903657293676544), (-91055305/37778931862957161709568)), (57/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((231132749/4835703278458516698824704), (444730577/4835703278458516698824704)), (9/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((-529169131/309485009821345068724781056), (-509096383/154742504910672534362390528)), (85/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (-2670471822093/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781137729612083/633825300114114700748351602688), (-1584193275059/316912650057057350374175801344)), (23129/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473101586661031/9903520314283042199192993792), (-3564251443887/39614081257132168796771975168)), (26025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118271702974861/154742504910672534362390528), (-473351049771/309485009821345068724781056)), (27657/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887006352932977/77371252455336267181195264), (-473321682009/19342813113834066795298816)), (27663/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552198227127351/9671406556917033397649408), (-3549662910675/9671406556917033397649408)), (25941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261102044723847/604462909807314587353088), (-776426313569/151115727451828646838272)), (22705/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891549681251417/75557863725914323419136), (-2523151244923/37778931862957161709568)), (36909/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300356301868927/4722366482869645213696), (-1892158350183/2361183241434822606848)), (27693/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625319041165985/590295810358705651712), (-2601384295375/295147905179352825856)), (2381/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1828309916409215/73786976294838206464), (-6502459816425/73786976294838206464)), (1489/2305843009213693952), by norm_num⟩
  | 7 => ⟨((228511496437997/1152921504606846976), (-7313890029211/9223372036854775808)), (26821/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599334684096041/1152921504606846976), (-7312166955271/1152921504606846976)), (26845/576460752303423488), by norm_num⟩
  | 5 => ⟨((74953404310215/9007199254740992), (-3198102787915/72057594037927936)), (5879/18014398509481984), by norm_num⟩
  | 4 => ⟨((374658735242009/9007199254740992), (-4795211109821/18014398509481984)), (35327/18014398509481984), by norm_num⟩
  | 3 => ⟨((5851491565679/35184372088832), (-1497651938579/1125899906842624)), (88505/9007199254740992), by norm_num⟩
  | 2 => ⟨((8770813241683/17592186044416), (-5985487060333/1125899906842624)), (88787/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121001826354123/1125899906842624), (-17930777422151/1125899906842624)), (33471/281474976710656), by norm_num⟩
  | 0 => ⟨((1115926774363683/1125899906842624), (-17879169729485/562949953421312)), (135295/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1115926774363683/1125899906842624), (-17879169729485/562949953421312)), (516109468700218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1104906305916195/1125899906842624), (-8860398727839/140737488355328)), (553575/1125899906842624), by norm_num⟩
  | 2 => ⟨((1079841565724431/1125899906842624), (-69561497378751/562949953421312)), (578105/562949953421312), by norm_num⟩
  | 3 => ⟨((31827390706171/35184372088832), (-66715873930795/281474976710656)), (2503561/1125899906842624), by norm_num⟩
  | 4 => ⟨((858049863155925/1125899906842624), (-120700871428827/281474976710656)), (1429047/281474976710656), by norm_num⟩
  | 5 => ⟨((223443646626653/562949953421312), (-45993149827475/70368744177664)), (3403753/281474976710656), by norm_num⟩
  | 6 => ⟨((-75900713242969/281474976710656), (-1168345661119137/2251799813685248)), (57211241/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-1118473351/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((912718165/8796093022208), (35407835/1099511627776)), (7/68719476736), by norm_num⟩
  | 1 => ⟨((366923305/17592186044416), (1553074007/17592186044416)), (2375/8796093022208), by norm_num⟩
  | 2 => ⟨((-933862843/35184372088832), (863544101/35184372088832)), (12919/35184372088832), by norm_num⟩
  | 3 => ⟨((-150853721/17592186044416), (-13069697/4398046511104)), (5937/17592186044416), by norm_num⟩
  | 4 => ⟨((-224617945/1125899906842624), (-1776019443/1125899906842624)), (66165/281474976710656), by norm_num⟩
  | 5 => ⟨((782185569/4503599627370496), (-116598369/1125899906842624)), (595799/4503599627370496), by norm_num⟩
  | 6 => ⟨((254166201/18014398509481984), (871749329/72057594037927936)), (2254721/36028797018963968), by norm_num⟩
  | 7 => ⟨((-780970647/1152921504606846976), (1109589621/1152921504606846976)), (7373125/288230376151711744), by norm_num⟩
  | 8 => ⟨((-210995073/9223372036854775808), (-1191139561/18446744073709551616)), (170374501/18446744073709551616), by norm_num⟩
  | 9 => ⟨((628165625/73786976294838206464), (271960551/147573952589676412928)), (55536059/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-321027493/1180591620717411303424), (1002228275/1180591620717411303424)), (1083428809/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-142240125/2361183241434822606848), (-72285991/2361183241434822606848)), (337690455/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((34986719/9444732965739290427392), (-61226597/18889465931478580854784)), (1063946661/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((2451315/18889465931478580854784), (1841653/4722366482869645213696)), (325451517/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-627633/18889465931478580854784), (12057/18889465931478580854784)), (1108732871/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((13627/18889465931478580854784), (-89163/37778931862957161709568)), (2133260697/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((5421/37778931862957161709568), (4145/37778931862957161709568)), (2116029933/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1248455161/2199023255552), (738075275/2199023255552)), (63279/2199023255552), by norm_num⟩
  | 1 => ⟨((-278553411/549755813888), (389653221/549755813888)), (60107/1099511627776), by norm_num⟩
  | 2 => ⟨((-621001619/1099511627776), (-439770573/2199023255552)), (152769/2199023255552), by norm_num⟩
  | 3 => ⟨((287464139/8796093022208), (-1332393713/8796093022208)), (162843/2199023255552), by norm_num⟩
  | 4 => ⟨((1326154107/70368744177664), (108741249/70368744177664)), (1292383/17592186044416), by norm_num⟩
  | 5 => ⟨((263544047/1125899906842624), (830293117/1125899906842624)), (79463549/1125899906842624), by norm_num⟩
  | 6 => ⟨((24874051/281474976710656), (160222609/4503599627370496)), (606719825/9007199254740992), by norm_num⟩
  | 7 => ⟨((-14358411/18014398509481984), (212878457/18014398509481984)), (1168768665/18014398509481984), by norm_num⟩
  | 8 => ⟨((-4400837/18014398509481984), (773161/4503599627370496)), (8915987/140737488355328), by norm_num⟩
  | 9 => ⟨((-228969/18014398509481984), (791555/18014398509481984)), (1126894111/18014398509481984), by norm_num⟩
  | 10 => ⟨((-13489/4503599627370496), (4185/18014398509481984)), (140045101/2251799813685248), by norm_num⟩
  | 11 => ⟨((-539/9007199254740992), (831/18014398509481984)), (1117711809/18014398509481984), by norm_num⟩
  | 12 => ⟨((-195/18014398509481984), (-7/4503599627370496)), (1116741537/18014398509481984), by norm_num⟩
  | 13 => ⟨((1/18014398509481984), (-3/9007199254740992)), (558208449/9007199254740992), by norm_num⟩
  | 14 => ⟨((1/18014398509481984), (-1/18014398509481984)), (1116316833/18014398509481984), by norm_num⟩
  | 15 => ⟨(0, (-1/18014398509481984)), (1116288215/18014398509481984), by norm_num⟩
  | 16 => ⟨(0, 0), (558140287/9007199254740992), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-319604516905/562949953421312), (377894531521/1125899906842624)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-570477376789/1125899906842624), (199502447979/281474976710656)), (1/8388608), by norm_num⟩
  | 2 => ⟨((-635905653083/1125899906842624), (-225162534259/1125899906842624)), (1/4194304), by norm_num⟩
  | 3 => ⟨((36795411469/1125899906842624), (-170546388999/1125899906842624)), (1/4194304), by norm_num⟩
  | 4 => ⟨((21218460465/1125899906842624), (1739860449/1125899906842624)), (1/2097152), by norm_num⟩
  | 5 => ⟨((32943059/140737488355328), (415146033/562949953421312)), (1/2097152), by norm_num⟩
  | 6 => ⟨((49747815/562949953421312), (40054825/1125899906842624)), (1/2097152), by norm_num⟩
  | 7 => ⟨((-448467/562949953421312), (103941/8796093022208)), (1/2097152), by norm_num⟩
  | 8 => ⟨((-4297/17592186044416), (48353/281474976710656)), (1/2097152), by norm_num⟩
  | 9 => ⟨((-14369/1125899906842624), (49473/1125899906842624)), (1/2097152), by norm_num⟩
  | 10 => ⟨((-847/281474976710656), (15/70368744177664)), (1/2097152), by norm_num⟩
  | 11 => ⟨((-65/1125899906842624), (3/70368744177664)), (1/2097152), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨1,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨1,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(173423/1048576)) (K:=(796799/536870912)) (L:=(778628555653285137/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile001
