/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile002Gamma
import XiBand97.Tile002Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile002
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-515472611/4398046511104), (515841865/8796093022208)), (515/4398046511104), by norm_num⟩
  | 1 => ⟨((-1413239387/8796093022208), (-112616369/4398046511104)), (2263/8796093022208), by norm_num⟩
  | 2 => ⟨((-312539859/4398046511104), (-606635377/8796093022208)), (2485/8796093022208), by norm_num⟩
  | 3 => ⟨((-275188699/35184372088832), (-678782783/17592186044416)), (7329/35184372088832), by norm_num⟩
  | 4 => ⟨((152007135/35184372088832), (-1498943385/140737488355328)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((75319835/35184372088832), (-858183389/562949953421312)), (7411/140737488355328), by norm_num⟩
  | 6 => ⟨((1101747651/2251799813685248), (-83135521/2251799813685248)), (45285/2251799813685248), by norm_num⟩
  | 7 => ⟨((628416249/9007199254740992), (591975489/18014398509481984)), (120425/18014398509481984), by norm_num⟩
  | 8 => ⟨((454914385/72057594037927936), (601225279/72057594037927936)), (286597/144115188075855872), by norm_num⟩
  | 9 => ⟨((71963201/288230376151711744), (1415802603/1152921504606846976)), (638501/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-261152595/9223372036854775808), (609807835/4611686018427387904)), (1505707/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-137390341/18446744073709551616), (102445899/9223372036854775808)), (1238773/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-1173040301/1180591620717411303424), (212111939/295147905179352825856)), (26881297/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-949143129/9444732965739290427392), (143292811/4722366482869645213696)), (96933907/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-159221315/18889465931478580854784), (-6644649/37778931862957161709568)), (1518250167/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-22929135/37778931862957161709568), (-3760949/18889465931478580854784)), (378087259/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((-1434445/37778931862957161709568), (-975129/37778931862957161709568)), (1511346847/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile002Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-519599025/67108864), (357591081/67108864)), (6931/33554432), by norm_num⟩
  | 1 => ⟨((371128441/67108864), (1204665157/134217728)), (14443/67108864), by norm_num⟩
  | 2 => ⟨((-68985183/67108864), (-566725601/134217728)), (29481/134217728), by norm_num⟩
  | 3 => ⟨((-2742347/134217728), (22154363/16777216)), (234165/1073741824), by norm_num⟩
  | 4 => ⟨((12289385/134217728), (-10177619/33554432)), (457449/2147483648), by norm_num⟩
  | 5 => ⟨((-9544339/268435456), (14210217/268435456)), (1783939/8589934592), by norm_num⟩
  | 6 => ⟨((590411/67108864), (-3691793/536870912)), (1751123/8589934592), by norm_num⟩
  | 7 => ⟨((-883967/536870912), (610595/1073741824)), (110874299/549755813888), by norm_num⟩
  | 8 => ⟨((528575/2147483648), (2897/1073741824)), (882456023/4398046511104), by norm_num⟩
  | 9 => ⟨((-63987/2147483648), (-48917/4294967296)), (1761192877/8796093022208), by norm_num⟩
  | 10 => ⟨((49085/17179869184), (43763/17179869184)), (1759836589/8796093022208), by norm_num⟩
  | 11 => ⟨((-13399/68719476736), (-26233/68719476736)), (1759395373/8796093022208), by norm_num⟩
  | 12 => ⟨((1191/274877906944), (12337/274877906944)), (1759265485/8796093022208), by norm_num⟩
  | 13 => ⟨((1375/1099511627776), (-4729/1099511627776)), (1759230109/8796093022208), by norm_num⟩
  | 14 => ⟨((-569/2199023255552), (1463/4398046511104)), (1759221227/8796093022208), by norm_num⟩
  | 15 => ⟨((141/4398046511104), (-85/4398046511104)), (879609583/4398046511104), by norm_num⟩
  | 16 => ⟨((-27/8796093022208), (5/8796093022208)), (879609359/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile002Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9561/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9561/640))
  have he : value ((69/80), (9561/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-573820761/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-881890517161865/2251799813685248), (-1054241426581761/2251799813685248)), (60816345/2251799813685248), by norm_num⟩
  | 1 => ⟨((962759429/4294967296), (575457415/2147483648)), (69/4294967296), by norm_num⟩
  | 2 => ⟨((-275524873/4294967296), (-658743301/8589934592)), (41/8589934592), by norm_num⟩
  | 3 => ⟨((841070817/68719476736), (31420131/2147483648)), (65/68719476736), by norm_num⟩
  | 4 => ⟨((-962798901/549755813888), (-1150962015/549755813888)), (77/549755813888), by norm_num⟩
  | 5 => ⟨((881715741/4398046511104), (1054032493/4398046511104)), (73/4398046511104), by norm_num⟩
  | 6 => ⟨((-42055265/2199023255552), (-804388331/35184372088832)), (29/17592186044416), by norm_num⟩
  | 7 => ⟨((880309371/562949953421312), (131543909/70368744177664)), (79/562949953421312), by norm_num⟩
  | 8 => ⟨((-503858223/4503599627370496), (-37645561/281474976710656)), (47/4503599627370496), by norm_num⟩
  | 9 => ⟨((256347363/36028797018963968), (612892427/72057594037927936)), (25/36028797018963968), by norm_num⟩
  | 10 => ⟨((-939035161/2305843009213693952), (-1122554045/2305843009213693952)), (47/1152921504606846976), by norm_num⟩
  | 11 => ⟨((781775719/36893488147419103232), (934560847/36893488147419103232)), (81/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-596614687/590295810358705651712), (-713213155/590295810358705651712)), (1/9223372036854775808), by norm_num⟩
  | 13 => ⟨((840569431/18889465931478580854784), (1004844817/18889465931478580854784)), (23/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-137460707/75557863725914323419136), (-328650255/151115727451828646838272)), (31/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((83922869/1208925819614629174706176), (802593641/9671406556917033397649408)), (39/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-384276065/154742504910672534362390528), (-918752927/309485009821345068724781056)), (23/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-738388784267/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781202882044645/633825300114114700748351602688), (-1752249469959/316912650057057350374175801344)), (723/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1892479566112947/39614081257132168796771975168), (-3942370898947/39614081257132168796771975168)), (13017/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892424950670197/2475880078570760549798248448), (-4188556194929/2475880078570760549798248448)), (6917/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((887045152373707/77371252455336267181195264), (-2094158288565/77371252455336267181195264)), (27675/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552270865386253/9671406556917033397649408), (-1963146041249/4835703278458516698824704)), (25953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261165492519647/604462909807314587353088), (-26837896365/4722366482869645213696)), (22717/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945826288209081/37778931862957161709568), (-5581804349841/75557863725914323419136)), (577/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((650216645852617/2361183241434822606848), (-261620916021/295147905179352825856)), (27709/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625424607237389/590295810358705651712), (-5754979404625/590295810358705651712)), (4765/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828441431650535/73786976294838206464), (-3596351118349/36893488147419103232)), (745/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1828239318056173/9223372036854775808), (-4045191641361/4611686018427387904)), (26841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199935158841515/144115188075855872), (-8088622681243/1152921504606846976)), (53735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599690938821337/72057594037927936), (-7075561168079/144115188075855872)), (23539/72057594037927936), by norm_num⟩
  | 4 => ⟨((93676521589417/2251799813685248), (-2652341724967/9007199254740992)), (35367/18014398509481984), by norm_num⟩
  | 3 => ⟨((187276950999713/1125899906842624), (-3313683946625/2251799813685248)), (5539/562949953421312), by norm_num⟩
  | 2 => ⟨((561446691352095/1125899906842624), (-13244242884305/2251799813685248)), (11117/281474976710656), by norm_num⟩
  | 1 => ⟨((280333642667687/281474976710656), (-19840014535713/1125899906842624)), (134183/1125899906842624), by norm_num⟩
  | 0 => ⟨((558273790762509/562949953421312), (-9893481617109/281474976710656)), (135745/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558273790762509/562949953421312), (-9893481617109/281474976710656)), (517826082469749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1105881969246203/1125899906842624), (-306603158763/4398046511104)), (557555/1125899906842624), by norm_num⟩
  | 2 => ⟨((1080748100483631/1125899906842624), (-38547444204361/281474976710656)), (1173023/1125899906842624), by norm_num⟩
  | 3 => ⟨((1016291024157535/1125899906842624), (-296012651562889/1125899906842624)), (1286625/562949953421312), by norm_num⟩
  | 4 => ⟨((839527519412079/1125899906842624), (-534390311238361/1125899906842624)), (5998555/1125899906842624), by norm_num⟩
  | 5 => ⟨((372354104087661/1125899906842624), (-796936512145035/1125899906842624)), (3659971/281474976710656), by norm_num⟩
  | 6 => ⟨((-881890517161865/2251799813685248), (-1054241426581761/2251799813685248)), (60816345/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-573820761/67108864)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1290525623/17592186044416), (140320891/4398046511104)), (1855/17592186044416), by norm_num⟩
  | 1 => ⟨((157407363/17592186044416), (294613357/4398046511104)), (1261/4398046511104), by norm_num⟩
  | 2 => ⟨((-759798679/35184372088832), (588030141/35184372088832)), (13851/35184372088832), by norm_num⟩
  | 3 => ⟨((-28144109/4398046511104), (-194402653/70368744177664)), (25479/70368744177664), by norm_num⟩
  | 4 => ⟨((-96946875/1125899906842624), (-700270105/562949953421312)), (141739/562949953421312), by norm_num⟩
  | 5 => ⟨((642615317/4503599627370496), (-355274577/4503599627370496)), (636175/4503599627370496), by norm_num⟩
  | 6 => ⟨((858885679/72057594037927936), (181073183/18014398509481984)), (4800101/72057594037927936), by norm_num⟩
  | 7 => ⟨((-289663469/576460752303423488), (524245353/576460752303423488)), (31333769/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-582192651/18446744073709551616), (-189079319/4611686018427387904)), (180966775/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1725499735/295147905179352825856), (159083815/295147905179352825856)), (472581439/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-158626347/1180591620717411303424), (377567761/590295810358705651712)), (577991927/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-230412655/4722366482869645213696), (-71103689/4722366482869645213696)), (1448775829/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((4804437/2361183241434822606848), (-13505011/4722366482869645213696)), (287426201/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((668615/4722366482869645213696), (1135949/4722366482869645213696)), (1415268967/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-419531/18889465931478580854784), (96291/18889465931478580854784)), (302039527/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((1021/9444732965739290427392), (-31829/18889465931478580854784)), (290732069/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((1045/9444732965739290427392), (905/18889465931478580854784)), (36052133/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1622859113/2199023255552), (316348039/2199023255552)), (25423/1099511627776), by norm_num⟩
  | 1 => ⟨((-674876871/2199023255552), (400094443/1099511627776)), (23979/549755813888), by norm_num⟩
  | 2 => ⟨((-911065651/2199023255552), (-37452345/274877906944)), (62931/1099511627776), by norm_num⟩
  | 3 => ⟨((27333851/1099511627776), (-547683267/4398046511104)), (544149/8796093022208), by norm_num⟩
  | 4 => ⟨((1211988021/70368744177664), (111054499/70368744177664)), (4269995/70368744177664), by norm_num⟩
  | 5 => ⟨((145945863/1125899906842624), (1002457343/1125899906842624)), (31967301/562949953421312), by norm_num⟩
  | 6 => ⟨((529062911/9007199254740992), (488850385/18014398509481984)), (118537719/2251799813685248), by norm_num⟩
  | 7 => ⟨((-37096359/36028797018963968), (97252731/9007199254740992)), (1785011151/36028797018963968), by norm_num⟩
  | 8 => ⟨((-3298999/9007199254740992), (1893025/18014398509481984)), (1718008705/36028797018963968), by norm_num⟩
  | 9 => ⟨((-389141/36028797018963968), (291935/9007199254740992)), (420957653/9007199254740992), by norm_num⟩
  | 10 => ⟨((-54299/18014398509481984), (-169/18014398509481984)), (417136747/9007199254740992), by norm_num⟩
  | 11 => ⟨((-1673/36028797018963968), (615/36028797018963968)), (1662433335/36028797018963968), by norm_num⟩
  | 12 => ⟨((-61/4503599627370496), (-91/36028797018963968)), (830107191/18014398509481984), by norm_num⟩
  | 13 => ⟨((-11/36028797018963968), (-5/36028797018963968)), (829738011/18014398509481984), by norm_num⟩
  | 14 => ⟨((-5/36028797018963968), (-5/36028797018963968)), (829624457/18014398509481984), by norm_num⟩
  | 15 => ⟨((1/36028797018963968), 0), (1659183893/36028797018963968), by norm_num⟩
  | 16 => ⟨(0, 0), (207395809/4503599627370496), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-207725964175/281474976710656), (161970216963/1125899906842624)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-345536927651/1125899906842624), (409696716811/1125899906842624)), (1/8388608), by norm_num⟩
  | 2 => ⟨((-116616409289/281474976710656), (-4793899599/35184372088832)), (1/4194304), by norm_num⟩
  | 3 => ⟨((13994937715/562949953421312), (-70103460761/562949953421312)), (1/4194304), by norm_num⟩
  | 4 => ⟨((19391797041/1125899906842624), (888437023/562949953421312)), (1/4194304), by norm_num⟩
  | 5 => ⟨((72976209/562949953421312), (501227251/562949953421312)), (1/4194304), by norm_num⟩
  | 6 => ⟨((33065587/562949953421312), (3819387/140737488355328)), (1/4194304), by norm_num⟩
  | 7 => ⟨((-579227/562949953421312), (3039057/281474976710656)), (1/4194304), by norm_num⟩
  | 8 => ⟨((-412683/1125899906842624), (118763/1125899906842624)), (1/4194304), by norm_num⟩
  | 9 => ⟨((-6099/562949953421312), (36391/1125899906842624)), (1/4194304), by norm_num⟩
  | 10 => ⟨((-3427/1125899906842624), (-11/1125899906842624)), (1/4194304), by norm_num⟩
  | 11 => ⟨((-47/1125899906842624), (-5/1125899906842624)), (1/4194304), by norm_num⟩
  | 12 => ⟨((-11/1125899906842624), (-1/562949953421312)), (1/4194304), by norm_num⟩
  | 13 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | 14 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | 15 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | 16 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨2,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨2,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(326799/1048576)) (K:=(1354079/1073741824)) (L:=(887664994455074037/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile002
