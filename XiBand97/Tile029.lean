/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile029Gamma
import XiBand97.Tile029Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile029
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((418341241/4503599627370496), (834842855/9007199254740992)), (2061/9007199254740992), by norm_num⟩
  | 1 => ⟨((422245849/9007199254740992), (834406363/4503599627370496)), (505/1125899906842624), by norm_num⟩
  | 2 => ⟨((-175142153/4503599627370496), (596490533/4503599627370496)), (553/1125899906842624), by norm_num⟩
  | 3 => ⟨((-862758927/18014398509481984), (816062333/18014398509481984)), (1705/4503599627370496), by norm_num⟩
  | 4 => ⟨((-820237489/36028797018963968), (6174165/1125899906842624)), (16791/72057594037927936), by norm_num⟩
  | 5 => ⟨((-914666713/144115188075855872), (-260857663/144115188075855872)), (2321/18014398509481984), by norm_num⟩
  | 6 => ⟨((-627373145/576460752303423488), (-625987391/576460752303423488)), (42843/576460752303423488), by norm_num⟩
  | 7 => ⟨((-99880295/1152921504606846976), (-168290817/576460752303423488)), (237201/4611686018427387904), by norm_num⟩
  | 8 => ⟨((192267691/18446744073709551616), (-946723613/18446744073709551616)), (399859/9223372036854775808), by norm_num⟩
  | 9 => ⟨((368347309/73786976294838206464), (-912443987/147573952589676412928)), (6032663/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1160094765/1180591620717411303424), (-261423647/590295810358705651712)), (47469951/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((1246722985/9444732965739290427392), (20739119/4722366482869645213696)), (378217077/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((247497837/18889465931478580854784), (256350627/37778931862957161709568)), (755749955/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((35130651/37778931862957161709568), (45174861/37778931862957161709568)), (94451313/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((1302735/37778931862957161709568), (5277909/37778931862957161709568)), (1511168353/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-78407/37778931862957161709568), (118599/9444732965739290427392)), (377789771/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((-21029/37778931862957161709568), (33811/37778931862957161709568)), (1511157555/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile029Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((217780003/33554432), (1147143789/67108864)), (7285/33554432), by norm_num⟩
  | 1 => ⟨((-245562609/16777216), (83060637/16777216)), (16071/67108864), by norm_num⟩
  | 2 => ⟨((1687703849/134217728), (-61638029/67108864)), (33745/134217728), by norm_num⟩
  | 3 => ⟨((-808954627/134217728), (-33199623/67108864)), (33233/134217728), by norm_num⟩
  | 4 => ⟨((138786263/67108864), (121329083/268435456)), (125783/536870912), by norm_num⟩
  | 5 => ⟨((-74286329/134217728), (-1678933/8388608)), (472993/2147483648), by norm_num⟩
  | 6 => ⟨((4057495/33554432), (4283561/67108864)), (1805107/8589934592), by norm_num⟩
  | 7 => ⟨((-11860489/536870912), (-4368199/268435456)), (1755867/8589934592), by norm_num⟩
  | 8 => ⟨((7311713/2147483648), (7466483/2147483648)), (27720687/137438953472), by norm_num⟩
  | 9 => ⟨((-3773141/8589934592), (-1373175/2147483648)), (110272059/549755813888), by norm_num⟩
  | 10 => ⟨((391963/8589934592), (1768499/17179869184)), (1760819629/8796093022208), by norm_num⟩
  | 11 => ⟨((-227043/68719476736), (-125971/8589934592)), (1759675181/8796093022208), by norm_num⟩
  | 12 => ⟨((4019/137438953472), (511535/274877906944)), (1759338861/8796093022208), by norm_num⟩
  | 13 => ⟨((733/17179869184), (-231883/1099511627776)), (1759247909/8796093022208), by norm_num⟩
  | 14 => ⟨((-10559/1099511627776), (93673/4398046511104)), (1759225247/8796093022208), by norm_num⟩
  | 15 => ⟨((6419/4398046511104), (-4175/2199023255552)), (879610009/4398046511104), by norm_num⟩
  | 16 => ⟨((-399/2199023255552), (641/4398046511104)), (219902361/1099511627776), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile029Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6223/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6223/256))
  have he : value ((69/80), (6223/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-233427897/16777216)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((305017305523339/2251799813685248), (-1340194132621285/2251799813685248)), (74997897/2251799813685248), by norm_num⟩
  | 1 => ⟨((-332987237/4294967296), (1463089253/4294967296)), (85/4294967296), by norm_num⟩
  | 2 => ⟨((190590221/8589934592), (-837420997/8589934592)), (25/4294967296), by norm_num⟩
  | 3 => ⟨((-36362387/8589934592), (1278161123/68719476736)), (79/68719476736), by norm_num⟩
  | 4 => ⟨((333000889/549755813888), (-1463149237/549755813888)), (93/549755813888), by norm_num⟩
  | 5 => ⟨((-38119607/549755813888), (83745533/274877906944)), (11/549755813888), by norm_num⟩
  | 6 => ⟨((116364409/17592186044416), (-1022570821/35184372088832)), (69/35184372088832), by norm_num⟩
  | 7 => ⟨((-152235219/281474976710656), (1337791291/562949953421312)), (23/140737488355328), by norm_num⟩
  | 8 => ⟨((174268205/4503599627370496), (-191426209/1125899906842624)), (27/2251799813685248), by norm_num⟩
  | 9 => ⟨((-354648929/144115188075855872), (48695845/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 10 => ⟨((324781783/2305843009213693952), (-1427035881/2305843009213693952)), (105/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-135195423/18446744073709551616), (1188051361/36893488147419103232)), (89/36893488147419103232), by norm_num⟩
  | 12 => ⟨((206349655/590295810358705651712), (-453332633/295147905179352825856)), (35/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-290725683/18889465931478580854784), (1277399171/18889465931478580854784)), (101/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((380345575/604462909807314587353088), (-1671173723/604462909807314587353088)), (67/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-58052393/2417851639229258349412352), (127536167/1208925819614629174706176)), (21/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((265817237/309485009821345068724781056), (-1167955695/309485009821345068724781056)), (49/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-1754639082905/10141204801825835211973625643008)), (7279/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781207113874817/633825300114114700748351602688), (-2081942107261/633825300114114700748351602688)), (8663/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892484585290851/39614081257132168796771975168), (-1171038660065/19807040628566084398385987584)), (9747/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946215298420321/1237940039285380274899124224), (-2488331367551/2475880078570760549798248448)), (41431/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774096303346553/154742504910672534362390528), (-2488189840411/154742504910672534362390528)), (41437/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552276863471081/9671406556917033397649408), (-1166263793051/4835703278458516698824704)), (38855/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630585557588757/302231454903657293676544), (-2040811229777/604462909807314587353088)), (34005/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891662414975651/75557863725914323419136), (-3316036193381/75557863725914323419136)), (27635/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300441284507289/4722366482869645213696), (-2486780307037/4722366482869645213696)), (5183/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625436594644163/590295810358705651712), (-854730433929/147573952589676412928)), (28515/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914228955707011/36893488147419103232), (-4273050259295/73786976294838206464)), (71315/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828259913376095/9223372036854775808), (-4806353702809/9223372036854775808)), (40133/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599504434433243/1152921504606846976), (-2402659293107/576460752303423488)), (80313/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199405033793785/144115188075855872), (-4203488820005/144115188075855872)), (70327/144115188075855872), by norm_num⟩
  | 4 => ⟨((749432425843113/18014398509481984), (-3151451126791/18014398509481984)), (26399/9007199254740992), by norm_num⟩
  | 3 => ⟨((749138166654961/4503599627370496), (-3937273079085/4503599627370496)), (132179/9007199254740992), by norm_num⟩
  | 2 => ⟨((17546394212503/35184372088832), (-7868418779095/2251799813685248)), (16557/281474976710656), by norm_num⟩
  | 1 => ⟨((560743042375795/562949953421312), (-1473411580571/140737488355328)), (12461/70368744177664), by norm_num⟩
  | 0 => ⟨((1117001221871593/1125899906842624), (-2939142633449/140737488355328)), (200763/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117001221871593/1125899906842624), (-2939142633449/140737488355328)), (765850069286155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1107681823473221/1125899906842624), (-11663651068323/281474976710656)), (813477/1125899906842624), by norm_num⟩
  | 2 => ⟨((1087825269821485/1125899906842624), (-22949845195291/281474976710656)), (834023/562949953421312), by norm_num⟩
  | 3 => ⟨((260888353442819/281474976710656), (-88694994609031/562949953421312)), (1747641/562949953421312), by norm_num⟩
  | 4 => ⟨((234820278581549/281474976710656), (-328831946236645/1125899906842624)), (3790339/562949953421312), by norm_num⟩
  | 5 => ⟨((687555401825151/1125899906842624), (-274327793270153/562949953421312)), (8538199/562949953421312), by norm_num⟩
  | 6 => ⟨((305017305523339/2251799813685248), (-1340194132621285/2251799813685248)), (74997897/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-233427897/16777216)), (3/134217728), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((305101307/4503599627370496), (-384881209/9007199254740992)), (781/4503599627370496), by norm_num⟩
  | 1 => ⟨((350578433/4503599627370496), (97517547/4503599627370496)), (3917/9007199254740992), by norm_num⟩
  | 2 => ⟨((161304457/9007199254740992), (40185619/1125899906842624)), (21085/36028797018963968), by norm_num⟩
  | 3 => ⟨((-334647825/72057594037927936), (216173019/18014398509481984)), (19779/36028797018963968), by norm_num⟩
  | 4 => ⟨((-815969407/288230376151711744), (314766923/288230376151711744)), (115991/288230376151711744), by norm_num⟩
  | 5 => ⟨((-1149158383/2305843009213693952), (-573802777/2305843009213693952)), (579381/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-421652171/18446744073709551616), (-732637683/9223372036854775808)), (2712241/18446744073709551616), by norm_num⟩
  | 7 => ⟨((771763485/147573952589676412928), (-1284681059/147573952589676412928)), (6713969/73786976294838206464), by norm_num⟩
  | 8 => ⟨((75583233/73786976294838206464), (-269188019/1180591620717411303424)), (38947819/590295810358705651712), by norm_num⟩
  | 9 => ⟨((91251427/1180591620717411303424), (472957359/9444732965739290427392)), (532497747/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((59482375/37778931862957161709568), (126965969/18889465931478580854784)), (1003728779/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-3933543/18889465931478580854784), (14821025/37778931862957161709568)), (1970399045/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-847583/37778931862957161709568), (405029/37778931862957161709568)), (1960237931/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((-47917/37778931862957161709568), (-3331/37778931862957161709568)), (244710805/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-2201/37778931862957161709568), (-1135/37778931862957161709568)), (978547431/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-83/37778931862957161709568), (-13/4722366482869645213696)), (978483675/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-1/18889465931478580854784), (-3/18889465931478580854784)), (1956941651/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((20584963/17592186044416), (247895381/281474976710656)), (7903/281474976710656), by norm_num⟩
  | 1 => ⟨((-363062395/562949953421312), (342275537/140737488355328)), (34741/562949953421312), by norm_num⟩
  | 2 => ⟨((-2089310283/2251799813685248), (3773529/562949953421312)), (12371/140737488355328), by norm_num⟩
  | 3 => ⟨((-944136045/9007199254740992), (-47046569/4503599627370496)), (902785/9007199254740992), by norm_num⟩
  | 4 => ⟨((-1253031581/18014398509481984), (-618766309/18014398509481984)), (225737/2251799813685248), by norm_num⟩
  | 5 => ⟨((20469579/4503599627370496), (-170245639/9007199254740992)), (416411/4503599627370496), by norm_num⟩
  | 6 => ⟨((617183843/288230376151711744), (42018483/576460752303423488)), (5925427/72057594037927936), by norm_num⟩
  | 7 => ⟨((1119320031/18446744073709551616), (170943507/4611686018427387904)), (676404857/9223372036854775808), by norm_num⟩
  | 8 => ⟨((377614291/18446744073709551616), (159375455/18446744073709551616)), (1239607865/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-7760715/18446744073709551616), (49241789/18446744073709551616)), (586819299/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-555601/4611686018427387904), (157979/9223372036854775808)), (1140091127/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-15473/4611686018427387904), (18961/4611686018427387904)), (1124901581/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-14343/18446744073709551616), (-1245/9223372036854775808)), (1118691773/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-19/4611686018427387904), (-33/1152921504606846976)), (558187657/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-3/2305843009213693952), (-3/18446744073709551616)), (1115580305/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-1/9223372036854775808), (-1/9223372036854775808)), (139415953/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-1/18446744073709551616), 0), (557626449/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1317437555/1125899906842624), (991581463/1125899906842624)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-726124701/1125899906842624), (1369102107/562949953421312)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-261163795/281474976710656), (3773521/562949953421312)), (1/4294967296), by norm_num⟩
  | 3 => ⟨((-59008471/562949953421312), (-5880823/562949953421312)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-78314507/1125899906842624), (-38672883/1125899906842624)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((5117409/1125899906842624), (-10640357/562949953421312)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((2410869/1125899906842624), (82071/1125899906842624)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((2135/35184372088832), (10433/281474976710656)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((2881/140737488355328), (19/2199023255552)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((-237/562949953421312), (3005/1125899906842624)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-17/140737488355328), (19/1125899906842624)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((-1/281474976710656), (5/1125899906842624)), (1/4294967296), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/4294967296), by norm_num⟩
  | 13 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 14 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 15 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 16 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨29,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨29,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(1913/536870912)) (L:=(1728998333347781/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile029
