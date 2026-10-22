/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile036Gamma
import XiBand97.Tile036Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile036
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1310726927/36028797018963968), (308538133/36028797018963968)), (4465/36028797018963968), by norm_num⟩
  | 1 => ⟨((-956720405/18014398509481984), (-293278903/18014398509481984)), (63/281474976710656), by norm_num⟩
  | 2 => ⟨((-62871041/2251799813685248), (-1080788207/36028797018963968)), (8759/36028797018963968), by norm_num⟩
  | 3 => ⟨((-330126097/72057594037927936), (-1403489145/72057594037927936)), (1721/9007199254740992), by norm_num⟩
  | 4 => ⟨((291445035/144115188075855872), (-251720897/36028797018963968)), (18031/144115188075855872), by norm_num⟩
  | 5 => ⟨((858346259/576460752303423488), (-213362331/144115188075855872)), (45409/576460752303423488), by norm_num⟩
  | 6 => ⟨((555209723/1152921504606846976), (-40340313/288230376151711744)), (126523/2305843009213693952), by norm_num⟩
  | 7 => ⟨((459811167/4611686018427387904), (24438471/1152921504606846976)), (414441/9223372036854775808), by norm_num⟩
  | 8 => ⟨((127666811/9223372036854775808), (424759317/36893488147419103232)), (3058005/73786976294838206464), by norm_num⟩
  | 9 => ⟨((323657127/295147905179352825856), (381458221/147573952589676412928)), (11917535/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-120760499/4722366482869645213696), (922761945/2361183241434822606848)), (189318443/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-232555477/9444732965739290427392), (808338399/18889465931478580854784)), (755946587/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-176687477/37778931862957161709568), (60725639/18889465931478580854784)), (1511304585/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((-22331557/37778931862957161709568), (3754083/37778931862957161709568)), (755592329/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-1069551/18889465931478580854784), (-564253/37778931862957161709568)), (1511162031/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-78757/18889465931478580854784), (-125017/37778931862957161709568)), (1511158051/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-8177/37778931862957161709568), (-15017/37778931862957161709568)), (1511157395/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile036Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-98746773/4194304), (40639233/2097152)), (7365/33554432), by norm_num⟩
  | 1 => ⟨((419731119/16777216), (254943643/16777216)), (8253/33554432), by norm_num⟩
  | 2 => ⟨((-442501095/33554432), (-424621547/33554432)), (8729/33554432), by norm_num⟩
  | 3 => ⟨((338564827/67108864), (27133797/4194304)), (34267/134217728), by norm_num⟩
  | 4 => ⟨((-196968969/134217728), (-162784393/67108864)), (128611/536870912), by norm_num⟩
  | 5 => ⟨((44833649/134217728), (194701733/268435456)), (239697/1073741824), by norm_num⟩
  | 6 => ⟨((-31587567/536870912), (-24289127/134217728)), (1817219/8589934592), by norm_num⟩
  | 7 => ⟨((3939039/536870912), (10386551/268435456)), (1760827/8589934592), by norm_num⟩
  | 8 => ⟨((-755731/2147483648), (-3870095/536870912)), (27749295/137438953472), by norm_num⟩
  | 9 => ⟨((-519627/4294967296), (634953/536870912)), (110309947/549755813888), by norm_num⟩
  | 10 => ⟨((799975/17179869184), (-2954145/17179869184)), (1760999341/8796093022208), by norm_num⟩
  | 11 => ⟨((-178713/17179869184), (1525897/68719476736)), (1759724717/8796093022208), by norm_num⟩
  | 12 => ⟨((250329/137438953472), (-174525/68719476736)), (1759351021/8796093022208), by norm_num⟩
  | 13 => ⟨((-297361/1099511627776), (34975/137438953472)), (1759250757/8796093022208), by norm_num⟩
  | 14 => ⟨((38721/1099511627776), (-95483/4398046511104)), (1759225889/8796093022208), by norm_num⟩
  | 15 => ⟨((-35989/8796093022208), (25/17179869184)), (879610073/4398046511104), by norm_num⟩
  | 16 => ⟨((941/2199023255552), (-233/4398046511104)), (1759218913/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile036Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33263/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33263/1280))
  have he : value ((69/80), (33263/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1996339293/134217728)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-230862815873775/562949953421312), (-63627137541769/140737488355328)), (45683293/1125899906842624), by norm_num⟩
  | 1 => ⟨((1008131275/4294967296), (1111387419/4294967296)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((-72127375/1073741824), (-636119197/8589934592)), (15/2147483648), by norm_num⟩
  | 3 => ⟨((880707859/68719476736), (970912875/68719476736)), (47/34359738368), by norm_num⟩
  | 4 => ⟨((-1008172607/549755813888), (-1111432985/549755813888)), (55/274877906944), by norm_num⟩
  | 5 => ⟨((923268251/4398046511104), (254458111/1099511627776)), (103/4398046511104), by norm_num⟩
  | 6 => ⟨((-704595173/35184372088832), (-776762145/35184372088832)), (81/35184372088832), by norm_num⟩
  | 7 => ⟨((921795603/562949953421312), (508104481/281474976710656)), (109/562949953421312), by norm_num⟩
  | 8 => ⟨((-16487609/140737488355328), (-581642385/4503599627370496)), (1/70368744177664), by norm_num⟩
  | 9 => ⟨((536856427/72057594037927936), (591843041/72057594037927936)), (67/72057594037927936), by norm_num⟩
  | 10 => ⟨((-983288955/2305843009213693952), (-1084000667/2305843009213693952)), (63/1152921504606846976), by norm_num⟩
  | 11 => ⟨((409309183/18446744073709551616), (902463971/36893488147419103232)), (107/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-624731273/590295810358705651712), (-688718319/590295810358705651712)), (21/147573952589676412928), by norm_num⟩
  | 13 => ⟨((440091421/9444732965739290427392), (242583521/4722366482869645213696)), (121/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-575755203/302231454903657293676544), (-634725957/302231454903657293676544)), (81/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((351511567/4835703278458516698824704), (775029091/9671406556917033397649408)), (101/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-100596449/38685626227668133590597632), (-887198963/309485009821345068724781056)), (59/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-1502898734507/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890601324320745/316912650057057350374175801344), (-3566486337623/633825300114114700748351602688)), (34707/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473119822321067/9903520314283042199192993792), (-4012102827471/39614081257132168796771975168)), (19527/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892424639261035/2475880078570760549798248448), (-4262642538753/2475880078570760549798248448)), (1297/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((887044986950239/77371252455336267181195264), (-4262398604729/154742504910672534362390528)), (41515/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552270534567799/9671406556917033397649408), (-124866855953/302231454903657293676544)), (9733/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261165182407627/604462909807314587353088), (-3496012528601/604462909807314587353088)), (34077/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945826016891365/37778931862957161709568), (-710066702787/9444732965739290427392)), (55397/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325108212717701/1180591620717411303424), (-4259974031961/4722366482869645213696)), (41567/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203177993260667/73786976294838206464), (-366048199993/36893488147419103232)), (28593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828440522728465/73786976294838206464), (-3659961703775/36893488147419103232)), (71529/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828238182146877/9223372036854775808), (-1029185184277/1152921504606846976)), (40267/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599479993169157/1152921504606846976), (-8231688709383/1152921504606846976)), (40307/576460752303423488), by norm_num⟩
  | 5 => ⟨((149922575062395/18014398509481984), (-3600353789323/72057594037927936)), (17657/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498822111375211/36028797018963968), (-10797013337309/36028797018963968)), (53061/18014398509481984), by norm_num⟩
  | 3 => ⟨((749106129405359/4503599627370496), (-3372291189753/2251799813685248)), (132969/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122889199549657/2251799813685248), (-3369619056003/562949953421312)), (133445/2251799813685248), by norm_num⟩
  | 1 => ⟨((280331553598141/281474976710656), (-10095434200477/562949953421312)), (201357/1125899906842624), by norm_num⟩
  | 0 => ⟨((558261281573573/562949953421312), (-40273607348019/1125899906842624)), (101871/281474976710656), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558261281573573/562949953421312), (-40273607348019/1125899906842624)), (388607026220226199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1105782728110549/1125899906842624), (-4992272295933/70368744177664)), (837333/1125899906842624), by norm_num⟩
  | 2 => ⟨((1080358211267163/1125899906842624), (-78449154427567/562949953421312)), (1763553/1125899906842624), by norm_num⟩
  | 3 => ⟨((507397140006375/562949953421312), (-150551905436181/562949953421312)), (1937977/562949953421312), by norm_num⟩
  | 4 => ⟨((417063683954993/562949953421312), (-542780798019951/1125899906842624)), (9060061/1125899906842624), by norm_num⟩
  | 5 => ⟨((178149704409443/562949953421312), (-804242571924731/1125899906842624)), (22159825/1125899906842624), by norm_num⟩
  | 6 => ⟨((-230862815873775/562949953421312), (-63627137541769/140737488355328)), (45683293/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1996339293/134217728)), (3/134217728), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((677011695/36028797018963968), (466047161/36028797018963968)), (979/9007199254740992), by norm_num⟩
  | 1 => ⟨((66006321/18014398509481984), (419428993/18014398509481984)), (18593/72057594037927936), by norm_num⟩
  | 2 => ⟨((-525094665/72057594037927936), (683071415/72057594037927936)), (24635/72057594037927936), by norm_num⟩
  | 3 => ⟨((-568296817/144115188075855872), (119625413/288230376151711744)), (23243/72057594037927936), by norm_num⟩
  | 4 => ⟨((-424188611/576460752303423488), (-720414833/1152921504606846976)), (281835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-51333237/4611686018427387904), (-1691071401/9223372036854775808)), (379793/2305843009213693952), by norm_num⟩
  | 6 => ⟨((707197915/36893488147419103232), (-96553863/4611686018427387904)), (4067377/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1078052643/295147905179352825856), (-36351381/295147905179352825856)), (23974425/295147905179352825856), by norm_num⟩
  | 8 => ⟨((687308247/2361183241434822606848), (643949975/2361183241434822606848)), (161436679/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((31776203/18889465931478580854784), (704946161/18889465931478580854784)), (299687693/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-18587829/9444732965739290427392), (5434179/2361183241434822606848)), (72969979/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-4001135/18889465931478580854784), (570651/18889465931478580854784)), (579046557/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-216255/18889465931478580854784), (-15959/2361183241434822606848)), (577755681/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-5827/18889465931478580854784), (-1587/2361183241434822606848)), (1154863479/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((67/18889465931478580854784), (-719/18889465931478580854784)), (1154713323/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((19/18889465931478580854784), (-31/18889465931478580854784)), (1154680969/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/9444732965739290427392), (-1/18889465931478580854784)), (577337225/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-195079145/281474976710656), (67098579/1125899906842624)), (26187/2251799813685248), by norm_num⟩
  | 1 => ⟨((-594260303/2251799813685248), (594521969/4503599627370496)), (8209/281474976710656), by norm_num⟩
  | 2 => ⟨((-403503437/1125899906842624), (-75771897/562949953421312)), (104531/2251799813685248), by norm_num⟩
  | 3 => ⟨((142986145/9007199254740992), (-1138110803/9007199254740992)), (501733/9007199254740992), by norm_num⟩
  | 4 => ⟨((109850975/9007199254740992), (-380435645/72057594037927936)), (1007105/18014398509481984), by norm_num⟩
  | 5 => ⟨((594277491/288230376151711744), (-780814123/288230376151711744)), (1787813/36028797018963968), by norm_num⟩
  | 6 => ⟨((270798377/288230376151711744), (40683963/144115188075855872)), (11899521/288230376151711744), by norm_num⟩
  | 7 => ⟨((-23503121/2305843009213693952), (130682175/1152921504606846976)), (78574131/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-35835669/9223372036854775808), (79551245/36893488147419103232)), (1076241147/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-1574555/4611686018427387904), (23606065/36893488147419103232)), (1945389965/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-6997273/73786976294838206464), (-1294513/73786976294838206464)), (1842230505/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-18307/36893488147419103232), (-337203/73786976294838206464)), (1796537061/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-7679/73786976294838206464), (-8541/73786976294838206464)), (1778269937/73786976294838206464), by norm_num⟩
  | 13 => ⟨((367/73786976294838206464), (-455/18446744073709551616)), (1771605967/73786976294838206464), by norm_num⟩
  | 14 => ⟨((5/4611686018427387904), (-5/36893488147419103232)), (442342017/18446744073709551616), by norm_num⟩
  | 15 => ⟨((1/36893488147419103232), (-1/73786976294838206464)), (1768671577/73786976294838206464), by norm_num⟩
  | 16 => ⟨(0, 0), (1768469769/73786976294838206464), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-780316587/1125899906842624), (16774647/281474976710656)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-148565075/562949953421312), (74315251/562949953421312)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-201751721/562949953421312), (-75771895/562949953421312)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((1117079/70368744177664), (-71131925/562949953421312)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((13731373/1125899906842624), (-1486077/281474976710656)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((580349/281474976710656), (-1525027/562949953421312)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((528903/562949953421312), (158921/562949953421312)), (1/8589934592), by norm_num⟩
  | 7 => ⟨((-2869/281474976710656), (31905/281474976710656)), (1/8589934592), by norm_num⟩
  | 8 => ⟨((-4375/1125899906842624), (607/281474976710656)), (1/8589934592), by norm_num⟩
  | 9 => ⟨((-3/8796093022208), (45/70368744177664)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-107/1125899906842624), (-5/281474976710656)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((-1/1125899906842624), (-5/1125899906842624)), (1/8589934592), by norm_num⟩
  | 12 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 13 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 14 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 15 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | 16 => ⟨(0, 0), (1/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨36,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨36,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(381/536870912)) (L:=(25663771173007/36893488147419103232)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile036
