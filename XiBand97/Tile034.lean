/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile034Gamma
import XiBand97.Tile034Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile034
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-598788179/18014398509481984), (830396971/18014398509481984)), (2965/18014398509481984), by norm_num⟩
  | 1 => ⟨((-691903119/9007199254740992), (19010513/562949953421312)), (5557/18014398509481984), by norm_num⟩
  | 2 => ⟨((-1100553263/18014398509481984), (-124587737/18014398509481984)), (6027/18014398509481984), by norm_num⟩
  | 3 => ⟨((-865047259/36028797018963968), (-636284137/36028797018963968)), (9335/36028797018963968), by norm_num⟩
  | 4 => ⟨((-633523945/144115188075855872), (-1414460539/144115188075855872)), (23607/144115188075855872), by norm_num⟩
  | 5 => ⟨((155916797/576460752303423488), (-221130343/72057594037927936)), (6961/72057594037927936), by norm_num⟩
  | 6 => ⟨((117015331/288230376151711744), (-699322361/1152921504606846976)), (17805/288230376151711744), by norm_num⟩
  | 7 => ⟨((1199423293/9223372036854775808), (-158692199/2305843009213693952)), (217853/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1901116097/73786976294838206464), (-106247/4611686018427387904)), (3108053/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1044915837/295147905179352825856), (538641407/295147905179352825856)), (11970253/295147905179352825856), by norm_num⟩
  | 10 => ⟨((190855011/590295810358705651712), (526129389/1180591620717411303424)), (94759879/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((55183505/4722366482869645213696), (1280279557/18889465931478580854784)), (378061219/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-80450825/37778931862957161709568), (142400119/18889465931478580854784)), (377843851/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-20187807/37778931862957161709568), (23487933/37778931862957161709568)), (1511197895/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-2715421/37778931862957161709568), (635709/18889465931478580854784)), (377791085/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-16877/2361183241434822606848), (7297/37778931862957161709568)), (1511158429/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-21215/37778931862957161709568), (-8271/37778931862957161709568)), (1511157453/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile034Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-407740681/33554432), (669504669/67108864)), (3661/16777216), by norm_num⟩
  | 1 => ⟨((531932817/67108864), (389491041/16777216)), (1017/4194304), by norm_num⟩
  | 2 => ⟨((-59599925/67108864), (-272636521/16777216)), (17099/67108864), by norm_num⟩
  | 3 => ⟨((-53047739/67108864), (62143389/8388608)), (33589/134217728), by norm_num⟩
  | 4 => ⟨((40637617/67108864), (-337308771/134217728)), (126659/536870912), by norm_num⟩
  | 5 => ⟨((-34169159/134217728), (22775189/33554432)), (474761/2147483648), by norm_num⟩
  | 6 => ⟨((42856579/536870912), (-81351191/536870912)), (1808067/8589934592), by norm_num⟩
  | 7 => ⟨((-21880833/1073741824), (30655893/1073741824)), (1756899/8589934592), by norm_num⟩
  | 8 => ⟨((4733215/1073741824), (-9838043/2147483648)), (27725423/137438953472), by norm_num⟩
  | 9 => ⟨((-3550757/4294967296), (1340081/2147483648)), (110277051/549755813888), by norm_num⟩
  | 10 => ⟨((2343847/17179869184), (-1210967/17179869184)), (1760835501/8796093022208), by norm_num⟩
  | 11 => ⟨((-1375177/68719476736), (419595/68719476736)), (1759678381/8796093022208), by norm_num⟩
  | 12 => ⟨((45121/17179869184), (-76141/274877906944)), (1759338925/8796093022208), by norm_num⟩
  | 13 => ⟨((-340329/1099511627776), (-8155/274877906944)), (1759247829/8796093022208), by norm_num⟩
  | 14 => ⟨((144087/4398046511104), (45369/4398046511104)), (1759225205/8796093022208), by norm_num⟩
  | 15 => ⟨((-13631/4398046511104), (-15709/8796093022208)), (1759220005/8796093022208), by norm_num⟩
  | 16 => ⟨((2275/8796093022208), (1055/4398046511104)), (439804721/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile034Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32547/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32547/1280))
  have he : value ((69/80), (32547/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-976683627/67108864)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-556123681400297/2251799813685248), (-628466848920233/1125899906842624)), (88749597/2251799813685248), by norm_num⟩
  | 1 => ⟨((151779985/1073741824), (1372193879/4294967296)), (99/4294967296), by norm_num⟩
  | 2 => ⟨((-173747085/4294967296), (-785395671/8589934592)), (59/8589934592), by norm_num⟩
  | 3 => ⟨((66297827/8589934592), (1198754529/68719476736)), (93/68719476736), by norm_num⟩
  | 4 => ⟨((-4743319/4294967296), (-171531267/68719476736)), (109/549755813888), by norm_num⟩
  | 5 => ⟨((139003367/1099511627776), (628342297/2199023255552)), (103/4398046511104), by norm_num⟩
  | 6 => ⟨((-424323489/35184372088832), (-479521471/17592186044416)), (81/35184372088832), by norm_num⟩
  | 7 => ⟨((555126605/562949953421312), (1254680135/562949953421312)), (27/140737488355328), by norm_num⟩
  | 8 => ⟨((-635470015/9007199254740992), (-179533731/1125899906842624)), (63/4503599627370496), by norm_num⟩
  | 9 => ⟨((646614683/144115188075855872), (365364671/36028797018963968)), (131/144115188075855872), by norm_num⟩
  | 10 => ⟨((-296079661/1152921504606846976), (-669190173/1152921504606846976)), (61/1152921504606846976), by norm_num⟩
  | 11 => ⟨((246495445/18446744073709551616), (1114242895/36893488147419103232)), (13/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-94056901/147573952589676412928), (-850338095/590295810358705651712)), (81/590295810358705651712), by norm_num⟩
  | 13 => ⟨((66258305/2361183241434822606848), (1198039915/18889465931478580854784)), (117/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-346733083/302231454903657293676544), (-783675483/302231454903657293676544)), (39/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((423376771/9671406556917033397649408), (239225799/2417851639229258349412352)), (97/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-484652043/309485009821345068724781056), (-1095395687/309485009821345068724781056)), (113/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-2588744673645/10141204801825835211973625643008)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890602198923167/316912650057057350374175801344), (-767909565209/158456325028528675187087900672)), (34689/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946240681967587/19807040628566084398385987584), (-431928636905/4951760157141521099596496896)), (4879/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1892426973072157/2475880078570760549798248448), (-3671207185213/2475880078570760549798248448)), (5185/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((55440389168295/4835703278458516698824704), (-3670997599571/154742504910672534362390528)), (41489/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((97017063364975/604462909807314587353088), (-860334372885/2417851639229258349412352)), (19453/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630583753249169/302231454903657293676544), (-3010947464601/604462909807314587353088)), (34053/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29557126570125/1180591620717411303424), (-4892371628927/75557863725914323419136)), (55355/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162554519330427/590295810358705651712), (-1834456397863/2361183241434822606848)), (10383/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((406357225249799/147573952589676412928), (-5044160136351/590295810358705651712)), (28567/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457111833630807/18446744073709551616), (-1576076789987/18446744073709551616)), (71457/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828246695070761/9223372036854775808), (-7091116733591/9223372036854775808)), (80445/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99968097981473/72057594037927936), (-7089579309983/1152921504606846976)), (40257/576460752303423488), by norm_num⟩
  | 5 => ⟨((599695085948899/72057594037927936), (-6201650375481/144115188075855872)), (70527/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498838854254777/36028797018963968), (-1162375966055/4503599627370496)), (52973/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498237358962595/9007199254740992), (-5808840088895/4503599627370496)), (132705/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122920549875951/2251799813685248), (-11608539442307/2251799813685248)), (66557/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121388840173105/1125899906842624), (-17389882181133/1125899906842624)), (25087/140737488355328), by norm_num⟩
  | 0 => ⟨((1116710064163523/1125899906842624), (-34687606740671/1125899906842624)), (405495/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116710064163523/1125899906842624), (-34687606740671/1125899906842624)), (1546840672019576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1106526548027191/1125899906842624), (-68808957729967/1125899906842624)), (829357/1125899906842624), by norm_num⟩
  | 2 => ⟨((1083281312497319/1125899906842624), (-135249924096373/1125899906842624)), (1731545/1125899906842624), by norm_num⟩
  | 3 => ⟨((256507228799183/281474976710656), (-260260640221833/1125899906842624)), (1874005/562949953421312), by norm_num⟩
  | 4 => ⟨((874855507123499/1125899906842624), (-29646834138221/70368744177664)), (1070483/140737488355328), by norm_num⟩
  | 5 => ⟨((479940403946169/1125899906842624), (-368582620276919/562949953421312)), (20524751/1125899906842624), by norm_num⟩
  | 6 => ⟨((-556123681400297/2251799813685248), (-628466848920233/1125899906842624)), (88749597/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-976683627/67108864)), (3/134217728), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1222803389/36028797018963968), (258312145/36028797018963968)), (611/4503599627370496), by norm_num⟩
  | 1 => ⟨((662758833/36028797018963968), (1096526813/36028797018963968)), (11905/36028797018963968), by norm_num⟩
  | 2 => ⟨((-43779877/9007199254740992), (1240500859/72057594037927936)), (7909/18014398509481984), by norm_num⟩
  | 3 => ⟨((-752283113/144115188075855872), (389237249/144115188075855872)), (59333/144115188075855872), by norm_num⟩
  | 4 => ⟨((-1539836665/1152921504606846976), (-543307113/1152921504606846976)), (352711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-498147505/4611686018427387904), (-1123091799/4611686018427387904)), (912653/4611686018427387904), by norm_num⟩
  | 6 => ⟨((286811217/18446744073709551616), (-1385377371/36893488147419103232)), (2287493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1416301341/295147905179352825856), (-556644451/295147905179352825856)), (24949573/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1192877639/2361183241434822606848), (266139779/1180591620717411303424)), (158186321/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5441259/295147905179352825856), (893858531/18889465931478580854784)), (569349761/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-28561869/18889465931478580854784), (70364619/18889465931478580854784)), (1095924993/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-2333929/9444732965739290427392), (1165919/9444732965739290427392)), (1082993493/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-153865/9444732965739290427392), (-63525/18889465931478580854784)), (67465393/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-11961/18889465931478580854784), (-6025/9444732965739290427392)), (1078554741/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-125/9444732965739290427392), (-415/9444732965739290427392)), (1078347787/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((3/9444732965739290427392), (-11/4722366482869645213696)), (1078303125/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/18889465931478580854784), (-1/9444732965739290427392)), (539147057/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1089754105/2251799813685248), (566266327/2251799813685248)), (26961/2251799813685248), by norm_num⟩
  | 1 => ⟨((-478042807/1125899906842624), (370669067/562949953421312)), (18105/562949953421312), by norm_num⟩
  | 2 => ⟨((-330488631/562949953421312), (-82918377/562949953421312)), (27845/562949953421312), by norm_num⟩
  | 3 => ⟨((-15337069/4503599627370496), (-637170341/4503599627370496)), (534751/9007199254740992), by norm_num⟩
  | 4 => ⟨((-36489867/72057594037927936), (-894697407/72057594037927936)), (2165553/36028797018963968), by norm_num⟩
  | 5 => ⟨((439649233/144115188075855872), (-239082861/36028797018963968)), (7837765/144115188075855872), by norm_num⟩
  | 6 => ⟨((1620922417/1152921504606846976), (171759675/576460752303423488)), (26765529/576460752303423488), by norm_num⟩
  | 7 => ⟨((16828657/4611686018427387904), (1119676329/9223372036854775808)), (363409057/9223372036854775808), by norm_num⟩
  | 8 => ⟨((14685177/18446744073709551616), (151331891/36893488147419103232)), (318464555/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-7866321/18446744073709551616), (45860357/36893488147419103232)), (584492785/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-4407067/36893488147419103232), (-441445/36893488147419103232)), (1115653077/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-25137/18446744073709551616), (-118321/36893488147419103232)), (545747787/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-5719/18446744073709551616), (-2657/18446744073709551616)), (540803075/18446744073709551616), by norm_num⟩
  | 13 => ⟨((13/4611686018427387904), (-579/18446744073709551616)), (1077907655/36893488147419103232), by norm_num⟩
  | 14 => ⟨((5/9223372036854775808), (-3/9223372036854775808)), (269158405/9223372036854775808), by norm_num⟩
  | 15 => ⟨(0, (-3/36893488147419103232)), (134528347/4611686018427387904), by norm_num⟩
  | 16 => ⟨(0, 0), (134513227/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-136219261/281474976710656), (70783295/281474976710656)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-478042785/1125899906842624), (741338159/1125899906842624)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-660977279/1125899906842624), (-165836741/1125899906842624)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((-3834263/1125899906842624), (-159292585/1125899906842624)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-35635/70368744177664), (-13979645/1125899906842624)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((1717381/562949953421312), (-1867835/281474976710656)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((1582931/1125899906842624), (335469/1125899906842624)), (1/8589934592), by norm_num⟩
  | 7 => ⟨((4109/1125899906842624), (136679/1125899906842624)), (1/8589934592), by norm_num⟩
  | 8 => ⟨((7/8796093022208), (2309/562949953421312)), (1/8589934592), by norm_num⟩
  | 9 => ⟨((-15/35184372088832), (175/140737488355328)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-67/562949953421312), (-13/1125899906842624)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((-1/562949953421312), (-1/281474976710656)), (1/8589934592), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨34,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨34,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(801/536870912)) (L:=(643876375079001/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile034
