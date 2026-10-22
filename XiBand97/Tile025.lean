/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile025Gamma
import XiBand97.Tile025Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile025
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1122992305/4503599627370496), (-96307895/562949953421312)), (687/2251799813685248), by norm_num⟩
  | 1 => ⟨((1951845973/4503599627370496), (-54094427/2251799813685248)), (2869/4503599627370496), by norm_num⟩
  | 2 => ⟨((1230229475/4503599627370496), (648297293/4503599627370496)), (809/1125899906842624), by norm_num⟩
  | 3 => ⟨((685072355/9007199254740992), (17394677/140737488355328)), (631/1125899906842624), by norm_num⟩
  | 4 => ⟨((44537459/36028797018963968), (1825981045/36028797018963968)), (1535/4503599627370496), by norm_num⟩
  | 5 => ⟨((-480809541/72057594037927936), (890173649/72057594037927936)), (12935/72057594037927936), by norm_num⟩
  | 6 => ⟨((-782136049/288230376151711744), (247579687/144115188075855872)), (3389/36028797018963968), by norm_num⟩
  | 7 => ⟨((-1436550313/2305843009213693952), (44975735/1152921504606846976)), (66891/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-882931093/9223372036854775808), (-403984375/9223372036854775808)), (417607/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-354679449/36893488147419103232), (-28494481/2305843009213693952)), (763337/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-235123669/590295810358705651712), (-1205412235/590295810358705651712)), (5951211/147573952589676412928), by norm_num⟩
  | 11 => ⟨((153323737/2361183241434822606848), (-1138754257/4722366482869645213696)), (94614625/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((669230285/37778931862957161709568), (-786227345/37778931862957161709568)), (755846249/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((47037205/18889465931478580854784), (-5500733/4722366482869645213696)), (1511256731/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((4834649/18889465931478580854784), (-230613/37778931862957161709568)), (188896819/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((390409/18889465931478580854784), (307719/37778931862957161709568)), (47223753/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((24723/18889465931478580854784), (23517/18889465931478580854784)), (755578855/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile025Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-21630789/67108864), (929206719/33554432)), (895/4194304), by norm_num⟩
  | 1 => ⟨((-2818353/134217728), (-1652844873/134217728)), (967/4194304), by norm_num⟩
  | 2 => ⟨((39591587/134217728), (344433809/33554432)), (32213/134217728), by norm_num⟩
  | 3 => ⟨((20816359/67108864), (-667433685/134217728)), (15899/67108864), by norm_num⟩
  | 4 => ⟨((-20169585/67108864), (228514069/134217728)), (121515/536870912), by norm_num⟩
  | 5 => ⟨((38055373/268435456), (-121005147/268435456)), (462513/2147483648), by norm_num⟩
  | 6 => ⟨((-6286503/134217728), (51963405/536870912)), (1783363/8589934592), by norm_num⟩
  | 7 => ⟨((6506029/536870912), (-18549249/1073741824)), (1746051/8589934592), by norm_num⟩
  | 8 => ⟨((-695551/268435456), (1387123/536870912)), (27657967/137438953472), by norm_num⟩
  | 9 => ⟨((2028393/4294967296), (-687535/2147483648)), (110182843/549755813888), by norm_num⟩
  | 10 => ⟨((-642597/8589934592), (536427/17179869184)), (1760359341/8796093022208), by norm_num⟩
  | 11 => ⟨((716319/68719476736), (-133247/68719476736)), (1759541037/8796093022208), by norm_num⟩
  | 12 => ⟨((-353585/274877906944), (-13377/274877906944)), (1759302381/8796093022208), by norm_num⟩
  | 13 => ⟨((154813/1099511627776), (42669/1099511627776)), (1759238789/8796093022208), by norm_num⟩
  | 14 => ⟨((-59821/4398046511104), (-33363/4398046511104)), (1759223137/8796093022208), by norm_num⟩
  | 15 => ⟨((5015/4398046511104), (37/34359738368)), (1759219559/8796093022208), by norm_num⟩
  | 16 => ⟨((-349/4398046511104), (-559/4398046511104)), (879609397/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile025Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (29683/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (29683/1280))
  have he : value ((69/80), (29683/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-890739549/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((130663551340363/281474976710656), (-892460753340509/2251799813685248)), (36333731/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1141162661/4294967296), (974298951/4294967296)), (21/2147483648), by norm_num⟩
  | 2 => ⟨((326580751/4294967296), (-139413641/2147483648)), (13/4294967296), by norm_num⟩
  | 3 => ⟨((-62307791/4294967296), (425575897/34359738368)), (21/34359738368), by norm_num⟩
  | 4 => ⟨((142651181/68719476736), (-60896181/34359738368)), (51/549755813888), by norm_num⟩
  | 5 => ⟨((-1045101249/4398046511104), (892283883/4398046511104)), (49/4398046511104), by norm_num⟩
  | 6 => ⟨((797572423/35184372088832), (-85118669/4398046511104)), (5/4398046511104), by norm_num⟩
  | 7 => ⟨((-1043434273/562949953421312), (55678791/35184372088832)), (55/562949953421312), by norm_num⟩
  | 8 => ⟨((298612599/2251799813685248), (-509897409/4503599627370496)), (33/4503599627370496), by norm_num⟩
  | 9 => ⟨((-151924785/18014398509481984), (518839825/72057594037927936)), (9/18014398509481984), by norm_num⟩
  | 10 => ⟨((278260547/576460752303423488), (-475145163/1152921504606846976)), (17/576460752303423488), by norm_num⟩
  | 11 => ⟨((-926641933/36893488147419103232), (395572995/18446744073709551616)), (59/36893488147419103232), by norm_num⟩
  | 12 => ⟨((353584905/295147905179352825856), (-603765639/590295810358705651712)), (47/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-498165179/9444732965739290427392), (850644395/18889465931478580854784)), (69/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((81466367/37778931862957161709568), (-278216589/151115727451828646838272)), (47/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-795792939/9671406556917033397649408), (169857517/2417851639229258349412352)), (59/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((910967961/309485009821345068724781056), (-12152561/4835703278458516698824704)), (35/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-920533492165/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890604393364181/316912650057057350374175801344), (-1092245953687/633825300114114700748351602688)), (11539/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946243284692507/19807040628566084398385987584), (-307180357075/9903520314283042199192993792)), (6491/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((473108207198501/618970019642690137449562112), (-1305450669223/2475880078570760549798248448)), (27589/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887049337308635/77371252455336267181195264), (-163172073877/19342813113834066795298816)), (27591/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776139617269793/4835703278458516698824704), (-152963980985/1208925819614629174706176)), (25869/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630586668919687/302231454903657293676544), (-1070669162833/604462909807314587353088)), (11319/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236458288025519/9444732965739290427392), (-869844912013/37778931862957161709568)), (18395/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300444444102521/4722366482869645213696), (-1304638252679/4722366482869645213696)), (27597/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625441333331835/590295810358705651712), (-896833896761/295147905179352825856)), (593/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1828464425963547/73786976294838206464), (-2241770050947/73786976294838206464)), (47449/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914134027421885/4611686018427387904), (-315194828937/1152921504606846976)), (53393/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599513591220121/1152921504606846976), (-2521017823111/1152921504606846976)), (53409/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199414187624869/144115188075855872), (-275660279483/18014398509481984)), (1461/4503599627370496), by norm_num⟩
  | 4 => ⟨((1498880864238793/36028797018963968), (-1653353380189/18014398509481984)), (17541/9007199254740992), by norm_num⟩
  | 3 => ⟨((187287542353985/1125899906842624), (-2065627347115/4503599627370496)), (87769/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122999213208327/2251799813685248), (-2064031062565/1125899906842624)), (43933/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121545982056019/1125899906842624), (-6184113746895/1125899906842624)), (16505/140737488355328), by norm_num⟩
  | 0 => ⟨((558590282012145/562949953421312), (-6168160825255/562949953421312)), (265047/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558590282012145/562949953421312), (-6168160825255/562949953421312)), (1011074070457076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1108393579409187/1125899906842624), (-12240785078445/562949953421312)), (265899/562949953421312), by norm_num⟩
  | 2 => ⟨((1090627126030841/1125899906842624), (-48201825066045/1125899906842624)), (535093/562949953421312), by norm_num⟩
  | 3 => ⟨((1054395781436485/1125899906842624), (-93383466188651/1125899906842624)), (270619/140737488355328), by norm_num⟩
  | 4 => ⟨((979687435312869/1125899906842624), (-87452829693673/562949953421312)), (4414047/1125899906842624), by norm_num⟩
  | 5 => ⟨((412645687053097/562949953421312), (-152191927386709/562949953421312)), (2263269/281474976710656), by norm_num⟩
  | 6 => ⟨((130663551340363/281474976710656), (-892460753340509/2251799813685248)), (36333731/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-890739549/67108864)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((215945115/4503599627370496), (-1605469695/9007199254740992)), (2427/9007199254740992), by norm_num⟩
  | 1 => ⟨((184897161/1125899906842624), (-364344473/4503599627370496)), (3199/4503599627370496), by norm_num⟩
  | 2 => ⟨((738679085/9007199254740992), (613573157/18014398509481984)), (139/140737488355328), by norm_num⟩
  | 3 => ⟨((161312989/18014398509481984), (956836149/36028797018963968)), (33981/36028797018963968), by norm_num⟩
  | 4 => ⟨((-233809905/72057594037927936), (402254897/72057594037927936)), (49959/72057594037927936), by norm_num⟩
  | 5 => ⟨((-652983409/576460752303423488), (128268183/576460752303423488)), (122493/288230376151711744), by norm_num⟩
  | 6 => ⟨((-608480997/4611686018427387904), (-465551905/4611686018427387904)), (1088899/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-55760249/36893488147419103232), (-724264179/36893488147419103232)), (9842851/73786976294838206464), by norm_num⟩
  | 8 => ⟨((786284877/590295810358705651712), (-839177339/590295810358705651712)), (51508263/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1530256559/9444732965739290427392), (-3126025/2361183241434822606848)), (656358647/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((38657373/4722366482869645213696), (148432925/18889465931478580854784)), (74951689/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((1297807/18889465931478580854784), (1574911/2361183241434822606848)), (582455895/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-73275/4722366482869645213696), (579173/18889465931478580854784)), (1155512165/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-24651/18889465931478580854784), (333/295147905179352825856)), (576577513/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-863/9444732965739290427392), (653/18889465931478580854784)), (144076159/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((-103/18889465931478580854784), (-13/18889465931478580854784)), (288122947/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((-1/4722366482869645213696), (-3/18889465931478580854784)), (1152468135/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1385009069/281474976710656), (194962645/140737488355328)), (491/8796093022208), by norm_num⟩
  | 1 => ⟨((-2419217/281474976710656), (1122254729/281474976710656)), (35939/281474976710656), by norm_num⟩
  | 2 => ⟨((-282742579/2251799813685248), (382280259/562949953421312)), (393717/2251799813685248), by norm_num⟩
  | 3 => ⟨((-705308315/2251799813685248), (1344117631/2251799813685248)), (218749/1125899906842624), by norm_num⟩
  | 4 => ⟨((-482836275/2251799813685248), (-128661019/2251799813685248)), (869097/4503599627370496), by norm_num⟩
  | 5 => ⟨((96913603/36028797018963968), (-1155393283/36028797018963968)), (6476615/36028797018963968), by norm_num⟩
  | 6 => ⟨((196777641/144115188075855872), (-1679803/2251799813685248)), (2945689/18014398509481984), by norm_num⟩
  | 7 => ⟨((701782189/4611686018427387904), (-1306781865/4611686018427387904)), (690665817/4611686018427387904), by norm_num⟩
  | 8 => ⟨((242195021/4611686018427387904), (101854043/9223372036854775808)), (1295066577/9223372036854775808), by norm_num⟩
  | 9 => ⟨((335669/9223372036854775808), (7988887/2305843009213693952)), (1245222605/9223372036854775808), by norm_num⟩
  | 10 => ⟨((10195/2305843009213693952), (614361/9223372036854775808)), (1220025651/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-39495/9223372036854775808), (154337/9223372036854775808)), (302168141/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-9409/9223372036854775808), (419/9223372036854775808)), (602026289/4611686018427387904), by norm_num⟩
  | 13 => ⟨((-211/9223372036854775808), (19/4611686018427387904)), (1202337267/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-41/9223372036854775808), (-15/9223372036854775808)), (300437871/2305843009213693952), by norm_num⟩
  | 15 => ⟨(0, (-1/2305843009213693952)), (75097893/576460752303423488), by norm_num⟩
  | 16 => ⟨(0, 0), (1201511813/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((5540036139/1125899906842624), (389925281/281474976710656)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-9676913/1125899906842624), (4489018805/1125899906842624)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((-141371241/1125899906842624), (764560481/1125899906842624)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((-352654183/1125899906842624), (84007353/140737488355328)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-60354529/281474976710656), (-32165261/562949953421312)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((757135/281474976710656), (-18053013/562949953421312)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((1537325/1125899906842624), (-839907/1125899906842624)), (1/1073741824), by norm_num⟩
  | 7 => ⟨((42833/281474976710656), (-319037/1125899906842624)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((59129/1125899906842624), (777/70368744177664)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((41/1125899906842624), (3901/1125899906842624)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((5/1125899906842624), (75/1125899906842624)), (1/1073741824), by norm_num⟩
  | 11 => ⟨((-5/1125899906842624), (19/1125899906842624)), (1/1073741824), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/1073741824), by norm_num⟩
  | 13 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 14 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 15 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 16 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨25,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨25,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(2431/536870912)) (L:=(6034977850133929/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile025
