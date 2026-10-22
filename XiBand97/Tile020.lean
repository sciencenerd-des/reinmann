/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile020Gamma
import XiBand97.Tile020Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile020
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39927947/70368744177664), (-721586387/1125899906842624)), (1489/1125899906842624), by norm_num⟩
  | 1 => ⟨((-228004645/1125899906842624), (-41793491/35184372088832)), (421/140737488355328), by norm_num⟩
  | 2 => ⟨((175745373/562949953421312), (-438872311/562949953421312)), (481/140737488355328), by norm_num⟩
  | 3 => ⟨((173510499/562949953421312), (-524274043/2251799813685248)), (367/140737488355328), by norm_num⟩
  | 4 => ⟨((36898217/281474976710656), (-8271011/562949953421312)), (13551/9007199254740992), by norm_num⟩
  | 5 => ⟨((1176101925/36028797018963968), (518403783/36028797018963968)), (12805/18014398509481984), by norm_num⟩
  | 6 => ⟨((170898855/36028797018963968), (230290431/36028797018963968)), (1339/4503599627370496), by norm_num⟩
  | 7 => ⟨((228523167/1152921504606846976), (430732111/288230376151711744)), (144185/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-405208039/4611686018427387904), (533541795/2305843009213693952)), (74657/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-123506195/4611686018427387904), (438580911/18446744073709551616)), (1713579/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-330152399/73786976294838206464), (348709161/295147905179352825856)), (1531883/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-1251211439/2361183241434822606848), (-246775907/2361183241434822606848)), (95224081/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-438135599/9444732965739290427392), (-641458181/18889465931478580854784)), (756819275/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-52635293/18889465931478580854784), (-184759081/37778931862957161709568)), (755809027/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-1089585/18889465931478580854784), (-19171949/37778931862957161709568)), (377809335/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((444401/37778931862957161709568), (-786007/18889465931478580854784)), (1511170359/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((78423/37778931862957161709568), (-51719/18889465931478580854784)), (1511159295/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile020Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-254761159/33554432), (459007801/33554432)), (14215/67108864), by norm_num⟩
  | 1 => ⟨((445457951/33554432), (211092071/33554432)), (15315/67108864), by norm_num⟩
  | 2 => ⟨((-292794647/33554432), (-442820717/134217728)), (15931/67108864), by norm_num⟩
  | 3 => ⟨((1033854815/268435456), (51460019/33554432)), (63095/268435456), by norm_num⟩
  | 4 => ⟨((-163558125/134217728), (-10230241/16777216)), (242085/1073741824), by norm_num⟩
  | 5 => ⟨((39839189/134217728), (6664959/33554432)), (462049/2147483648), by norm_num⟩
  | 6 => ⟨((-30961183/536870912), (-7121549/134217728)), (1783491/8589934592), by norm_num⟩
  | 7 => ⟨((9684111/1073741824), (12702995/1073741824)), (1746627/8589934592), by norm_num⟩
  | 8 => ⟨((-2375087/2147483648), (-1204241/536870912)), (110659259/549755813888), by norm_num⟩
  | 9 => ⟨((100563/1073741824), (1576299/4294967296)), (881572311/4398046511104), by norm_num⟩
  | 10 => ⟨((-25737/17179869184), (-899163/17179869184)), (1760452013/8796093022208), by norm_num⟩
  | 11 => ⟨((-92961/68719476736), (112279/17179869184)), (1759573293/8796093022208), by norm_num⟩
  | 12 => ⟨((93977/274877906944), (-196035/274877906944)), (1759312269/8796093022208), by norm_num⟩
  | 13 => ⟨((-62063/1099511627776), (73833/1099511627776)), (1759241573/8796093022208), by norm_num⟩
  | 14 => ⟨((32973/4398046511104), (-23137/4398046511104)), (1759223851/8796093022208), by norm_num⟩
  | 15 => ⟨((-7487/8796093022208), (1347/4398046511104)), (1759219725/8796093022208), by norm_num⟩
  | 16 => ⟨((93/1099511627776), (-7/1099511627776)), (1759218831/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile020Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27893/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27893/1280))
  have he : value ((69/80), (27893/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-209256125/16777216)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((342108016282523/562949953421312), (128645065606681/2251799813685248)), (22603645/2251799813685248), by norm_num⟩
  | 1 => ⟨((-746958295/2147483648), (-140441753/4294967296)), (27/4294967296), by norm_num⟩
  | 2 => ⟨((213766371/2147483648), (1255999/134217728)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((-1305092019/68719476736), (-122690525/68719476736)), (27/68719476736), by norm_num⟩
  | 4 => ⟨((746988919/274877906944), (140447511/549755813888)), (33/549755813888), by norm_num⟩
  | 5 => ⟨((-42755027/137438953472), (-128619571/4398046511104)), (33/4398046511104), by norm_num⟩
  | 6 => ⟨((261029105/8796093022208), (98156445/35184372088832)), (27/35184372088832), by norm_num⟩
  | 7 => ⟨((-1365978595/562949953421312), (-64207209/281474976710656)), (37/562949953421312), by norm_num⟩
  | 8 => ⟨((781838261/4503599627370496), (73499911/4503599627370496)), (45/9007199254740992), by norm_num⟩
  | 9 => ⟨((-1591099775/144115188075855872), (-149577857/144115188075855872)), (3/9007199254740992), by norm_num⟩
  | 10 => ⟨((1457103571/2305843009213693952), (136980995/2305843009213693952)), (47/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-151635455/4611686018427387904), (-114040901/36893488147419103232)), (41/36893488147419103232), by norm_num⟩
  | 12 => ⟨((1851537463/1180591620717411303424), (87030685/590295810358705651712)), (65/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-326078503/4722366482869645213696), (-61308693/9444732965739290427392)), (3/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((853192703/302231454903657293676544), (40103939/151115727451828646838272)), (65/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((-1041786865/9671406556917033397649408), (-97937445/9671406556917033397649408)), (21/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((1192564559/309485009821345068724781056), (7006995/19342813113834066795298816)), (25/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (15262312639/1267650600228229401496703205376)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781209410830533/633825300114114700748351602688), (144874244039/633825300114114700748351602688)), (23055/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892487309603715/39614081257132168796771975168), (162976250777/39614081257132168796771975168)), (1621/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892433661484195/2475880078570760549798248448), (173153539433/2475880078570760549798248448)), (13779/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887049779641839/77371252455336267181195264), (43285930561/38685626227668133590597632)), (13779/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552280119130711/9671406556917033397649408), (40577952405/2417851639229258349412352)), (6459/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((315293541765893/151115727451828646838272), (71006202155/302231454903657293676544)), (22607/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891667755186549/75557863725914323419136), (115375302145/37778931862957161709568)), (287/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1300445622875777/4722366482869645213696), (86522923227/2361183241434822606848)), (27553/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812721550614673/295147905179352825856), (237910243875/590295810358705651712)), (18943/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457116714099079/18446744073709551616), (297346118453/73786976294838206464)), (23679/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228533886530669/1152921504606846976), (83614268599/2305843009213693952)), (1665/288230376151711744), by norm_num⟩
  | 6 => ⟨((1599517007417887/1152921504606846976), (167192726599/576460752303423488)), (53281/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199417602724071/144115188075855872), (18281669885/9007199254740992)), (1457/4503599627370496), by norm_num⟩
  | 4 => ⟨((374721709547795/9007199254740992), (438599021595/36028797018963968)), (17485/9007199254740992), by norm_num⟩
  | 3 => ⟨((374577323704853/2251799813685248), (547967044627/9007199254740992)), (87433/9007199254740992), by norm_num⟩
  | 2 => ⟨((2246020799098053/4503599627370496), (1095089352001/4503599627370496)), (43723/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121568328818739/1125899906842624), (205065474185/281474976710656)), (131201/1125899906842624), by norm_num⟩
  | 0 => ⟨((2234494949612681/2251799813685248), (3272616293603/2251799813685248)), (262531/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((2234494949612681/2251799813685248), (3272616293603/2251799813685248)), (1001476292136764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((277164789443239/281474976710656), (6494933106961/2251799813685248)), (1043581/2251799813685248), by norm_num⟩
  | 2 => ⟨((1091673047137597/1125899906842624), (12790954194761/2251799813685248)), (2061223/2251799813685248), by norm_num⟩
  | 3 => ⟨((2116900680916315/2251799813685248), (12402114838743/1125899906842624)), (4020543/2251799813685248), by norm_num⟩
  | 4 => ⟨((15545388736875/17592186044416), (46636553013957/2251799813685248)), (7647943/2251799813685248), by norm_num⟩
  | 5 => ⟨((1757335568721029/2251799813685248), (41210532000937/1125899906842624)), (13833047/2251799813685248), by norm_num⟩
  | 6 => ⟨((342108016282523/562949953421312), (128645065606681/2251799813685248)), (22603645/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-209256125/16777216)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-347007045/1125899906842624), (-118752395/281474976710656)), (251/281474976710656), by norm_num⟩
  | 1 => ⟨((272919863/2251799813685248), (-1107775803/2251799813685248)), (5661/2251799813685248), by norm_num⟩
  | 2 => ⟨((484967221/2251799813685248), (-118496999/1125899906842624)), (4027/1125899906842624), by norm_num⟩
  | 3 => ⟨((604524959/9007199254740992), (135674107/4503599627370496)), (61303/18014398509481984), by norm_num⟩
  | 4 => ⟨((317130951/72057594037927936), (1139792341/72057594037927936)), (175705/72057594037927936), by norm_num⟩
  | 5 => ⟨((-232290521/144115188075855872), (670347329/288230376151711744)), (101771/72057594037927936), by norm_num⟩
  | 6 => ⟨((-447844183/1152921504606846976), (2508885/72057594037927936)), (3220667/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-574981989/18446744073709551616), (-569335331/18446744073709551616)), (362297/1152921504606846976), by norm_num⟩
  | 8 => ⟨((80996365/295147905179352825856), (-1196969741/295147905179352825856)), (2644045/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1147992995/4722366482869645213696), (-910546203/4722366482869645213696)), (46073225/590295810358705651712), by norm_num⟩
  | 10 => ⟨((363042935/18889465931478580854784), (38753621/18889465931478580854784)), (2119955815/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((845377/1180591620717411303424), (393209/590295810358705651712)), (467674295/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((773107/37778931862957161709568), (1529323/37778931862957161709568)), (1802705335/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((26147/37778931862957161709568), (101343/37778931862957161709568)), (1785710741/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-213/4722366482869645213696), (6661/37778931862957161709568)), (1781785773/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-139/18889465931478580854784), (211/37778931862957161709568)), (1780942377/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-3/9444732965739290427392), (1/37778931862957161709568)), (445193195/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1141566857/140737488355328), (-142548045/140737488355328)), (6109/35184372088832), by norm_num⟩
  | 1 => ⟨((1230596647/281474976710656), (-302128245/140737488355328)), (103421/281474976710656), by norm_num⟩
  | 2 => ⟨((817104919/140737488355328), (376469943/140737488355328)), (4549/8796093022208), by norm_num⟩
  | 3 => ⟨((-349631637/562949953421312), (687466991/281474976710656)), (165603/281474976710656), by norm_num⟩
  | 4 => ⟨((-980117961/2251799813685248), (-41301441/1125899906842624)), (165493/281474976710656), by norm_num⟩
  | 5 => ⟨((-205162381/18014398509481984), (-400769819/18014398509481984)), (19534763/36028797018963968), by norm_num⟩
  | 6 => ⟨((-362350451/72057594037927936), (-398983879/144115188075855872)), (69530887/144115188075855872), by norm_num⟩
  | 7 => ⟨((35495177/144115188075855872), (-627335997/576460752303423488)), (497165421/1152921504606846976), by norm_num⟩
  | 8 => ⟨((12453431/144115188075855872), (3445397/1152921504606846976)), (1828648425/4611686018427387904), by norm_num⟩
  | 9 => ⟨((782457/576460752303423488), (4854845/4611686018427387904)), (868747185/2305843009213693952), by norm_num⟩
  | 10 => ⟨((1721953/4611686018427387904), (525667/4611686018427387904)), (1692310919/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1115/1152921504606846976), (66859/2305843009213693952)), (1672408553/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-865/4611686018427387904), (1707/4611686018427387904)), (832251419/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-83/4611686018427387904), (421/4611686018427387904)), (830819811/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-21/4611686018427387904), (3/2305843009213693952)), (1660686005/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-1/4611686018427387904), (1/2305843009213693952)), (1660391895/4611686018427387904), by norm_num⟩
  | 16 => ⟨(0, 0), (415076855/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((4566267271/562949953421312), (-570192061/562949953421312)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((2461193205/562949953421312), (-2417025821/1125899906842624)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((6536839147/1125899906842624), (3011759555/1125899906842624)), (1/1073741824), by norm_num⟩
  | 3 => ⟨((-699263351/1125899906842624), (2749867919/1125899906842624)), (1/536870912), by norm_num⟩
  | 4 => ⟨((-490058947/1125899906842624), (-10325375/281474976710656)), (1/536870912), by norm_num⟩
  | 5 => ⟨((-12822655/1125899906842624), (-25048067/1125899906842624)), (1/536870912), by norm_num⟩
  | 6 => ⟨((-5661729/1125899906842624), (-3117087/1125899906842624)), (1/536870912), by norm_num⟩
  | 7 => ⟨((277313/1125899906842624), (-612627/562949953421312)), (1/536870912), by norm_num⟩
  | 8 => ⟨((12161/140737488355328), (3363/1125899906842624)), (1/536870912), by norm_num⟩
  | 9 => ⟨((1529/1125899906842624), (1185/1125899906842624)), (1/536870912), by norm_num⟩
  | 10 => ⟨((421/1125899906842624), (1/8796093022208)), (1/536870912), by norm_num⟩
  | 11 => ⟨((-1/1125899906842624), (33/1125899906842624)), (1/536870912), by norm_num⟩
  | 12 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | 13 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | 14 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | 15 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | 16 => ⟨(0, 0), (1/536870912), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨20,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨20,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(11079/1073741824)) (L:=(2412631635020847/295147905179352825856)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile020
