/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile015Gamma
import XiBand97.Tile015Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile015
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-490661851/281474976710656), (253690103/281474976710656)), (951/281474976710656), by norm_num⟩
  | 1 => ⟨((-380875275/140737488355328), (-66572477/281474976710656)), (4219/562949953421312), by norm_num⟩
  | 2 => ⟨((-13072977/8796093022208), (-629565579/562949953421312)), (2341/281474976710656), by norm_num⟩
  | 3 => ⟨((-676537/2199023255552), (-879601975/1125899906842624)), (869/140737488355328), by norm_num⟩
  | 4 => ⟨((105276565/2251799813685248), (-78023577/281474976710656)), (15621/4503599627370496), by norm_num⟩
  | 5 => ⟨((215984821/4503599627370496), (-1025943695/18014398509481984)), (14303/9007199254740992), by norm_num⟩
  | 6 => ⟨((1100612441/72057594037927936), (-400235105/72057594037927936)), (45273/72057594037927936), by norm_num⟩
  | 7 => ⟨((1711807965/576460752303423488), (278646897/576460752303423488)), (134597/576460752303423488), by norm_num⟩
  | 8 => ⟨((440020907/1152921504606846976), (340197333/1152921504606846976)), (221819/2305843009213693952), by norm_num⟩
  | 9 => ⟨((524611659/18446744073709551616), (1142068643/18446744073709551616)), (1007885/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-22453973/73786976294838206464), (39594963/4611686018427387904)), (6413653/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-537985237/1180591620717411303424), (511202023/590295810358705651712)), (24054521/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-761718899/9444732965739290427392), (73174869/1180591620717411303424)), (379207745/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-178517763/18889465931478580854784), (11023589/4722366482869645213696)), (1512214457/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-4035345/4722366482869645213696), (-2490637/18889465931478580854784)), (1511341641/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-2337629/37778931862957161709568), (-686639/18889465931478580854784)), (23612305/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-132645/37778931862957161709568), (-82381/18889465931478580854784)), (1511161963/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile015Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((56574193/8388608), (469249467/67108864)), (3521/16777216), by norm_num⟩
  | 1 => ⟨((-58203757/16777216), (510697177/33554432)), (14995/67108864), by norm_num⟩
  | 2 => ⟨((127774827/67108864), (-1200418311/134217728)), (30985/134217728), by norm_num⟩
  | 3 => ⟨((-14003649/16777216), (7517299/2097152)), (30695/134217728), by norm_num⟩
  | 4 => ⟨((23593083/67108864), (-72397473/67108864)), (237109/1073741824), by norm_num⟩
  | 5 => ⟨((-2061395/16777216), (68722305/268435456)), (456049/2147483648), by norm_num⟩
  | 6 => ⟨((18551103/536870912), (-13189819/268435456)), (1771347/8589934592), by norm_num⟩
  | 7 => ⟨((-8541683/1073741824), (8243735/1073741824)), (1741323/8589934592), by norm_num⟩
  | 8 => ⟨((3295085/2147483648), (-256975/268435456)), (110527675/549755813888), by norm_num⟩
  | 9 => ⟨((-67815/268435456), (373971/4294967296)), (881202647/4398046511104), by norm_num⟩
  | 10 => ⟨((617649/17179869184), (-57279/17179869184)), (1760217005/8796093022208), by norm_num⟩
  | 11 => ⟨((-152863/34359738368), (-48911/68719476736)), (1759504429/8796093022208), by norm_num⟩
  | 12 => ⟨((8209/17179869184), (58659/274877906944)), (1759293997/8796093022208), by norm_num⟩
  | 13 => ⟨((-48263/1099511627776), (-39885/1099511627776)), (1759237045/8796093022208), by norm_num⟩
  | 14 => ⟨((14513/4398046511104), (21177/4398046511104)), (1759222797/8796093022208), by norm_num⟩
  | 15 => ⟨((-767/4398046511104), (-2371/4398046511104)), (439804875/2199023255552), by norm_num⟩
  | 16 => ⟨((7/8796093022208), (115/2199023255552)), (1759218785/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile015Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26461/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26461/1280))
  have he : value ((69/80), (26461/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-794052461/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1020480497740665/2251799813685248), (920747209342523/2251799813685248)), (9239357/562949953421312), by norm_num⟩
  | 1 => ⟨((-1114058041/4294967296), (-251294815/1073741824)), (43/4294967296), by norm_num⟩
  | 2 => ⟨((637647767/8589934592), (287664685/4294967296)), (13/4294967296), by norm_num⟩
  | 3 => ⟨((-973245941/68719476736), (-439064483/34359738368)), (21/34359738368), by norm_num⟩
  | 4 => ⟨((1114103715/549755813888), (1005220471/549755813888)), (51/549755813888), by norm_num⟩
  | 5 => ⟨((-1020278255/4398046511104), (-230141183/1099511627776)), (49/4398046511104), by norm_num⟩
  | 6 => ⟨((389314337/17592186044416), (351265987/17592186044416)), (39/35184372088832), by norm_num⟩
  | 7 => ⟨((-127331359/70368744177664), (-229774099/140737488355328)), (27/281474976710656), by norm_num⟩
  | 8 => ⟨((36440003/281474976710656), (131514639/1125899906842624)), (33/4503599627370496), by norm_num⟩
  | 9 => ⟨((-9269769/1125899906842624), (-535284401/72057594037927936)), (35/72057594037927936), by norm_num⟩
  | 10 => ⟨((1086605477/2305843009213693952), (490204841/1152921504606846976)), (67/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-226158139/9223372036854775808), (-816221283/36893488147419103232)), (29/18446744073709551616), by norm_num⟩
  | 12 => ⟨((345186641/295147905179352825856), (622901931/590295810358705651712)), (23/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-486332879/9444732965739290427392), (-877605485/18889465931478580854784)), (67/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((636251179/302231454903657293676544), (574069273/302231454903657293676544)), (23/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-12138929/151115727451828646838272), (-700964537/9671406556917033397649408)), (29/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((222332717/77371252455336267181195264), (802415055/309485009821345068724781056)), (69/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (956204091851/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781208736540459/633825300114114700748351602688), (567285198807/316912650057057350374175801344)), (11539/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946243254929733/19807040628566084398385987584), (19942722657/618970019642690137449562112)), (25965/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946216380916139/1237940039285380274899124224), (339009184071/618970019642690137449562112)), (13795/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887049301737911/77371252455336267181195264), (84747486389/9671406556917033397649408)), (27593/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776139581702097/4835703278458516698824704), (1271130533787/9671406556917033397649408)), (12935/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315293317789095/151115727451828646838272), (1112157456859/604462909807314587353088)), (22639/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891666187521785/75557863725914323419136), (903551285467/37778931862957161709568)), (36793/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300444349310165/4722366482869645213696), (1355192797719/4722366482869645213696)), (27599/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((3174689826493/1152921504606846976), (931586071095/295147905179352825856)), (37955/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914232115258829/36893488147419103232), (2328638258617/73786976294838206464)), (47453/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828267810587873/9223372036854775808), (2619268548111/9223372036854775808)), (26699/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599513316502995/1152921504606846976), (1309353356769/576460752303423488)), (53415/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149926739124523/18014398509481984), (572684088441/36028797018963968)), (46757/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498880383837567/36028797018963968), (1717420298951/18014398509481984)), (35087/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498299618627933/9007199254740992), (4291339109397/9007199254740992)), (10973/1125899906842624), by norm_num⟩
  | 2 => ⟨((561499156824797/1125899906842624), (1072005535503/562949953421312)), (21971/562949953421312), by norm_num⟩
  | 1 => ⟨((280386046256675/281474976710656), (6423742512341/1125899906842624)), (132077/1125899906842624), by norm_num⟩
  | 0 => ⟨((279293795843471/281474976710656), (400447892579/35184372088832)), (33145/140737488355328), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279293795843471/281474976710656), (400447892579/35184372088832)), (126438141406011537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1108372223537167/1125899906842624), (12715032875793/562949953421312)), (532247/1125899906842624), by norm_num⟩
  | 2 => ⟨((545271515790355/562949953421312), (12517088930589/281474976710656)), (1071967/1125899906842624), by norm_num⟩
  | 3 => ⟨((1054069954417707/1125899906842624), (96992096906447/1125899906842624)), (2171949/1125899906842624), by norm_num⟩
  | 4 => ⟨((244616771714909/281474976710656), (181608426368485/1125899906842624)), (2220489/562949953421312), by norm_num⟩
  | 5 => ⟨((821046537015797/1125899906842624), (157827411493669/562949953421312)), (1143945/140737488355328), by norm_num⟩
  | 6 => ⟨((1020480497740665/2251799813685248), (920747209342523/2251799813685248)), (9239357/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-794052461/67108864)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-652185243/562949953421312), (-342640987/1125899906842624)), (3329/1125899906842624), by norm_num⟩
  | 1 => ⟨((-262696769/562949953421312), (-1170463353/1125899906842624)), (9237/1125899906842624), by norm_num⟩
  | 2 => ⟨((541785631/2251799813685248), (-1057560919/2251799813685248)), (201/17592186044416), by norm_num⟩
  | 3 => ⟨((348920637/2251799813685248), (-281369321/9007199254740992)), (11969/1125899906842624), by norm_num⟩
  | 4 => ⟨((943774639/36028797018963968), (798186099/36028797018963968)), (268501/36028797018963968), by norm_num⟩
  | 5 => ⟨((-55540077/288230376151711744), (1648326599/288230376151711744)), (607723/144115188075855872), by norm_num⟩
  | 6 => ⟨((-703591545/1152921504606846976), (518421841/1152921504606846976)), (582265/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1445155241/18446744073709551616), (-48643963/2305843009213693952)), (15821641/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-425199121/147573952589676412928), (-474052099/73786976294838206464)), (25554787/73786976294838206464), by norm_num⟩
  | 9 => ⟨((242908943/1180591620717411303424), (-524514933/1180591620717411303424)), (359974165/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((464973915/18889465931478580854784), (-89846915/9444732965739290427392)), (827372869/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((5132005/4722366482869645213696), (2282831/18889465931478580854784)), (321784195/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((568409/9444732965739290427392), (109327/18889465931478580854784)), (148366361/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((82661/18889465931478580854784), (45761/18889465931478580854784)), (1161871997/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((1717/18889465931478580854784), (5463/18889465931478580854784)), (144509597/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((-27/4722366482869645213696), (189/18889465931478580854784)), (1154829079/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-1/9444732965739290427392), (3/18889465931478580854784)), (1154577585/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-50008013/8796093022208), (-178616553/17592186044416)), (24463/70368744177664), by norm_num⟩
  | 1 => ⟨((449408871/35184372088832), (-472364359/17592186044416)), (28533/35184372088832), by norm_num⟩
  | 2 => ⟨((306460189/17592186044416), (337860889/70368744177664)), (20507/17592186044416), by norm_num⟩
  | 3 => ⟨((-77632199/140737488355328), (313814525/70368744177664)), (377649/281474976710656), by norm_num⟩
  | 4 => ⟨((-453097827/1125899906842624), (205028951/2251799813685248)), (1518499/1125899906842624), by norm_num⟩
  | 5 => ⟨((-655048969/18014398509481984), (844920699/18014398509481984)), (22276723/18014398509481984), by norm_num⟩
  | 6 => ⟨((-298254595/18014398509481984), (-165922403/36028797018963968)), (4898751/4503599627370496), by norm_num⟩
  | 7 => ⟨((111273749/576460752303423488), (-527818197/288230376151711744)), (553553975/576460752303423488), by norm_num⟩
  | 8 => ⟨((79900267/1152921504606846976), (-4869979/288230376151711744)), (504325229/576460752303423488), by norm_num⟩
  | 9 => ⟨((1459697/576460752303423488), (-5855369/1152921504606846976)), (1906680671/2305843009213693952), by norm_num⟩
  | 10 => ⟨((814357/1152921504606846976), (46343/576460752303423488)), (115791729/144115188075855872), by norm_num⟩
  | 11 => ⟨((7765/1152921504606846976), (24355/1152921504606846976)), (228653591/288230376151711744), by norm_num⟩
  | 12 => ⟨((3533/2305843009213693952), (1337/2305843009213693952)), (455011999/576460752303423488), by norm_num⟩
  | 13 => ⟨((67/2305843009213693952), (331/2305843009213693952)), (1816765063/2305843009213693952), by norm_num⟩
  | 14 => ⟨((3/2305843009213693952), (1/144115188075855872)), (1815683837/2305843009213693952), by norm_num⟩
  | 15 => ⟨((1/2305843009213693952), (1/576460752303423488)), (1815353543/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-1/2305843009213693952), (1/2305843009213693952)), (1815259425/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6401025885/1125899906842624), (-2857864859/281474976710656)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((14381083695/1125899906842624), (-944728715/35184372088832)), (1/536870912), by norm_num⟩
  | 2 => ⟨((19613451693/1125899906842624), (2702886957/562949953421312)), (1/268435456), by norm_num⟩
  | 3 => ⟨((-621057211/1125899906842624), (2510516133/562949953421312)), (1/268435456), by norm_num⟩
  | 4 => ⟨((-453097961/1125899906842624), (102514653/1125899906842624)), (1/268435456), by norm_num⟩
  | 5 => ⟨((-40940527/1125899906842624), (26403733/562949953421312)), (1/268435456), by norm_num⟩
  | 6 => ⟨((-9320463/562949953421312), (-5185025/1125899906842624)), (1/268435456), by norm_num⟩
  | 7 => ⟨((54331/281474976710656), (-1030907/562949953421312)), (1/268435456), by norm_num⟩
  | 8 => ⟨((4877/70368744177664), (-19019/1125899906842624)), (1/268435456), by norm_num⟩
  | 9 => ⟨((2851/1125899906842624), (-715/140737488355328)), (1/268435456), by norm_num⟩
  | 10 => ⟨((199/281474976710656), (91/1125899906842624)), (1/268435456), by norm_num⟩
  | 11 => ⟨((7/1125899906842624), (3/140737488355328)), (1/268435456), by norm_num⟩
  | 12 => ⟨((1/562949953421312), (1/1125899906842624)), (1/268435456), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨15,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨15,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(52657/1073741824)) (L:=(214656285920253/18446744073709551616)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile015
