/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile008Gamma
import XiBand97.Tile008Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile008
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1593453127/140737488355328), (-18224117/35184372088832)), (1949/140737488355328), by norm_num⟩
  | 1 => ⟨((455206419/35184372088832), (544868721/70368744177664)), (2009/70368744177664), by norm_num⟩
  | 2 => ⟨((610665811/140737488355328), (312860755/35184372088832)), (1073/35184372088832), by norm_num⟩
  | 3 => ⟨((-68785555/140737488355328), (149205147/35184372088832)), (6287/281474976710656), by norm_num⟩
  | 4 => ⟨((-119502453/140737488355328), (149855327/140737488355328)), (1763/140737488355328), by norm_num⟩
  | 5 => ⟨((-1449248653/4503599627370496), (530951823/4503599627370496)), (25749/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1255870955/18014398509481984), (-57558033/4503599627370496)), (9989/4503599627370496), by norm_num⟩
  | 7 => ⟨((-684635529/72057594037927936), (-287009415/36028797018963968)), (55011/72057594037927936), by norm_num⟩
  | 8 => ⟨((-395820293/576460752303423488), (-1005908819/576460752303423488)), (145339/576460752303423488), by norm_num⟩
  | 9 => ⟨((118263219/4611686018427387904), (-572366395/2305843009213693952)), (55195/576460752303423488), by norm_num⟩
  | 10 => ⟨((290048561/18446744073709551616), (-927867243/36893488147419103232)), (491525/9223372036854775808), by norm_num⟩
  | 11 => ⟨((49250521/18446744073709551616), (-515478679/295147905179352825856)), (12662875/295147905179352825856), by norm_num⟩
  | 12 => ⟨((1462400313/4722366482869645213696), (-250371679/4722366482869645213696)), (191662077/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((1055290659/37778931862957161709568), (116950343/18889465931478580854784)), (1515315093/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((38247251/18889465931478580854784), (50717145/37778931862957161709568)), (755944109/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((543341/4722366482869645213696), (5882699/37778931862957161709568)), (1511278189/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((164651/37778931862957161709568), (524759/37778931862957161709568)), (755588091/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile008Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((14120435/2097152), (1157763821/33554432)), (3493/16777216), by norm_num⟩
  | 1 => ⟨((-19714055/4194304), (-1004687519/67108864)), (14619/67108864), by norm_num⟩
  | 2 => ⟨((152038351/67108864), (251292515/33554432)), (29963/134217728), by norm_num⟩
  | 3 => ⟨((-66356799/134217728), (-89213715/33554432)), (118923/536870912), by norm_num⟩
  | 4 => ⟨((853499/33554432), (24657597/33554432)), (462665/2147483648), by norm_num⟩
  | 5 => ⟨((207371/8388608), (-22057589/134217728)), (1796195/8589934592), by norm_num⟩
  | 6 => ⟨((-6145947/536870912), (8113137/268435456)), (1757059/8589934592), by norm_num⟩
  | 7 => ⟨((1675081/536870912), (-4914141/1073741824)), (27760431/137438953472), by norm_num⟩
  | 8 => ⟨((-172321/268435456), (150219/268435456)), (110371515/549755813888), by norm_num⟩
  | 9 => ⟨((14421/134217728), (-220537/4294967296)), (1761532845/8796093022208), by norm_num⟩
  | 10 => ⟨((-129797/8589934592), (42315/17179869184)), (1759944621/8796093022208), by norm_num⟩
  | 11 => ⟨((124337/68719476736), (16713/68719476736)), (1759425965/8796093022208), by norm_num⟩
  | 12 => ⟨((-791/4294967296), (-23715/274877906944)), (1759273293/8796093022208), by norm_num⟩
  | 13 => ⟨((8565/549755813888), (3991/274877906944)), (1759231989/8796093022208), by norm_num⟩
  | 14 => ⟨((-4463/4398046511104), (-8121/4398046511104)), (1759221657/8796093022208), by norm_num⟩
  | 15 => ⟨((39/1099511627776), (855/4398046511104)), (879609629/4398046511104), by norm_num⟩
  | 16 => ⟨((11/4398046511104), (-153/8796093022208)), (1759218737/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile008Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11709/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11709/640))
  have he : value ((69/80), (11709/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-351368439/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-687685125377237/2251799813685248), (1190060938824605/2251799813685248)), (7499665/281474976710656), by norm_num⟩
  | 1 => ⟨((375372751/2147483648), (-649594461/2147483648)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((-429700407/8589934592), (743610193/8589934592)), (41/8589934592), by norm_num⟩
  | 3 => ⟨((655854531/68719476736), (-567488541/34359738368)), (65/68719476736), by norm_num⟩
  | 4 => ⟨((-750776283/549755813888), (649621093/274877906944)), (77/549755813888), by norm_num⟩
  | 5 => ⟨((687548839/4398046511104), (-18591017/68719476736)), (73/4398046511104), by norm_num⟩
  | 6 => ⟨((-32794071/2199023255552), (227004723/8796093022208)), (29/17592186044416), by norm_num⟩
  | 7 => ⟨((171613043/140737488355328), (-148490909/70368744177664)), (39/281474976710656), by norm_num⟩
  | 8 => ⟨((-785802317/9007199254740992), (1359855851/9007199254740992)), (23/2251799813685248), by norm_num⟩
  | 9 => ⟨((99947933/18014398509481984), (-345926141/36028797018963968)), (49/72057594037927936), by norm_num⟩
  | 10 => ⟨((-366122835/1152921504606846976), (633587187/1152921504606846976)), (93/2305843009213693952), by norm_num⟩
  | 11 => ⟨((609617093/36893488147419103232), (-1054961729/36893488147419103232)), (5/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-232615635/295147905179352825856), (100637185/73786976294838206464)), (63/590295810358705651712), by norm_num⟩
  | 13 => ⟨((655463555/18889465931478580854784), (-141787561/2361183241434822606848)), (91/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-428759269/302231454903657293676544), (741981525/302231454903657293676544)), (61/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((130883613/2417851639229258349412352), (-226498247/2417851639229258349412352)), (77/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-299652767/154742504910672534362390528), (518558625/154742504910672534362390528)), (45/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (2728678474599/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781203840007251/633825300114114700748351602688), (3237674726839/633825300114114700748351602688)), (23131/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892480702308057/39614081257132168796771975168), (910552529041/9903520314283042199192993792)), (13013/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892426228795733/2475880078570760549798248448), (241853238311/154742504910672534362390528)), (27659/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887045831326033/77371252455336267181195264), (3869430729275/154742504910672534362390528)), (13833/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552272223174131/9671406556917033397649408), (1813678159723/4835703278458516698824704)), (3243/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315291691330411/151115727451828646838272), (1586850845761/302231454903657293676544)), (5677/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945827401786613/37778931862957161709568), (1289206062245/18889465931478580854784)), (36913/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300435101035657/4722366482869645213696), (3867232102285/4722366482869645213696)), (27697/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625427320824833/590295810358705651712), (5316816360443/590295810358705651712)), (38101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828445162169355/73786976294838206464), (415317380807/4611686018427387904)), (47655/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828243980207761/9223372036854775808), (1868603999121/2305843009213693952)), (26825/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799743257140071/576460752303423488), (7472793250649/1152921504606846976)), (26849/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199387119472467/144115188075855872), (6536866206341/144115188075855872)), (47041/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498833514759689/36028797018963968), (2450409447961/9007199254740992)), (35335/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498229354227247/9007199254740992), (6122813340169/4503599627370496)), (44265/4503599627370496), by norm_num⟩
  | 2 => ⟨((35090954745759/70368744177664), (764748129521/140737488355328)), (88817/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121368867951311/1125899906842624), (18329723570157/1125899906842624)), (66973/562949953421312), by norm_num⟩
  | 0 => ⟨((1116650267057183/1125899906842624), (36561982257767/1125899906842624)), (270775/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116650267057183/1125899906842624), (36561982257767/1125899906842624)), (1032924656394576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((276572329565519/281474976710656), (72523226983413/1125899906842624)), (8667/17592186044416), by norm_num⟩
  | 2 => ⟨((1082348821456131/1125899906842624), (35630019529285/281474976710656)), (1161513/1125899906842624), by norm_num⟩
  | 3 => ⟨((127805210707983/140737488355328), (274014479700075/1125899906842624)), (1263613/562949953421312), by norm_num⟩
  | 4 => ⟨((861802243344077/1125899906842624), (124417732348215/281474976710656)), (1455031/281474976710656), by norm_num⟩
  | 5 => ⟨((439672078895841/1125899906842624), (95233581775633/140737488355328)), (7027537/562949953421312), by norm_num⟩
  | 6 => ⟨((-687685125377237/2251799813685248), (1190060938824605/2251799813685248)), (7499665/281474976710656), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-351368439/33554432)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-28006563/8796093022208), (108048911/17592186044416)), (1671/140737488355328), by norm_num⟩
  | 1 => ⟨((-1751015321/281474976710656), (269495957/281474976710656)), (4385/140737488355328), by norm_num⟩
  | 2 => ⟨((-546725385/281474976710656), (-556325785/281474976710656)), (5867/140737488355328), by norm_num⟩
  | 3 => ⟨((9733487/70368744177664), (-433969319/562949953421312)), (85315/2251799813685248), by norm_num⟩
  | 4 => ⟨((1299016721/9007199254740992), (-597567361/9007199254740992)), (236693/9007199254740992), by norm_num⟩
  | 5 => ⟨((753513093/36028797018963968), (450840375/36028797018963968)), (66585/4503599627370496), by norm_num⟩
  | 6 => ⟨((44385709/288230376151711744), (418447119/144115188075855872)), (4048491/576460752303423488), by norm_num⟩
  | 7 => ⟨((-125131315/576460752303423488), (741972231/4611686018427387904)), (6702525/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1313702675/73786976294838206464), (-480050521/73786976294838206464)), (40054659/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-267513099/1180591620717411303424), (-1011194163/1180591620717411303424)), (115182455/295147905179352825856), by norm_num⟩
  | 10 => ⟨((10495687/9444732965739290427392), (-120956285/9444732965739290427392)), (1471782585/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-10996369/4722366482869645213696), (-34371275/18889465931478580854784)), (802271081/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((352705/9444732965739290427392), (-2954285/9444732965739290427392)), (309201195/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((335753/18889465931478580854784), (-83293/18889465931478580854784)), (572089831/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((2189/18889465931478580854784), (11491/18889465931478580854784)), (70163097/1180591620717411303424), by norm_num⟩
  | 15 => ⟨((-459/18889465931478580854784), (-531/18889465931478580854784)), (558966999/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((15/4722366482869645213696), (-35/18889465931478580854784)), (279246307/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-513158721/2199023255552), (-75323151/1099511627776)), (5347/2199023255552), by norm_num⟩
  | 1 => ⟨((281419949/8796093022208), (-1665969189/8796093022208)), (44373/8796093022208), by norm_num⟩
  | 2 => ⟨((800101283/17592186044416), (-57180795/35184372088832)), (121551/17592186044416), by norm_num⟩
  | 3 => ⟨((522096311/140737488355328), (-146297569/140737488355328)), (2092785/281474976710656), by norm_num⟩
  | 4 => ⟨((351476285/140737488355328), (66192021/70368744177664)), (3973815/562949953421312), by norm_num⟩
  | 5 => ⟨((-228039901/2251799813685248), (1165295283/2251799813685248)), (14127969/2251799813685248), by norm_num⟩
  | 6 => ⟨((-848953055/18014398509481984), (-74859997/36028797018963968)), (198287463/36028797018963968), by norm_num⟩
  | 7 => ⟨((-96193453/144115188075855872), (-127375683/144115188075855872)), (712702871/144115188075855872), by norm_num⟩
  | 8 => ⟨((-66138733/288230376151711744), (-2432855/36028797018963968)), (1329806771/288230376151711744), by norm_num⟩
  | 9 => ⟨((51727/72057594037927936), (-6064335/288230376151711744)), (320254095/72057594037927936), by norm_num⟩
  | 10 => ⟨((30881/144115188075855872), (-81083/288230376151711744)), (314760031/72057594037927936), by norm_num⟩
  | 11 => ⟨((4941/288230376151711744), (-2601/36028797018963968)), (625072327/144115188075855872), by norm_num⟩
  | 12 => ⟨((69/18014398509481984), (-7/288230376151711744)), (1246866463/288230376151711744), by norm_num⟩
  | 13 => ⟨((-1/144115188075855872), (-29/288230376151711744)), (1245755169/288230376151711744), by norm_num⟩
  | 14 => ⟨(0, (-1/144115188075855872)), (311351493/72057594037927936), by norm_num⟩
  | 15 => ⟨(0, (-1/288230376151711744)), (622651799/144115188075855872), by norm_num⟩
  | 16 => ⟨(0, 0), (311318863/72057594037927936), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-262737259449/1125899906842624), (-19282727829/281474976710656)), (1/268435456), by norm_num⟩
  | 1 => ⟨((18010879567/562949953421312), (-213244052813/1125899906842624)), (1/134217728), by norm_num⟩
  | 2 => ⟨((12801620175/281474976710656), (-914890939/562949953421312)), (1/67108864), by norm_num⟩
  | 3 => ⟨((4176769741/1125899906842624), (-73148891/70368744177664)), (1/33554432), by norm_num⟩
  | 4 => ⟨((2811810831/1125899906842624), (1059073219/1125899906842624)), (1/33554432), by norm_num⟩
  | 5 => ⟨((-14252537/140737488355328), (291323631/562949953421312)), (1/33554432), by norm_num⟩
  | 6 => ⟨((-53059289/1125899906842624), (-2339179/1125899906842624)), (1/33554432), by norm_num⟩
  | 7 => ⟨((-187909/281474976710656), (-497541/562949953421312)), (1/33554432), by norm_num⟩
  | 8 => ⟨((-129175/562949953421312), (-76017/1125899906842624)), (1/33554432), by norm_num⟩
  | 9 => ⟨((393/562949953421312), (-23689/1125899906842624)), (1/33554432), by norm_num⟩
  | 10 => ⟨((121/562949953421312), (-161/562949953421312)), (1/33554432), by norm_num⟩
  | 11 => ⟨((19/1125899906842624), (-81/1125899906842624)), (1/33554432), by norm_num⟩
  | 12 => ⟨((5/1125899906842624), 0), (1/33554432), by norm_num⟩
  | 13 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | 14 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | 15 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | 16 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨8,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨8,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(326799/1048576)) (K:=(486947/1073741824)) (L:=(143563079611546111/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile008
