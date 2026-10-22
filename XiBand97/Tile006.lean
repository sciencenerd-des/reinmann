/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile006Gamma
import XiBand97.Tile006Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile006
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((268958833/35184372088832), (-216153499/8796093022208)), (619/17592186044416), by norm_num⟩
  | 1 => ⟨((461108665/17592186044416), (-367612163/17592186044416)), (1369/17592186044416), by norm_num⟩
  | 2 => ⟨((1507643315/70368744177664), (-128465431/70368744177664)), (3067/35184372088832), by norm_num⟩
  | 3 => ⟨((280522863/35184372088832), (603383279/140737488355328)), (4607/70368744177664), by norm_num⟩
  | 4 => ⟨((386931221/281474976710656), (690824989/281474976710656)), (2607/70368744177664), by norm_num⟩
  | 5 => ⟨((-16499517/562949953421312), (387073921/562949953421312)), (37987/2251799813685248), by norm_num⟩
  | 6 => ⟨((-681388605/9007199254740992), (520474675/4503599627370496)), (7281/1125899906842624), by norm_num⟩
  | 7 => ⟨((-375484597/18014398509481984), (384416113/36028797018963968)), (77903/36028797018963968), by norm_num⟩
  | 8 => ⟨((-1976014805/576460752303423488), (-11501587/144115188075855872)), (379833/576460752303423488), by norm_num⟩
  | 9 => ⟨((-896163559/2305843009213693952), (-242153111/1152921504606846976)), (116419/576460752303423488), by norm_num⟩
  | 10 => ⟨((-276232683/9223372036854775808), (-759111189/18446744073709551616)), (1448041/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-81570167/73786976294838206464), (-1535547143/295147905179352825856)), (14284061/295147905179352825856), by norm_num⟩
  | 12 => ⟨((221704961/2361183241434822606848), (-592392111/1180591620717411303424)), (49223569/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((28335261/1180591620717411303424), (-729208463/18889465931478580854784)), (761592319/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((112624437/37778931862957161709568), (-44039621/18889465931478580854784)), (756637643/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((10587319/37778931862957161709568), (-3637559/37778931862957161709568)), (1511508555/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((414099/18889465931478580854784), (-12091/37778931862957161709568)), (1511212391/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile006Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-156794713/16777216), (1031907805/33554432)), (6963/33554432), by norm_num⟩
  | 1 => ⟨((172106539/16777216), (-92530949/8388608)), (7253/33554432), by norm_num⟩
  | 2 => ⟨((-332024689/67108864), (610588697/134217728)), (29641/134217728), by norm_num⟩
  | 3 => ⟨((247843667/134217728), (-20460435/16777216)), (117611/536870912), by norm_num⟩
  | 4 => ⟨((-71204851/134217728), (3688713/16777216)), (458585/2147483648), by norm_num⟩
  | 5 => ⟨((1028067/8388608), (-5770577/268435456)), (1785859/8589934592), by norm_num⟩
  | 6 => ⟨((-6241669/268435456), (-879211/536870912)), (1751555/8589934592), by norm_num⟩
  | 7 => ⟨((3919837/1073741824), (1364951/1073741824)), (27718703/137438953472), by norm_num⟩
  | 8 => ⟨((-1010981/2147483648), (-358725/1073741824)), (110303675/549755813888), by norm_num⟩
  | 9 => ⟨((412643/8589934592), (534867/8589934592)), (1761144749/8796093022208), by norm_num⟩
  | 10 => ⟨((-57933/17179869184), (-159443/17179869184)), (1759817645/8796093022208), by norm_num⟩
  | 11 => ⟨((2345/68719476736), (39571/34359738368)), (1759388589/8796093022208), by norm_num⟩
  | 12 => ⟨((10163/274877906944), (-33055/274877906944)), (1759263053/8796093022208), by norm_num⟩
  | 13 => ⟨((-2107/274877906944), (11451/1099511627776)), (1759229389/8796093022208), by norm_num⟩
  | 14 => ⟨((2297/2199023255552), (-3091/4398046511104)), (1759221043/8796093022208), by norm_num⟩
  | 15 => ⟨((-499/4398046511104), (61/2199023255552)), (1759219123/8796093022208), by norm_num⟩
  | 16 => ⟨((91/8796093022208), (11/8796093022208)), (1759218709/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile006Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10993/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10993/640))
  have he : value ((69/80), (10993/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-659764839/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1262469477105865/2251799813685248), (2122811262071/8796093022208)), (14879149/562949953421312), by norm_num⟩
  | 1 => ⟨((689118643/2147483648), (-296636413/2147483648)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((-394427353/4294967296), (339568567/8589934592)), (41/8589934592), by norm_num⟩
  | 3 => ⟨((1204034077/68719476736), (-129571429/17179869184)), (65/68719476736), by norm_num⟩
  | 4 => ⟨((-43071681/17179869184), (593297149/549755813888)), (77/549755813888), by norm_num⟩
  | 5 => ⟨((1262219277/4398046511104), (-271665991/2199023255552)), (73/4398046511104), by norm_num⟩
  | 6 => ⟨((-963266753/35184372088832), (103661393/8796093022208)), (57/35184372088832), by norm_num⟩
  | 7 => ⟨((1260205989/562949953421312), (-542465347/562949953421312)), (77/562949953421312), by norm_num⟩
  | 8 => ⟨((-721297729/4503599627370496), (620976295/9007199254740992)), (91/9007199254740992), by norm_num⟩
  | 9 => ⟨((1467895231/144115188075855872), (-78983347/18014398509481984)), (3/4503599627370496), by norm_num⟩
  | 10 => ⟨((-1344274833/2305843009213693952), (289326713/1152921504606846976)), (45/1152921504606846976), by norm_num⟩
  | 11 => ⟨((559575119/18446744073709551616), (-481746815/36893488147419103232)), (77/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-427041575/295147905179352825856), (367646651/590295810358705651712)), (61/590295810358705651712), by norm_num⟩
  | 13 => ⟨((300829079/4722366482869645213696), (-517976749/18889465931478580854784)), (89/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-787126943/302231454903657293676544), (338824837/302231454903657293676544)), (15/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((961117585/9671406556917033397649408), (-413720445/9671406556917033397649408)), (75/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-137527503/38685626227668133590597632), (236799079/154742504910672534362390528)), (11/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (3562784065339/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890599952897745/316912650057057350374175801344), (4227370880413/633825300114114700748351602688)), (23155/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236559504515197/4951760157141521099596496896), (2377777303467/19807040628566084398385987584)), (26055/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892420979730611/2475880078570760549798248448), (1263129748633/618970019642690137449562112)), (27691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774086085947455/154742504910672534362390528), (2526114386889/77371252455336267181195264)), (6925/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((388066661737597/2417851639229258349412352), (4736155904113/9671406556917033397649408)), (12989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630580769061583/302231454903657293676544), (2071913803381/302231454903657293676544)), (5685/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((59113926781227/2361183241434822606848), (6733140337825/75557863725914323419136)), (18485/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300427670404585/4722366482869645213696), (5049347665133/4722366482869645213696)), (13871/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406354044140105/147573952589676412928), (867753407665/73786976294838206464)), (19085/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828429841542573/73786976294838206464), (8676293752219/73786976294838206464)), (47749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828224833535093/9223372036854775808), (9759122333903/9223372036854775808)), (53769/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599464979934899/1152921504606846976), (304905722749/36028797018963968)), (53833/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199365592217815/144115188075855872), (4267474043725/72057594037927936)), (47175/144115188075855872), by norm_num⟩
  | 4 => ⟨((187349482256941/4503599627370496), (6398791993905/18014398509481984)), (70905/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498172901247989/9007199254740992), (1998560264921/1125899906842624)), (44441/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122840041986179/2251799813685248), (3993918295107/562949953421312)), (44629/1125899906842624), by norm_num⟩
  | 1 => ⟨((280307004519105/281474976710656), (23931270327763/1125899906842624)), (33707/281474976710656), by norm_num⟩
  | 0 => ⟨((139528571591181/140737488355328), (23866141748691/562949953421312)), (273431/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((139528571591181/140737488355328), (23866141748691/562949953421312)), (1043056492332076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((276154178566689/281474976710656), (94644538750899/1125899906842624)), (565349/1125899906842624), by norm_num⟩
  | 2 => ⟨((134472488335881/140737488355328), (23213861814655/140737488355328)), (1204373/1125899906842624), by norm_num⟩
  | 3 => ⟨((498629524909511/562949953421312), (88721940360925/281474976710656)), (1349415/562949953421312), by norm_num⟩
  | 4 => ⟨((771454268665133/1125899906842624), (314339693625371/562949953421312)), (1620577/281474976710656), by norm_num⟩
  | 5 => ⟨((177550344815535/1125899906842624), (861528443103703/1125899906842624)), (32244777/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1262469477105865/2251799813685248), (2122811262071/8796093022208)), (14879149/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-659764839/67108864)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((57870703/35184372088832), (549654403/35184372088832)), (2047/70368744177664), by norm_num⟩
  | 1 => ⟨((-745455151/70368744177664), (160081945/17592186044416)), (5653/70368744177664), by norm_num⟩
  | 2 => ⟨((-813083347/140737488355328), (-442786687/281474976710656)), (31461/281474976710656), by norm_num⟩
  | 3 => ⟨((-18089717/35184372088832), (-438499605/281474976710656)), (58869/562949953421312), by norm_num⟩
  | 4 => ⟨((906573693/4503599627370496), (-1122035103/4503599627370496)), (10379/140737488355328), by norm_num⟩
  | 5 => ⟨((1677938837/36028797018963968), (204895031/36028797018963968)), (188165/4503599627370496), by norm_num⟩
  | 6 => ⟨((308043587/144115188075855872), (173051129/36028797018963968)), (1429183/72057594037927936), by norm_num⟩
  | 7 => ⟨((-610211889/2305843009213693952), (825576931/2305843009213693952)), (1172231/144115188075855872), by norm_num⟩
  | 8 => ⟨((-240280463/9223372036854775808), (-79831337/18446744073709551616)), (6824523/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-53668099/590295810358705651712), (-435133317/590295810358705651712)), (1168436455/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-53415479/2361183241434822606848), (235704961/4722366482869645213696)), (1550406847/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-10201901/1180591620717411303424), (-18127845/9444732965739290427392)), (1219428511/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-102501/9444732965739290427392), (-6260067/9444732965739290427392)), (704546847/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((613291/18889465931478580854784), (7945/9444732965739290427392)), (575216419/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-20477/18889465931478580854784), (13457/9444732965739290427392)), (1090313039/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-1521/18889465931478580854784), (-321/2361183241434822606848)), (538647793/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((97/9444732965739290427392), (-83/18889465931478580854784)), (134331851/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1090281287/2199023255552), (-209824329/2199023255552)), (5223/1099511627776), by norm_num⟩
  | 1 => ⟨((18372827/2199023255552), (-1181817037/4398046511104)), (3205/274877906944), by norm_num⟩
  | 2 => ⟨((523033457/35184372088832), (-794404261/35184372088832)), (565197/35184372088832), by norm_num⟩
  | 3 => ⟨((161874991/17592186044416), (-704901235/35184372088832)), (618381/35184372088832), by norm_num⟩
  | 4 => ⟨((885288029/140737488355328), (211949103/140737488355328)), (1173691/70368744177664), by norm_num⟩
  | 5 => ⟨((-208021081/2251799813685248), (470000939/562949953421312)), (32914495/2251799813685248), by norm_num⟩
  | 6 => ⟨((-392040825/9007199254740992), (197862773/36028797018963968)), (452266123/36028797018963968), by norm_num⟩
  | 7 => ⟨((-44941377/36028797018963968), (152146729/72057594037927936)), (1592267331/144115188075855872), by norm_num⟩
  | 8 => ⟨((-62515151/144115188075855872), (-7916279/144115188075855872)), (731893837/72057594037927936), by norm_num⟩
  | 9 => ⟨((-253451/72057594037927936), (-2501209/144115188075855872)), (1398762839/144115188075855872), by norm_num⟩
  | 10 => ⟨((-34177/36028797018963968), (-32129/72057594037927936)), (85615621/9007199254740992), by norm_num⟩
  | 11 => ⟨((413/72057594037927936), (-15817/144115188075855872)), (1358341415/144115188075855872), by norm_num⟩
  | 12 => ⟨((215/144115188075855872), (-95/72057594037927936)), (1354183425/144115188075855872), by norm_num⟩
  | 13 => ⟨((5/144115188075855872), (-5/72057594037927936)), (1352805337/144115188075855872), by norm_num⟩
  | 14 => ⟨((-1/36028797018963968), (1/72057594037927936)), (1352382761/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1/144115188075855872), (1/144115188075855872)), (338065505/36028797018963968), by norm_num⟩
  | 16 => ⟨(0, 0), (676114843/72057594037927936), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-139556002919/281474976710656), (-53715021221/562949953421312)), (1/134217728), by norm_num⟩
  | 1 => ⟨((4703439755/562949953421312), (-302545149669/1125899906842624)), (1/33554432), by norm_num⟩
  | 2 => ⟨((8368533017/562949953421312), (-25420942655/1125899906842624)), (1/33554432), by norm_num⟩
  | 3 => ⟨((5180000873/562949953421312), (-22556834945/1125899906842624)), (1/16777216), by norm_num⟩
  | 4 => ⟨((3541150651/562949953421312), (1695590417/1125899906842624)), (1/16777216), by norm_num⟩
  | 5 => ⟨((-104009109/1125899906842624), (117500333/140737488355328)), (1/16777216), by norm_num⟩
  | 6 => ⟨((-24502931/562949953421312), (6183051/1125899906842624)), (1/16777216), by norm_num⟩
  | 7 => ⟨((-1404163/1125899906842624), (594321/281474976710656)), (1/16777216), by norm_num⟩
  | 8 => ⟨((-488483/1125899906842624), (-483/8796093022208)), (1/16777216), by norm_num⟩
  | 9 => ⟨((-3937/1125899906842624), (-4887/281474976710656)), (1/16777216), by norm_num⟩
  | 10 => ⟨((-1077/1125899906842624), (-497/1125899906842624)), (1/16777216), by norm_num⟩
  | 11 => ⟨((7/1125899906842624), (-127/1125899906842624)), (1/16777216), by norm_num⟩
  | 12 => ⟨((1/562949953421312), (-1/562949953421312)), (1/16777216), by norm_num⟩
  | 13 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 14 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 15 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 16 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨6,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨6,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(326799/1048576)) (K:=(137139/268435456)) (L:=(149020335713826747/295147905179352825856)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile006
