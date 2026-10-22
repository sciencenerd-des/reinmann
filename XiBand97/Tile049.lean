/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import XiBand97.Tile049Gamma
import XiBand97.Tile049Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile049
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨49,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1462664565/2305843009213693952), (5717995651/2305843009213693952)), (127605/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-1170039953/1152921504606846976), (4403609043/1152921504606846976)), (10881/144115188075855872), by norm_num⟩
  | 2 => ⟨((-1211875611/576460752303423488), (2521035355/1152921504606846976)), (93485/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-1697780523/1152921504606846976), (265801411/576460752303423488)), (165361/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-5297955139/9223372036854775808), (-518949909/4611686018427387904)), (538471/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-2522082525/18446744073709551616), (-1030857541/9223372036854775808)), (895395/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-1265587777/73786976294838206464), (-6002487545/147573952589676412928)), (1598043/36893488147419103232), by norm_num⟩
  | 7 => ⟨((226234015/295147905179352825856), (-5532996017/590295810358705651712)), (24265247/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1086509835/1180591620717411303424), (-3496291137/2361183241434822606848)), (95214187/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((4610592821/18889465931478580854784), (-2806192551/18889465931478580854784)), (189296601/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((3156377935/75557863725914323419136), (-67815669/18889465931478580854784)), (377979947/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((392360263/75557863725914323419136), (151263891/75557863725914323419136)), (3022645209/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((34967333/75557863725914323419136), (74048153/151115727451828646838272)), (6044761329/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((3554357/151115727451828646838272), (336419/4722366482869645213696)), (3022326827/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-128899/151115727451828646838272), (1160017/151115727451828646838272)), (6044633359/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-7081/18889465931478580854784), (48169/75557863725914323419136)), (6044629793/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((-4049/75557863725914323419136), (2935/75557863725914323419136)), (3022314603/75557863725914323419136), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile049Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((221101971/8388608), (1085372383/67108864)), (13839/67108864), by norm_num⟩
  | 1 => ⟨((-97705007/4194304), (2788924237/134217728)), (1797/8388608), by norm_num⟩
  | 2 => ⟨((1736227273/134217728), (-2225389759/134217728)), (58541/268435456), by norm_num⟩
  | 3 => ⟨((-1466072995/268435456), (4710569307/536870912)), (116087/536870912), by norm_num⟩
  | 4 => ⟨((270141007/134217728), (-1844074113/536870912)), (113489/536870912), by norm_num⟩
  | 5 => ⟨((-176217935/268435456), (1137140953/1073741824)), (443601/2147483648), by norm_num⟩
  | 6 => ⟨((50539495/268435456), (-35909585/134217728)), (1745683/8589934592), by norm_num⟩
  | 7 => ⟨((-50847039/1073741824), (244017157/4294967296)), (1729809/8589934592), by norm_num⟩
  | 8 => ⟨((90046855/8589934592), (-88479609/8589934592)), (27559375/137438953472), by norm_num⟩
  | 9 => ⟨((-70651927/34359738368), (27576557/17179869184)), (110048379/549755813888), by norm_num⟩
  | 10 => ⟨((24746335/68719476736), (-7359607/34359738368)), (1759698221/8796093022208), by norm_num⟩
  | 11 => ⟨((-7793201/137438953472), (1644321/68719476736)), (3518707673/17592186044416), by norm_num⟩
  | 12 => ⟨((8879443/1099511627776), (-1143221/549755813888)), (3518507609/17592186044416), by norm_num⟩
  | 13 => ⟨((-4596543/4398046511104), (440405/4398046511104)), (3518454209/17592186044416), by norm_num⟩
  | 14 => ⟨((135547/1099511627776), (150993/17592186044416)), (3518441039/17592186044416), by norm_num⟩
  | 15 => ⟨((-233441/17592186044416), (-115479/35184372088832)), (7036876037/35184372088832), by norm_num⟩
  | 16 => ⟨((45799/35184372088832), (20609/35184372088832)), (1759218685/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile049Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15131/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15131/512))
  have he : value ((69/80), (15131/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-66258563/134217728), (-4540572081/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-489086943258901/2251799813685248), (1284503729739545/2251799813685248)), (14668447/1125899906842624), by norm_num⟩
  | 1 => ⟨((2135743869/17179869184), (-5609168273/17179869184)), (131/17179869184), by norm_num⟩
  | 2 => ⟨((-611212459/17179869184), (1605245639/17179869184)), (77/34359738368), by norm_num⟩
  | 3 => ⟨((466448779/68719476736), (-612524219/34359738368)), (15/34359738368), by norm_num⟩
  | 4 => ⟨((-1067915715/1099511627776), (2804699117/1099511627776)), (35/549755813888), by norm_num⟩
  | 5 => ⟨((1955960055/17592186044416), (-160531145/549755813888)), (131/17592186044416), by norm_num⟩
  | 6 => ⟨((-1492697287/140737488355328), (1960157859/70368744177664)), (51/70368744177664), by norm_num⟩
  | 7 => ⟨((1952840223/2251799813685248), (-2564401465/1125899906842624)), (17/281474976710656), by norm_num⟩
  | 8 => ⟨((-2235474565/36028797018963968), (733886749/4503599627370496)), (79/18014398509481984), by norm_num⟩
  | 9 => ⟨((1137339797/288230376151711744), (-5974059337/576460752303423488)), (163/576460752303423488), by norm_num⟩
  | 10 => ⟨((-2083114969/9223372036854775808), (2735473705/4611686018427387904)), (19/1152921504606846976), by norm_num⟩
  | 11 => ⟨((867128713/73786976294838206464), (-2277366183/73786976294838206464)), (129/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-1323504203/2361183241434822606848), (3475958841/2361183241434822606848)), (101/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((1864682849/75557863725914323419136), (-4897272575/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-609873767/604462909807314587353088), (1601729793/604462909807314587353088)), (97/1208925819614629174706176), by norm_num⟩
  | 15 => ⟨((744683443/19342813113834066795298816), (-977892247/9671406556917033397649408)), (121/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-1704922785/1237940039285380274899124224), (4477689921/1237940039285380274899124224)), (141/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (2520041355307/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890602330491241/316912650057057350374175801344), (2990119313293/633825300114114700748351602688)), (11563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473120419007195/9903520314283042199192993792), (3363725127449/39614081257132168796771975168)), (6505/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892427324152115/2475880078570760549798248448), (3573776722981/2475880078570760549798248448)), (6913/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774092826379459/154742504910672534362390528), (1786786386597/77371252455336267181195264)), (13829/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388068346700403/2417851639229258349412352), (837501927861/2417851639229258349412352)), (1621/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630583928058101/302231454903657293676544), (366379988625/75557863725914323419136)), (11351/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118228544515699/4722366482869645213696), (2381266560203/37778931862957161709568)), (9225/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300436651637147/4722366482869645213696), (3571543790607/4722366482869645213696)), (13843/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625429646377975/590295810358705651712), (2455146916253/295147905179352825856)), (9521/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828448359237217/73786976294838206464), (6136998448599/73786976294838206464)), (2977/9223372036854775808), by norm_num⟩
  | 7 => ⟨((914123987845137/4611686018427387904), (6902927748053/9223372036854775808)), (26811/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599491008024815/1152921504606846976), (3450716046215/576460752303423488)), (26833/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599695805874433/72057594037927936), (3018534360133/72057594037927936)), (1469/9007199254740992), by norm_num⟩
  | 4 => ⟨((1498841372934737/36028797018963968), (9052229993421/36028797018963968)), (17653/18014398509481984), by norm_num⟩
  | 3 => ⟨((749120567429977/4503599627370496), (11309374778531/9007199254740992)), (44221/9007199254740992), by norm_num⟩
  | 2 => ⟨((140365658253085/281474976710656), (11300486116391/2251799813685248)), (22177/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121398261267913/1125899906842624), (2116054885057/140737488355328)), (66863/1125899906842624), by norm_num⟩
  | 0 => ⟨((558369135599535/562949953421312), (16883654112837/562949953421312)), (8441/70368744177664), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558369135599535/562949953421312), (16883654112837/562949953421312)), (32199859887576081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1106638456654601/1125899906842624), (33492537997213/562949953421312)), (17251/70368744177664), by norm_num⟩
  | 2 => ⟨((1083721266806579/1125899906842624), (131678243628675/1125899906842624)), (71929/140737488355328), by norm_num⟩
  | 3 => ⟨((513861231025691/562949953421312), (63372646240071/281474976710656)), (1242349/1125899906842624), by norm_num⟩
  | 4 => ⟨((55064618550507/70368744177664), (231386437194761/562949953421312)), (706863/281474976710656), by norm_num⟩
  | 5 => ⟨((499211333652513/1125899906842624), (724253703872953/1125899906842624)), (1687339/281474976710656), by norm_num⟩
  | 6 => ⟨((-489086943258901/2251799813685248), (1284503729739545/2251799813685248)), (14668447/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-4540572081/268435456)), (1/134217728), by norm_num⟩, -3, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-3579428701/2305843009213693952), (-815169199/4611686018427387904)), (12575/288230376151711744), by norm_num⟩
  | 1 => ⟨((-616734521/576460752303423488), (-1507243399/1152921504606846976)), (194851/2305843009213693952), by norm_num⟩
  | 2 => ⟨((350002751/4611686018427387904), (-2068161005/2305843009213693952)), (121221/1152921504606846976), by norm_num⟩
  | 3 => ⟨((4374435995/18446744073709551616), (-1910459629/9223372036854775808)), (1922367/18446744073709551616), by norm_num⟩
  | 4 => ⟨((5988938905/73786976294838206464), (71915441/18446744073709551616)), (6704481/73786976294838206464), by norm_num⟩
  | 5 => ⟨((419046269/36893488147419103232), (3526369649/295147905179352825856)), (22461209/295147905179352825856), by norm_num⟩
  | 6 => ⟨((2738545/590295810358705651712), (1614537739/590295810358705651712)), (154939213/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-2457194373/9444732965739290427392), (2631682233/9444732965739290427392)), (282838703/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-1714133279/37778931862957161709568), (254689005/75557863725914323419136)), (1082631355/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-281122993/75557863725914323419136), (-437997235/151115727451828646838272)), (4255304787/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-5984265/75557863725914323419136), (-15940337/37778931862957161709568)), (2114904665/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((2605685/151115727451828646838272), (-4536257/151115727451828646838272)), (8444172163/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((87983/37778931862957161709568), (-33535/37778931862957161709568)), (8439934391/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((5841/37778931862957161709568), (1761/37778931862957161709568)), (527429399/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((439/75557863725914323419136), (569/75557863725914323419136)), (8438623829/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((3/75557863725914323419136), (77/151115727451828646838272)), (8438570733/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((-1/151115727451828646838272), (1/37778931862957161709568)), (2109640011/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-685566205/18014398509481984), (-2144814993/72057594037927936)), (159401/72057594037927936), by norm_num⟩
  | 1 => ⟨((2361970359/72057594037927936), (-2878677817/36028797018963968)), (114887/18014398509481984), by norm_num⟩
  | 2 => ⟨((1642272053/36028797018963968), (5213819/562949953421312)), (1523427/144115188075855872), by norm_num⟩
  | 3 => ⟨((566677073/576460752303423488), (5199006123/576460752303423488)), (3854769/288230376151711744), by norm_num⟩
  | 4 => ⟨((316370551/576460752303423488), (4779482717/4611686018427387904)), (8189199/576460752303423488), by norm_num⟩
  | 5 => ⟨((-123759911/576460752303423488), (2597009643/4611686018427387904)), (124877827/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-7443385625/73786976294838206464), (-225573391/18446744073709551616)), (450704893/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-374398747/147573952589676412928), (-1585675813/295147905179352825856)), (201452125/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-244216655/295147905179352825856), (-338091435/590295810358705651712)), (5883900379/590295810358705651712), by norm_num⟩
  | 9 => ⟨((25912911/590295810358705651712), (-103832291/590295810358705651712)), (2770393699/295147905179352825856), by norm_num⟩
  | 10 => ⟨((3703725/295147905179352825856), (-151127/590295810358705651712)), (5359590055/590295810358705651712), by norm_num⟩
  | 11 => ⟨((194759/590295810358705651712), (-16041/590295810358705651712)), (329667373/36893488147419103232), by norm_num⟩
  | 12 => ⟨((44493/590295810358705651712), (15115/590295810358705651712)), (2619398087/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-21/73786976294838206464), (3295/590295810358705651712)), (2612482721/295147905179352825856), by norm_num⟩
  | 14 => ⟨((-41/590295810358705651712), (49/590295810358705651712)), (5220061281/590295810358705651712), by norm_num⟩
  | 15 => ⟨((-3/590295810358705651712), (9/590295810358705651712)), (1304613091/147573952589676412928), by norm_num⟩
  | 16 => ⟨(0, 0), (5217963435/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2677993/70368744177664), (-33512735/1125899906842624)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((36905787/1125899906842624), (-44979341/562949953421312)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((25660501/562949953421312), (5213819/562949953421312)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((1106791/1125899906842624), (10154309/1125899906842624)), (1/68719476736), by norm_num⟩
  | 4 => ⟨((617911/1125899906842624), (583433/562949953421312)), (1/68719476736), by norm_num⟩
  | 5 => ⟨((-120859/562949953421312), (158509/281474976710656)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((-113577/1125899906842624), (-1721/140737488355328)), (1/68719476736), by norm_num⟩
  | 7 => ⟨((-357/140737488355328), (-6049/1125899906842624)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-233/281474976710656), (-645/1125899906842624)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((49/1125899906842624), (-99/562949953421312)), (1/68719476736), by norm_num⟩
  | 10 => ⟨((7/562949953421312), 0), (1/68719476736), by norm_num⟩
  | 11 => ⟨(0, 0), (1/68719476736), by norm_num⟩
  | 12 => ⟨(0, 0), (1/68719476736), by norm_num⟩
  | 13 => ⟨(0, 0), (1/68719476736), by norm_num⟩
  | 14 => ⟨(0, 0), (1/68719476736), by norm_num⟩
  | 15 => ⟨(0, 0), (1/68719476736), by norm_num⟩
  | 16 => ⟨(0, 0), (1/68719476736), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨49,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨49,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(161751/1048576)) (K:=(143/1073741824)) (L:=(57039497624187/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile049
