/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile026Gamma
import XiBand97.Tile026Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile026
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((534569757/2251799813685248), (-70355409/1125899906842624)), (417/2251799813685248), by norm_num⟩
  | 1 => ⟨((381951279/1125899906842624), (450432907/4503599627370496)), (823/2251799813685248), by norm_num⟩
  | 2 => ⟨((771619227/4503599627370496), (835765175/4503599627370496)), (1845/4503599627370496), by norm_num⟩
  | 3 => ⟨((56748133/2251799813685248), (1049365635/9007199254740992)), (723/2251799813685248), by norm_num⟩
  | 4 => ⟨((-463475137/36028797018963968), (358402169/9007199254740992)), (7239/36028797018963968), by norm_num⟩
  | 5 => ⟨((-619137461/72057594037927936), (565181527/72057594037927936)), (8215/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1500712805/576460752303423488), (175602217/288230376151711744)), (39469/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1160145177/2305843009213693952), (-322348883/2305843009213693952)), (56993/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-295304397/4611686018427387904), (-563575919/9223372036854775808)), (197167/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-39392389/9223372036854775808), (-14438699/1152921504606846976)), (1502289/36893488147419103232), by norm_num⟩
  | 10 => ⟨((36354087/147573952589676412928), (-129152495/73786976294838206464)), (23712407/590295810358705651712), by norm_num⟩
  | 11 => ⟨((141321157/1180591620717411303424), (-833689767/4722366482869645213696)), (189068971/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((763965839/37778931862957161709568), (-449765865/37778931862957161709568)), (755717987/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((5572953/2361183241434822606848), (-4604401/18889465931478580854784)), (1511209021/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((7984637/37778931862957161709568), (644373/9444732965739290427392)), (1511166255/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((138309/9444732965739290427392), (14959/1180591620717411303424)), (1511158739/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((13545/18889465931478580854784), (13317/9444732965739290427392)), (377789375/9444732965739290427392), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile026Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((200589159/67108864), (1804389355/67108864)), (14269/67108864), by norm_num⟩
  | 1 => ⟨((-190704305/33554432), (-23006959/2097152)), (7717/33554432), by norm_num⟩
  | 2 => ⟨((604817031/134217728), (1302497343/134217728)), (32187/134217728), by norm_num⟩
  | 3 => ⟨((-222904757/134217728), (-20719129/4194304)), (31795/134217728), by norm_num⟩
  | 4 => ⟨((49732113/134217728), (238796143/134217728)), (121555/536870912), by norm_num⟩
  | 5 => ⟨((-9945723/268435456), (-133708949/268435456)), (462641/2147483648), by norm_num⟩
  | 6 => ⟨((-1076867/134217728), (61222749/536870912)), (1783731/8589934592), by norm_num⟩
  | 7 => ⟨((5487213/1073741824), (-23601565/1073741824)), (1746291/8589934592), by norm_num⟩
  | 8 => ⟨((-1645895/1073741824), (7784943/2147483648)), (27659951/137438953472), by norm_num⟩
  | 9 => ⟨((1462437/4294967296), (-2210769/4294967296)), (110185915/549755813888), by norm_num⟩
  | 10 => ⟨((-532983/8589934592), (1075879/17179869184)), (1760379309/8796093022208), by norm_num⟩
  | 11 => ⟨((665075/68719476736), (-438199/68719476736)), (1759547437/8796093022208), by norm_num⟩
  | 12 => ⟨((-363093/274877906944), (138713/274877906944)), (1759304493/8796093022208), by norm_num⟩
  | 13 => ⟨((2743/17179869184), (-12179/549755813888)), (1759239405/8796093022208), by norm_num⟩
  | 14 => ⟨((-18893/1099511627776), (-927/549755813888)), (1759223293/8796093022208), by norm_num⟩
  | 15 => ⟨((14473/8796093022208), (5145/8796093022208)), (439804899/2199023255552), by norm_num⟩
  | 16 => ⟨((-611/4398046511104), (-823/8796093022208)), (1759218803/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile026Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30041/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30041/1280))
  have he : value ((69/80), (30041/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1802965117/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((444842225423681/1125899906842624), (-1047672395217919/2251799813685248)), (4994391/281474976710656), by norm_num⟩
  | 1 => ⟨((-971268063/4294967296), (1143743421/4294967296)), (23/2147483648), by norm_num⟩
  | 2 => ⟨((277959895/4294967296), (-327319319/4294967296)), (7/2147483648), by norm_num⟩
  | 3 => ⟨((-848503997/68719476736), (499589609/34359738368)), (45/68719476736), by norm_num⟩
  | 4 => ⟨((242826971/137438953472), (-1143790313/549755813888)), (27/274877906944), by norm_num⟩
  | 5 => ⟨((-889508131/4398046511104), (261866191/1099511627776)), (13/1099511627776), by norm_num⟩
  | 6 => ⟨((169707757/8796093022208), (-799376147/35184372088832)), (21/17592186044416), by norm_num⟩
  | 7 => ⟨((-222022333/140737488355328), (522897009/281474976710656)), (57/562949953421312), by norm_num⟩
  | 8 => ⟨((15884725/140737488355328), (-299287917/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 9 => ⟨((-517225797/72057594037927936), (609073463/72057594037927936)), (37/72057594037927936), by norm_num⟩
  | 10 => ⟨((236833531/576460752303423488), (-557779677/1152921504606846976)), (71/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-788684861/36893488147419103232), (928737551/36893488147419103232)), (61/36893488147419103232), by norm_num⟩
  | 12 => ⟨((601887421/590295810358705651712), (-708769087/590295810358705651712)), (49/590295810358705651712), by norm_num⟩
  | 13 => ⟨((-847998177/18889465931478580854784), (998583577/18889465931478580854784)), (71/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((138675551/75557863725914323419136), (-653204837/302231454903657293676544)), (3/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-338658235/4835703278458516698824704), (797592639/9671406556917033397649408)), (61/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((387672203/154742504910672534362390528), (-913028131/309485009821345068724781056)), (9/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-564529942499/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890604233156317/316912650057057350374175801344), (-1339669986323/633825300114114700748351602688)), (5771/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946243094677375/19807040628566084398385987584), (-1507060673701/39614081257132168796771975168)), (25971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892432401288855/2475880078570760549798248448), (-1601171167603/2475880078570760549798248448)), (27597/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774098220427435/154742504910672534362390528), (-1601080268465/154742504910672534362390528)), (27599/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776139390194217/4835703278458516698824704), (-1500916171175/9671406556917033397649408)), (25877/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261172912113769/604462909807314587353088), (-656602534535/302231454903657293676544)), (11323/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118229097454159/4722366482869645213696), (-533444286999/18889465931478580854784)), (9201/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300443838917775/4722366482869645213696), (-800087203749/2361183241434822606848)), (27609/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625440425689569/590295810358705651712), (-2199982322609/590295810358705651712)), (37969/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914231589087281/36893488147419103232), (-1374795835197/36893488147419103232)), (2967/4611686018427387904), by norm_num⟩
  | 7 => ⟨((914133247718113/4611686018427387904), (-3092759556891/9223372036854775808)), (53423/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799755918669281/576460752303423488), (-24156997761/9007199254740992)), (53443/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599706217154099/72057594037927936), (-1352418460567/72057594037927936)), (46785/144115188075855872), by norm_num⟩
  | 4 => ⟨((374719449301387/9007199254740992), (-4055761715341/36028797018963968)), (35111/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498295740823707/9007199254740992), (-2533544102969/4503599627370496)), (5491/562949953421312), by norm_num⟩
  | 2 => ⟨((1122993470145707/2251799813685248), (-5063167256283/2251799813685248)), (87975/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121534509272075/1125899906842624), (-7584948370865/1125899906842624)), (132259/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117146212368413/1125899906842624), (-15130685919831/1125899906842624)), (132853/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117146212368413/1125899906842624), (-15130685919831/1125899906842624)), (506793977977561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1108257239004373/1125899906842624), (-30026094439029/1125899906842624)), (534423/1125899906842624), by norm_num⟩
  | 2 => ⟨((545045138559501/562949953421312), (-29555590438231/562949953421312)), (1080603/1125899906842624), by norm_num⟩
  | 3 => ⟨((263079043120123/281474976710656), (-114462259301813/1125899906842624)), (2205935/1125899906842624), by norm_num⟩
  | 4 => ⟨((242976243138741/281474976710656), (-53490761421117/281474976710656)), (2286027/562949953421312), by norm_num⟩
  | 5 => ⟨((199577929906545/281474976710656), (-184698254951367/562949953421312)), (4815573/562949953421312), by norm_num⟩
  | 6 => ⟨((444842225423681/1125899906842624), (-1047672395217919/2251799813685248)), (4994391/281474976710656), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1802965117/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((72870501/1125899906842624), (-1217234677/9007199254740992)), (371/2251799813685248), by norm_num⟩
  | 1 => ⟨((1292738029/9007199254740992), (-184509679/4503599627370496)), (1877/4503599627370496), by norm_num⟩
  | 2 => ⟨((138005173/2251799813685248), (706022109/18014398509481984)), (10279/18014398509481984), by norm_num⟩
  | 3 => ⟨((255881911/72057594037927936), (821710825/36028797018963968)), (39087/72057594037927936), by norm_num⟩
  | 4 => ⟨((-246118025/72057594037927936), (593375489/144115188075855872)), (29053/72057594037927936), by norm_num⟩
  | 5 => ⟨((-1109658799/1152921504606846976), (36560967/1152921504606846976)), (9237/36028797018963968), by norm_num⟩
  | 6 => ⟨((-889308261/9223372036854775808), (-466164563/4611686018427387904)), (1422977/9223372036854775808), by norm_num⟩
  | 7 => ⟨((91049665/73786976294838206464), (-1229827247/73786976294838206464)), (7327047/73786976294838206464), by norm_num⟩
  | 8 => ⟨((96579277/73786976294838206464), (-307426193/295147905179352825856)), (22080475/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1321229729/9444732965739290427392), (88690491/4722366482869645213696)), (309055295/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((58751517/9444732965739290427392), (149593145/18889465931478580854784)), (588332693/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-245619/9444732965739290427392), (718701/1180591620717411303424)), (1158714997/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-179243/9444732965739290427392), (30367/1180591620717411303424)), (288451875/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((-6599/4722366482869645213696), (3677/4722366482869645213696)), (1152578227/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-819/9444732965739290427392), (125/9444732965739290427392)), (1152293811/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-11/2361183241434822606848), (-7/4722366482869645213696)), (288058155/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((-3/18889465931478580854784), (-3/18889465931478580854784)), (1152220307/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1077214979/281474976710656), (188064289/140737488355328)), (3337/70368744177664), by norm_num⟩
  | 1 => ⟨((-45015347/140737488355328), (534032917/140737488355328)), (14129/140737488355328), by norm_num⟩
  | 2 => ⟨((-599708621/1125899906842624), (498121509/1125899906842624)), (38859/281474976710656), by norm_num⟩
  | 3 => ⟨((-566770951/2251799813685248), (858961441/2251799813685248)), (344575/2251799813685248), by norm_num⟩
  | 4 => ⟨((-385899565/2251799813685248), (-29617801/562949953421312)), (689095/4503599627370496), by norm_num⟩
  | 5 => ⟨((133497095/36028797018963968), (-264572563/9007199254740992)), (5178415/36028797018963968), by norm_num⟩
  | 6 => ⟨((130533823/72057594037927936), (-272219573/576460752303423488)), (38040161/288230376151711744), by norm_num⟩
  | 7 => ⟨((588127997/4611686018427387904), (-101222093/576460752303423488)), (70325919/576460752303423488), by norm_num⟩
  | 8 => ⟨((101084705/2305843009213693952), (50336935/4611686018427387904)), (1063254593/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-302357/2305843009213693952), (62901009/18446744073709551616)), (2056243345/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-770947/18446744073709551616), (490921/9223372036854775808)), (505396093/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-78645/18446744073709551616), (61357/4611686018427387904)), (2006399151/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-9229/9223372036854775808), (-547/18446744073709551616)), (2000398703/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-257/18446744073709551616), (-39/4611686018427387904)), (999117439/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-37/18446744073709551616), (-11/9223372036854775808)), (1997516021/18446744073709551616), by norm_num⟩
  | 15 => ⟨((3/9223372036854775808), (-1/18446744073709551616)), (31207725/288230376151711744), by norm_num⟩
  | 16 => ⟨((1/18446744073709551616), (1/9223372036854775808)), (998615337/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((4308859905/1125899906842624), (1504514281/1125899906842624)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-180061413/562949953421312), (4272263309/1125899906842624)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((-299854275/562949953421312), (498121445/1125899906842624)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((-141692753/562949953421312), (429480773/1125899906842624)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-48237443/281474976710656), (-59235643/1125899906842624)), (1/2147483648), by norm_num⟩
  | 5 => ⟨((4171789/1125899906842624), (-516743/17592186044416)), (1/2147483648), by norm_num⟩
  | 6 => ⟨((2039589/1125899906842624), (-132921/281474976710656)), (1/2147483648), by norm_num⟩
  | 7 => ⟨((143587/1125899906842624), (-197697/1125899906842624)), (1/2147483648), by norm_num⟩
  | 8 => ⟨((49357/1125899906842624), (12289/1125899906842624)), (1/2147483648), by norm_num⟩
  | 9 => ⟨((-37/281474976710656), (3839/1125899906842624)), (1/2147483648), by norm_num⟩
  | 10 => ⟨((-47/1125899906842624), (15/281474976710656)), (1/2147483648), by norm_num⟩
  | 11 => ⟨((-5/1125899906842624), (15/1125899906842624)), (1/2147483648), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/2147483648), by norm_num⟩
  | 13 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | 14 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | 15 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | 16 => ⟨(0, 0), (1/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨26,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨26,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(2513/536870912)) (L:=(4785671100184467/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile026
