/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import XiBand97.Tile047Gamma
import XiBand97.Tile047Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile047
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨47,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1681862377/576460752303423488), (2626279895/1152921504606846976)), (441/9007199254740992), by norm_num⟩
  | 1 => ⟨((315716093/144115188075855872), (6051015653/1152921504606846976)), (34935/576460752303423488), by norm_num⟩
  | 2 => ⟨((-563932053/1152921504606846976), (2487736577/576460752303423488)), (18359/288230376151711744), by norm_num⟩
  | 3 => ⟨((-2930824859/2305843009213693952), (64604265/36028797018963968)), (134167/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-3434676337/4611686018427387904), (420337441/1152921504606846976)), (29103/576460752303423488), by norm_num⟩
  | 5 => ⟨((-573234489/2305843009213693952), (-44165487/4611686018427387904)), (103415/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-1972089717/36893488147419103232), (-2293343159/73786976294838206464)), (3089881/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-2059400855/295147905179352825856), (-51106267/4611686018427387904)), (5995151/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-122457145/590295810358705651712), (-5676359585/2361183241434822606848)), (23719859/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1387133225/9444732965739290427392), (-3442988677/9444732965739290427392)), (189120953/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((3238183217/75557863725914323419136), (-2874190613/75557863725914323419136)), (755793217/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((68758343/9444732965739290427392), (-306399119/151115727451828646838272)), (188906291/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((135308251/151115727451828646838272), (23878055/151115727451828646838272)), (6044703541/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((6214883/75557863725914323419136), (545987/9444732965739290427392)), (377790183/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((196011/37778931862957161709568), (670691/75557863725914323419136)), (1511157875/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((16033/151115727451828646838272), (146915/151115727451828646838272)), (3022314745/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((-489/18889465931478580854784), (49/590295810358705651712)), (6044629159/151115727451828646838272), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile047Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1091939669/33554432), (2062342221/67108864)), (6913/33554432), by norm_num⟩
  | 1 => ⟨((-574076259/16777216), (405536219/134217728)), (895/4194304), by norm_num⟩
  | 2 => ⟨((2936128087/134217728), (-154095487/33554432)), (58267/268435456), by norm_num⟩
  | 3 => ⟨((-5419754627/536870912), (1521559091/536870912)), (28913/134217728), by norm_num⟩
  | 4 => ⟨((2008684005/536870912), (-293896285/268435456)), (226385/1073741824), by norm_num⟩
  | 5 => ⟨((-77330959/67108864), (320074899/1073741824)), (442945/2147483648), by norm_num⟩
  | 6 => ⟨((323574569/1073741824), (-7823799/134217728)), (1744395/8589934592), by norm_num⟩
  | 7 => ⟨((-73052965/1073741824), (31203645/4294967296)), (1729263/8589934592), by norm_num⟩
  | 8 => ⟨((28855369/2147483648), (-112991/2147483648)), (110223995/549755813888), by norm_num⟩
  | 9 => ⟨((-40293543/17179869184), (-9168773/34359738368)), (110043739/549755813888), by norm_num⟩
  | 10 => ⟨((25052451/68719476736), (777061/8589934592)), (3519349593/17592186044416), by norm_num⟩
  | 11 => ⟨((-13937343/274877906944), (-88115/4294967296)), (3518694233/17592186044416), by norm_num⟩
  | 12 => ⟨((6949333/1099511627776), (4127865/1099511627776)), (3518503945/17592186044416), by norm_num⟩
  | 13 => ⟨((-3097559/4398046511104), (-1296303/2199023255552)), (3518453289/17592186044416), by norm_num⟩
  | 14 => ⟨((611251/8796093022208), (1438677/17592186044416)), (1759220413/8796093022208), by norm_num⟩
  | 15 => ⟨((-104259/17592186044416), (-89639/8796093022208)), (7036875943/35184372088832), by norm_num⟩
  | 16 => ⟨((14417/35184372088832), (20271/17592186044416)), (7036874721/35184372088832), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile047Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37201/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37201/1280))
  have he : value ((69/80), (37201/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-4465371013/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-825179809594419/2251799813685248), (549598524292717/1125899906842624)), (30318553/2251799813685248), by norm_num⟩
  | 1 => ⟨((3603393513/17179869184), (-4799971435/17179869184)), (135/17179869184), by norm_num⟩
  | 2 => ⟨((-1031228061/17179869184), (171708461/2147483648)), (79/34359738368), by norm_num⟩
  | 3 => ⟨((3147940215/274877906944), (-4193275881/274877906944)), (123/274877906944), by norm_num⟩
  | 4 => ⟨((-3603541243/2199023255552), (1200042055/549755813888)), (9/137438953472), by norm_num⟩
  | 5 => ⟨((825016271/4398046511104), (-2197958407/8796093022208)), (135/17592186044416), by norm_num⟩
  | 6 => ⟨((-1259227709/70368744177664), (3354758235/140737488355328)), (105/140737488355328), by norm_num⟩
  | 7 => ⟨((411850169/281474976710656), (-4388905155/2251799813685248)), (35/562949953421312), by norm_num⟩
  | 8 => ⟨((-471457197/4503599627370496), (314006931/2251799813685248)), (41/9007199254740992), by norm_num⟩
  | 9 => ⟨((1918901843/288230376151711744), (-2556111063/288230376151711744)), (85/288230376151711744), by norm_num⟩
  | 10 => ⟨((-878649715/2305843009213693952), (585211345/1152921504606846976)), (79/4611686018427387904), by norm_num⟩
  | 11 => ⟨((731502973/36893488147419103232), (-3897651875/147573952589676412928)), (67/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-1116497753/1180591620717411303424), (743626431/590295810358705651712)), (13/295147905179352825856), by norm_num⟩
  | 13 => ⟨((3146063619/75557863725914323419136), (-523847015/9444732965739290427392)), (149/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-514484721/302231454903657293676544), (2741318097/1208925819614629174706176)), (99/1208925819614629174706176), by norm_num⟩
  | 15 => ⟨((628209105/9671406556917033397649408), (-3347273335/38685626227668133590597632)), (123/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-719129737/309485009821345068724781056), (1915861911/618970019642690137449562112)), (143/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (2884962550043/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781203182282099/633825300114114700748351602688), (3423111379043/633825300114114700748351602688)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1892479922210695/39614081257132168796771975168), (3850814964325/39614081257132168796771975168)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1892425351250567/2475880078570760549798248448), (2045641519151/1237940039285380274899124224)), (13833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221761341291441/19342813113834066795298816), (4091049081475/154742504910672534362390528)), (3459/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552271290933747/9671406556917033397649408), (3835109828765/9671406556917033397649408)), (811/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1261165891431491/604462909807314587353088), (3355472295883/604462909807314587353088)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236456659304497/9444732965739290427392), (2726087859813/37778931862957161709568)), (9231/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300433858771609/4722366482869645213696), (511090390079/590295810358705651712)), (13853/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812712728854461/295147905179352825856), (5621329729339/590295810358705651712)), (9529/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828442600840641/73786976294838206464), (878208061229/9223372036854775808)), (23837/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914120389615537/4611686018427387904), (493906212815/576460752303423488)), (26837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599482914123303/1152921504606846976), (3950390476507/576460752303423488)), (13431/576460752303423488), by norm_num⟩
  | 5 => ⟨((74961470030923/9007199254740992), (6911247300753/144115188075855872)), (23533/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498827219206515/36028797018963968), (10362991954975/36028797018963968)), (17679/18014398509481984), by norm_num⟩
  | 3 => ⟨((93638744764057/562949953421312), (6473468063219/4503599627370496)), (22149/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122898763710929/2251799813685248), (202135926533/35184372088832)), (44451/2251799813685248), by norm_num⟩
  | 1 => ⟨((280336329949833/281474976710656), (9689674111695/562949953421312)), (4191/70368744177664), by norm_num⟩
  | 0 => ⟨((1116579764115627/1125899906842624), (9663810819841/281474976710656)), (135637/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116579764115627/1125899906842624), (9663810819841/281474976710656)), (517414097312545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1106009632145375/1125899906842624), (9583814280557/140737488355328)), (278343/1125899906842624), by norm_num⟩
  | 2 => ⟨((270312425475225/281474976710656), (37658022147683/281474976710656)), (584761/1125899906842624), by norm_num⟩
  | 3 => ⟨((63638588384961/70368744177664), (144658419363565/562949953421312)), (1279611/1125899906842624), by norm_num⟩
  | 4 => ⟨((846489517881773/1125899906842624), (523292419887695/1125899906842624)), (1486043/562949953421312), by norm_num⟩
  | 5 => ⟨((393205065993205/1125899906842624), (393428887887667/562949953421312)), (7231745/1125899906842624), by norm_num⟩
  | 6 => ⟨((-825179809594419/2251799813685248), (549598524292717/1125899906842624)), (30318553/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-4465371013/268435456)), (1/134217728), by norm_num⟩, -3, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-2514644875/1152921504606846976), (169891121/288230376151711744)), (96643/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-4880039187/2305843009213693952), (-686730653/576460752303423488)), (174969/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-1654391091/4611686018427387904), (-5695000321/4611686018427387904)), (3281/36028797018963968), by norm_num⟩
  | 3 => ⟨((971378175/4611686018427387904), (-1817079301/4611686018427387904)), (209303/2305843009213693952), by norm_num⟩
  | 4 => ⟨((4023318887/36893488147419103232), (-1282657851/36893488147419103232)), (3039339/36893488147419103232), by norm_num⟩
  | 5 => ⟨((380875719/18446744073709551616), (1507358245/147573952589676412928)), (10794073/147573952589676412928), by norm_num⟩
  | 6 => ⟨((761973599/590295810358705651712), (4205211429/1180591620717411303424)), (78656713/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-1970539825/9444732965739290427392), (4529354035/9444732965739290427392)), (297898183/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-2139735791/37778931862957161709568), (1859599243/75557863725914323419136)), (2323137135/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-452089083/75557863725914323419136), (-19395889/9444732965739290427392)), (2300031193/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-21067621/75557863725914323419136), (-9352679/18889465931478580854784)), (4584434185/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((166701/18889465931478580854784), (-3345603/75557863725914323419136)), (4579707335/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((186659/75557863725914323419136), (-153445/75557863725914323419136)), (2289205907/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((15377/75557863725914323419136), (-255/37778931862957161709568)), (4578086727/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((93/9444732965739290427392), (245/37778931862957161709568)), (4578011417/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((19/75557863725914323419136), (43/75557863725914323419136)), (4577995199/75557863725914323419136), by norm_num⟩
  | 16 => ⟨(0, (1/37778931862957161709568)), (4577991933/75557863725914323419136), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-3209884983/36028797018963968), (-430966199/9007199254740992)), (116113/36028797018963968), by norm_num⟩
  | 1 => ⟨((1462379727/36028797018963968), (-588014159/4503599627370496)), (137535/18014398509481984), by norm_num⟩
  | 2 => ⟨((64498623/1125899906842624), (437241475/72057594037927936)), (25519/2251799813685248), by norm_num⟩
  | 3 => ⟨((1022936623/288230376151711744), (3660204091/576460752303423488)), (3880855/288230376151711744), by norm_num⟩
  | 4 => ⟨((2660392559/1152921504606846976), (1836444999/1152921504606846976)), (8063677/576460752303423488), by norm_num⟩
  | 5 => ⟨((-539020157/2305843009213693952), (2028260625/2305843009213693952)), (62184527/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-4126576391/36893488147419103232), (53901171/73786976294838206464)), (465192651/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-3038757947/590295810358705651712), (-260497419/590295810358705651712)), (6965343629/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-511990817/295147905179352825856), (-446412079/590295810358705651712)), (6626823265/590295810358705651712), by norm_num⟩
  | 9 => ⟨((22216095/590295810358705651712), (-138592387/590295810358705651712)), (6425941277/590295810358705651712), by norm_num⟩
  | 10 => ⟨((3253107/295147905179352825856), (-1440237/590295810358705651712)), (790273083/73786976294838206464), by norm_num⟩
  | 11 => ⟨((284181/590295810358705651712), (-169771/295147905179352825856)), (6274514343/590295810358705651712), by norm_num⟩
  | 12 => ⟨((1027/9223372036854775808), (14951/590295810358705651712)), (3127375009/295147905179352825856), by norm_num⟩
  | 13 => ⟨((239/590295810358705651712), (3303/590295810358705651712)), (3123638667/295147905179352825856), by norm_num⟩
  | 14 => ⟨((21/295147905179352825856), (35/295147905179352825856)), (97573135/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-3/590295810358705651712), (13/590295810358705651712)), (780480955/73786976294838206464), by norm_num⟩
  | 16 => ⟨(0, 0), (6243601953/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-50154453/562949953421312), (-53870775/1125899906842624)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((22849683/562949953421312), (-147003541/1125899906842624)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((1007791/17592186044416), (3415949/562949953421312)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((1997923/562949953421312), (1787209/281474976710656)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((324755/140737488355328), (1793403/1125899906842624)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-263193/1125899906842624), (495181/562949953421312)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((-125933/1125899906842624), (411/562949953421312)), (1/34359738368), by norm_num⟩
  | 7 => ⟨((-1449/281474976710656), (-497/1125899906842624)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-1953/1125899906842624), (-851/1125899906842624)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((21/562949953421312), (-33/140737488355328)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((3/281474976710656), (-3/1125899906842624)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1/1125899906842624), (-1/1125899906842624)), (1/34359738368), by norm_num⟩
  | 12 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 13 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 14 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 15 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | 16 => ⟨(0, 0), (1/34359738368), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨47,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨47,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(323/1073741824)) (L:=(119390114739303/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile047
