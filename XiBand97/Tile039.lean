/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import XiBand97.Tile039Gamma
import XiBand97.Tile039Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile039
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-3778627365/288230376151711744), (-1080377723/72057594037927936)), (14397/288230376151711744), by norm_num⟩
  | 1 => ⟨((-832459941/144115188075855872), (-2112798209/72057594037927936)), (8957/144115188075855872), by norm_num⟩
  | 2 => ⟨((2048188733/288230376151711744), (-6082550385/288230376151711744)), (18643/288230376151711744), by norm_num⟩
  | 3 => ⟨((2355746245/288230376151711744), (-2115489249/288230376151711744)), (8419/144115188075855872), by norm_num⟩
  | 4 => ⟨((2269181431/576460752303423488), (-1028778049/1152921504606846976)), (7259/144115188075855872), by norm_num⟩
  | 5 => ⟨((5222352989/4611686018427387904), (1501396813/4611686018427387904)), (206173/4611686018427387904), by norm_num⟩
  | 6 => ⟨((936678977/4611686018427387904), (459969749/2305843009213693952)), (192747/4611686018427387904), by norm_num⟩
  | 7 => ⟨((648607689/36893488147419103232), (2060851865/36893488147419103232)), (374401/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-272272007/147573952589676412928), (6084487627/590295810358705651712)), (5928453/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-2366811713/2361183241434822606848), (3106043649/2361183241434822606848)), (94553927/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-3966514421/18889465931478580854784), (484151357/4722366482869645213696)), (755780749/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-4510321425/151115727451828646838272), (-1230547/18889465931478580854784)), (6044979971/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-473302325/151115727451828646838272), (-14251943/9444732965739290427392)), (6044699369/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((-35578145/151115727451828646838272), (-21771209/75557863725914323419136)), (3022321087/75557863725914323419136), by norm_num⟩
  | 14 => ⟨((-712121/75557863725914323419136), (-672609/18889465931478580854784)), (1511157843/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((80069/151115727451828646838272), (-253147/75557863725914323419136)), (3022314735/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((23505/151115727451828646838272), (-37363/151115727451828646838272)), (1511157289/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile039Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1623023915/67108864), (379960389/8388608)), (3443/16777216), by norm_num⟩
  | 1 => ⟨((1043937165/33554432), (-1044931593/67108864)), (7107/33554432), by norm_num⟩
  | 2 => ⟨((-1325215669/67108864), (1907521905/268435456)), (28895/134217728), by norm_num⟩
  | 3 => ⟨((301614815/33554432), (-1202496493/536870912)), (114813/536870912), by norm_num⟩
  | 4 => ⟨((-424722709/134217728), (264100033/536870912)), (450489/2147483648), by norm_num⟩
  | 5 => ⟨((488358443/536870912), (-15157537/268435456)), (1766531/8589934592), by norm_num⟩
  | 6 => ⟨((-473152815/2147483648), (-18751537/2147483648)), (1741795/8589934592), by norm_num⟩
  | 7 => ⟨((197014447/4294967296), (30502925/4294967296)), (27650319/137438953472), by norm_num⟩
  | 8 => ⟨((-8929449/1073741824), (-2575265/1073741824)), (110196539/549755813888), by norm_num⟩
  | 9 => ⟨((11368925/8589934592), (5088995/8589934592)), (880275415/4398046511104), by norm_num⟩
  | 10 => ⟨((-1593809/8589934592), (-2057501/17179869184)), (3519254873/17592186044416), by norm_num⟩
  | 11 => ⟨((6284027/274877906944), (2850833/137438953472)), (3518667353/17592186044416), by norm_num⟩
  | 12 => ⟨((-2690593/1099511627776), (-3468329/1099511627776)), (3518496873/17592186044416), by norm_num⟩
  | 13 => ⟨((484631/2199023255552), (235045/549755813888)), (3518451565/17592186044416), by norm_num⟩
  | 14 => ⟨((-266905/17592186044416), (-917231/17592186044416)), (3518440431/17592186044416), by norm_num⟩
  | 15 => ⟨((16667/35184372088832), (101213/17592186044416)), (7036875773/35184372088832), by norm_num⟩
  | 16 => ⟨((2577/35184372088832), (-20259/35184372088832)), (7036874687/35184372088832), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile039Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (34337/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (34337/1280))
  have he : value ((69/80), (34337/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-8243189401/536870912)), (3/536870912), by norm_num⟩
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
  | 0 => ⟨((-161165331547201/281474976710656), (-238119175964047/1125899906842624)), (11068023/1125899906842624), by norm_num⟩
  | 1 => ⟨((5630211535/17179869184), (1039818333/8589934592)), (99/17179869184), by norm_num⟩
  | 2 => ⟨((-402816963/4294967296), (-595155561/17179869184)), (59/34359738368), by norm_num⟩
  | 3 => ⟨((2459288619/137438953472), (454194905/68719476736)), (93/274877906944), by norm_num⟩
  | 4 => ⟨((-703805295/274877906944), (-2079721927/2199023255552)), (109/2199023255552), by norm_num⟩
  | 5 => ⟨((161133391/549755813888), (1904575875/17592186044416)), (51/8796093022208), by norm_num⟩
  | 6 => ⟨((-1967511555/70368744177664), (-1453483283/140737488355328)), (5/8796093022208), by norm_num⟩
  | 7 => ⟨((5148044063/2251799813685248), (1901538003/2251799813685248)), (107/2251799813685248), by norm_num⟩
  | 8 => ⟨((-1473279973/9007199254740992), (-2176747381/36028797018963968)), (125/36028797018963968), by norm_num⟩
  | 9 => ⟨((5996471521/576460752303423488), (276865309/72057594037927936)), (65/288230376151711744), by norm_num⟩
  | 10 => ⟨((-5491472127/9223372036854775808), (-2028390359/9223372036854775808)), (61/4611686018427387904), by norm_num⟩
  | 11 => ⟨((2285909913/73786976294838206464), (1688697501/147573952589676412928)), (13/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-3488999191/2361183241434822606848), (-644367499/1180591620717411303424)), (81/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((2457822551/37778931862957161709568), (1815696575/75557863725914323419136)), (29/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-25120919/9444732965739290427392), (-296926019/302231454903657293676544)), (77/1208925819614629174706176), by norm_num⟩
  | 15 => ⟨((3926243565/38685626227668133590597632), (1450240375/38685626227668133590597632)), (3/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((-1123622087/309485009821345068724781056), (-1660133499/1237940039285380274899124224)), (7/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-1815688324969/5070602400912917605986812821504)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((890599767923019/316912650057057350374175801344), (-4308758438409/633825300114114700748351602688)), (8685/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892475597341653/39614081257132168796771975168), (-2423555013737/19807040628566084398385987584)), (2443/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((29569070095961/38685626227668133590597632), (-5149791542077/2475880078570760549798248448)), (5193/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774085561549335/154742504910672534362390528), (-5149495584717/154742504910672534362390528)), (10389/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552266122597663/9671406556917033397649408), (-603417178855/1208925819614629174706176)), (9743/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315290261647691/151115727451828646838272), (-4223605319079/604462909807314587353088)), (8529/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891644796914213/75557863725914323419136), (-1715691901675/18889465931478580854784)), (6933/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300426971676201/4722366482869645213696), (-5146558010415/4722366482869645213696)), (10405/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625415128626819/590295810358705651712), (-7075675003365/590295810358705651712)), (3579/147573952589676412928), by norm_num⟩
  | 8 => ⟨((914214200446303/36893488147419103232), (-276354018781/2305843009213693952)), (17909/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828223033111439/9223372036854775808), (-9947002229139/9223372036854775808)), (2521/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599462954994033/1152921504606846976), (-4972409940617/576460752303423488)), (631/36028797018963968), by norm_num⟩
  | 5 => ⟨((1199363567948339/144115188075855872), (-8699256361579/144115188075855872)), (17695/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498792317099267/36028797018963968), (-6521973877083/18014398509481984)), (26597/36028797018963968), by norm_num⟩
  | 3 => ⟨((374541898213989/2251799813685248), (-8148131116259/4503599627370496)), (16671/4503599627370496), by norm_num⟩
  | 2 => ⟨((280708352961649/562949953421312), (-16283187474121/2251799813685248)), (16743/1125899906842624), by norm_num⟩
  | 1 => ⟨((560607386976879/562949953421312), (-24391863498583/1125899906842624)), (12647/281474976710656), by norm_num⟩
  | 0 => ⟨((1116188921878195/1125899906842624), (-3040667164333/70368744177664)), (102619/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116188921878195/1125899906842624), (-3040667164333/70368744177664)), (391460422996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((17257179313081/17592186044416), (-96462116628893/1125899906842624)), (212337/1125899906842624), by norm_num⟩
  | 2 => ⟨((1075162886955465/1125899906842624), (-189250390983959/1125899906842624)), (113243/281474976710656), by norm_num⟩
  | 3 => ⟨((497450757474573/562949953421312), (-361444202084307/1125899906842624)), (508699/562949953421312), by norm_num⟩
  | 4 => ⟨((763111452453331/1125899906842624), (-638780378322789/1125899906842624)), (2451273/1125899906842624), by norm_num⟩
  | 5 => ⟨((154808359140925/1125899906842624), (-1731808020723917/2251799813685248)), (1526077/281474976710656), by norm_num⟩
  | 6 => ⟨((-161165331547201/281474976710656), (-238119175964047/1125899906842624)), (11068023/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-8243189401/536870912)), (3/536870912), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1249578499/288230376151711744), (1636768311/144115188075855872)), (11369/288230376151711744), by norm_num⟩
  | 1 => ⟨((-1549286951/288230376151711744), (207337237/18014398509481984)), (10327/144115188075855872), by norm_num⟩
  | 2 => ⟨((-3554154551/576460752303423488), (1229133411/576460752303423488)), (49317/576460752303423488), by norm_num⟩
  | 3 => ⟨((-4515113223/2305843009213693952), (-1137593101/1152921504606846976)), (194665/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-1506543885/9223372036854775808), (-4764563065/9223372036854775808)), (700177/9223372036854775808), by norm_num⟩
  | 5 => ⟨((1814748561/36893488147419103232), (-1706887539/18446744073709551616)), (2474197/36893488147419103232), by norm_num⟩
  | 6 => ⟨((2331439151/147573952589676412928), (-1399588299/295147905179352825856)), (18008453/295147905179352825856), by norm_num⟩
  | 7 => ⟨((2255123793/1180591620717411303424), (2422501157/2361183241434822606848)), (136479439/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((1362023921/18889465931478580854784), (4370528953/18889465931478580854784)), (1065045399/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-1569266783/151115727451828646838272), (3157060761/151115727451828646838272)), (4219440021/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-275770013/151115727451828646838272), (26260985/37778931862957161709568)), (4205775239/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-2535903/18889465931478580854784), (-7537925/151115727451828646838272)), (2100832041/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-712293/151115727451828646838272), (-150975/18889465931478580854784)), (8401081543/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((7827/151115727451828646838272), (-20231/37778931862957161709568)), (8400518633/151115727451828646838272), by norm_num⟩
  | 14 => ⟨((1321/75557863725914323419136), (-855/37778931862957161709568)), (4200194139/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((25/18889465931478580854784), (-89/151115727451828646838272)), (8400360197/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((11/151115727451828646838272), 0), (4200177269/75557863725914323419136), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-5577974847/9007199254740992), (-705339743/9007199254740992)), (53693/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1433973651/18014398509481984), (-2125531927/9007199254740992)), (245159/18014398509481984), by norm_num⟩
  | 2 => ⟨((-1833923733/18014398509481984), (-1486620195/18014398509481984)), (684765/36028797018963968), by norm_num⟩
  | 3 => ⟨((1599403991/72057594037927936), (-5446891321/72057594037927936)), (1554963/72057594037927936), by norm_num⟩
  | 4 => ⟨((1140020267/72057594037927936), (189688841/288230376151711744)), (6316339/288230376151711744), by norm_num⟩
  | 5 => ⟨((3888565557/4611686018427387904), (1163064745/2305843009213693952)), (48611795/2305843009213693952), by norm_num⟩
  | 6 => ⟨((3441635417/9223372036854775808), (899205375/4611686018427387904)), (184034415/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-1276745687/73786976294838206464), (1420505599/18446744073709551616)), (701472665/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-910785027/147573952589676412928), (46198741/295147905179352825856)), (2715209157/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-55568341/295147905179352825856), (7907887/295147905179352825856)), (2665082399/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-15184309/295147905179352825856), (-1299053/73786976294838206464)), (1320411273/73786976294838206464), by norm_num⟩
  | 11 => ⟨((27879/73786976294838206464), (-1327897/295147905179352825856)), (1315160643/73786976294838206464), by norm_num⟩
  | 12 => ⟨((27969/295147905179352825856), (-17023/295147905179352825856)), (5252390579/295147905179352825856), by norm_num⟩
  | 13 => ⟨((759/147573952589676412928), (-897/73786976294838206464)), (164044233/9223372036854775808), by norm_num⟩
  | 14 => ⟨((307/295147905179352825856), (5/73786976294838206464)), (1312105891/73786976294838206464), by norm_num⟩
  | 15 => ⟨((1/73786976294838206464), (5/295147905179352825856)), (5248116703/295147905179352825856), by norm_num⟩
  | 16 => ⟨(0, 0), (2624014657/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-87155857/140737488355328), (-44083733/562949953421312)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((-44811677/562949953421312), (-8302859/35184372088832)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-114620235/1125899906842624), (-23228441/281474976710656)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((780959/35184372088832), (-21276919/281474976710656)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((1113301/70368744177664), (185243/281474976710656)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((949357/1125899906842624), (567903/1125899906842624)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((420121/1125899906842624), (219533/1125899906842624)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((-9741/562949953421312), (86701/1125899906842624)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-6949/1125899906842624), (11/70368744177664)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((-53/281474976710656), (15/562949953421312)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-29/562949953421312), (-5/281474976710656)), (1/17179869184), by norm_num⟩
  | 11 => ⟨(0, (-5/1125899906842624)), (1/17179869184), by norm_num⟩
  | 12 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 13 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 14 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 15 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 16 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨39,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨39,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(135/268435456)) (L:=(184234586909205/295147905179352825856)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile039
