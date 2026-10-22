/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile030Gamma
import XiBand97.Tile030Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile030
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((50630257/1125899906842624), (869265757/9007199254740992)), (493/2251799813685248), by norm_num⟩
  | 1 => ⟨((-141167629/9007199254740992), (697236185/4503599627370496)), (15/35184372088832), by norm_num⟩
  | 2 => ⟨((-600776917/9007199254740992), (819431333/9007199254740992)), (1049/2251799813685248), by norm_num⟩
  | 3 => ⟨((-223162057/4503599627370496), (390223641/18014398509481984)), (403/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1381758121/72057594037927936), (-74657059/36028797018963968)), (7941/36028797018963968), by norm_num⟩
  | 5 => ⟨((-640019719/144115188075855872), (-114353229/36028797018963968)), (17693/144115188075855872), by norm_num⟩
  | 6 => ⟨((-633758115/1152921504606846976), (-1329037667/1152921504606846976)), (41465/576460752303423488), by norm_num⟩
  | 7 => ⟨((30521147/2305843009213693952), (-585128973/2305843009213693952)), (58385/1152921504606846976), by norm_num⟩
  | 8 => ⟨((208267199/9223372036854775808), (-347271575/9223372036854775808)), (198881/4611686018427387904), by norm_num⟩
  | 9 => ⟨((841026871/147573952589676412928), (-8096469/2305843009213693952)), (3012087/73786976294838206464), by norm_num⟩
  | 10 => ⟨((67080655/73786976294838206464), (-5664357/73786976294838206464)), (1482951/36893488147419103232), by norm_num⟩
  | 11 => ⟨((494162861/4722366482869645213696), (24141023/590295810358705651712)), (378191061/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((162969985/18889465931478580854784), (173821461/18889465931478580854784)), (94467481/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((15485543/37778931862957161709568), (5832575/4722366482869645213696)), (1511217339/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-3647/295147905179352825856), (4669565/37778931862957161709568)), (94447983/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((-202423/37778931862957161709568), (91149/9444732965739290427392)), (188894873/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((-6799/9444732965739290427392), (21533/37778931862957161709568)), (1511157539/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile030Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((276767365/67108864), (886211837/67108864)), (14537/67108864), by norm_num⟩
  | 1 => ⟨((-26605359/2097152), (99949171/8388608)), (8013/33554432), by norm_num⟩
  | 2 => ⟨((100551405/8388608), (-50849119/8388608)), (4199/16777216), by norm_num⟩
  | 3 => ⟨((-815640875/134217728), (257626207/134217728)), (33031/134217728), by norm_num⟩
  | 4 => ⟨((294635771/134217728), (-50816387/134217728)), (125071/536870912), by norm_num⟩
  | 5 => ⟨((-83271641/134217728), (6675835/268435456)), (471105/2147483648), by norm_num⟩
  | 6 => ⟨((2419597/16777216), (3730967/268435456)), (1800883/8589934592), by norm_num⟩
  | 7 => ⟨((-15232767/536870912), (-7519475/1073741824)), (1753875/8589934592), by norm_num⟩
  | 8 => ⟨((5155389/1073741824), (4351709/2147483648)), (27707183/137438953472), by norm_num⟩
  | 9 => ⟨((-1511551/2147483648), (-1931893/4294967296)), (110252859/549755813888), by norm_num⟩
  | 10 => ⟨((1532897/17179869184), (713279/8589934592)), (1760716717/8796093022208), by norm_num⟩
  | 11 => ⟨((-661677/68719476736), (-227123/17179869184)), (1759645229/8796093022208), by norm_num⟩
  | 12 => ⟨((57957/68719476736), (508981/274877906944)), (1759330381/8796093022208), by norm_num⟩
  | 13 => ⟨((-55639/1099511627776), (-253787/1099511627776)), (1759245733/8796093022208), by norm_num⟩
  | 14 => ⟨((-509/4398046511104), (113325/4398046511104)), (1759224759/8796093022208), by norm_num⟩
  | 15 => ⟨((1345/2199023255552), (-11347/4398046511104)), (439804977/2199023255552), by norm_num⟩
  | 16 => ⟨((-1027/8796093022208), (1015/4398046511104)), (1759218865/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile030Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (31473/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (31473/1280))
  have he : value ((69/80), (31473/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1888909195/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((43744898688867/1125899906842624), (-42864947404063/70368744177664)), (26432667/1125899906842624), by norm_num⟩
  | 1 => ⟨((-95512567/4294967296), (1497460521/4294967296)), (15/1073741824), by norm_num⟩
  | 2 => ⟨((54668045/8589934592), (-428546953/4294967296)), (71/17179869184), by norm_num⟩
  | 3 => ⟨((-83440193/68719476736), (1308188013/68719476736)), (7/8589934592), by norm_num⟩
  | 4 => ⟨((95516483/549755813888), (-1497521915/549755813888)), (67/549755813888), by norm_num⟩
  | 5 => ⟨((-43736229/2199023255552), (1371406473/4398046511104)), (63/4398046511104), by norm_num⟩
  | 6 => ⟨((66754891/35184372088832), (-1046593317/35184372088832)), (25/17592186044416), by norm_num⟩
  | 7 => ⟨((-10916617/70368744177664), (1369219027/562949953421312)), (67/562949953421312), by norm_num⟩
  | 8 => ⟨((49986311/4503599627370496), (-1567385941/9007199254740992)), (79/9007199254740992), by norm_num⟩
  | 9 => ⟨((-50862955/72057594037927936), (1594874249/144115188075855872)), (83/144115188075855872), by norm_num⟩
  | 10 => ⟨((11644869/288230376151711744), (-730280087/1152921504606846976)), (39/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-77557699/36893488147419103232), (1215961369/36893488147419103232)), (67/36893488147419103232), by norm_num⟩
  | 12 => ⟨((118376821/1180591620717411303424), (-1855929759/1180591620717411303424)), (105/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-20847613/4722366482869645213696), (1307408161/18889465931478580854784)), (19/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((27274155/151115727451828646838272), (-855216683/302231454903657293676544)), (51/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-66605953/9671406556917033397649408), (261064559/2417851639229258349412352)), (1/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((76245825/309485009821345068724781056), (-298848403/77371252455336267181195264)), (75/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-1963165475737/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781206532665361/633825300114114700748351602688), (-2329366139897/633825300114114700748351602688)), (5777/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892483895945215/39614081257132168796771975168), (-2620415719817/39614081257132168796771975168)), (1625/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((946214910690397/1237940039285380274899124224), (-2784050863277/2475880078570760549798248448)), (27629/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774095479483029/154742504910672534362390528), (-1391946194989/77371252455336267181195264)), (13817/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776138019838979/4835703278458516698824704), (-2609730711143/9671406556917033397649408)), (3239/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1261170342946275/604462909807314587353088), (-2283345937897/604462909807314587353088)), (22679/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472915265930161/18889465931478580854784), (-3710121271171/75557863725914323419136)), (36861/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300440186752933/4722366482869645213696), (-2782314496737/4722366482869645213696)), (13827/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625434948258285/590295810358705651712), (-1912616536015/295147905179352825856)), (19019/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457113912008187/18446744073709551616), (-2390433545267/36893488147419103232)), (47567/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828257084748675/9223372036854775808), (-5377548045965/9223372036854775808)), (53541/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599501253051597/1152921504606846976), (-672048531379/144115188075855872)), (6697/144115188075855872), by norm_num⟩
  | 5 => ⟨((1199401853442901/144115188075855872), (-1175758563701/36028797018963968)), (23459/72057594037927936), by norm_num⟩
  | 4 => ⟨((749429644196395/18014398509481984), (-7051938715581/36028797018963968)), (8807/4503599627370496), by norm_num⟩
  | 3 => ⟨((749133996507241/4503599627370496), (-8810347325155/9007199254740992)), (88207/9007199254740992), by norm_num⟩
  | 2 => ⟨((561479406183491/1125899906842624), (-8803475429103/2251799813685248)), (44207/1125899906842624), by norm_num⟩
  | 1 => ⟨((560732637362363/562949953421312), (-13188006191533/1125899906842624)), (66569/562949953421312), by norm_num⟩
  | 0 => ⟨((1116938914207183/1125899906842624), (-26307021784601/1125899906842624)), (268345/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116938914207183/1125899906842624), (-26307021784601/1125899906842624)), (1023654942039107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((138429321192029/140737488355328), (-6524411310797/140737488355328)), (8515/17592186044416), by norm_num⟩
  | 2 => ⟨((1086852365843553/1125899906842624), (-25669630444191/281474976710656)), (1122573/1125899906842624), by norm_num⟩
  | 3 => ⟨((519897541153765/562949953421312), (-99117509146391/562949953421312)), (2372033/1125899906842624), by norm_num⟩
  | 4 => ⟨((925372392680209/1125899906842624), (-183074708425915/562949953421312)), (652067/140737488355328), by norm_num⟩
  | 5 => ⟨((320742841030679/562949953421312), (-601873327977815/1125899906842624)), (11967797/1125899906842624), by norm_num⟩
  | 6 => ⟨((43744898688867/1125899906842624), (-42864947404063/70368744177664)), (26432667/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1888909195/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((136312077/2251799813685248), (-425913101/18014398509481984)), (327/2251799813685248), by norm_num⟩
  | 1 => ⟨((1063747145/18014398509481984), (524121193/18014398509481984)), (1637/4503599627370496), by norm_num⟩
  | 2 => ⟨((328298105/36028797018963968), (141343765/4503599627370496)), (4413/9007199254740992), by norm_num⟩
  | 3 => ⟨((-794030111/144115188075855872), (651095707/72057594037927936)), (66165/144115188075855872), by norm_num⟩
  | 4 => ⟨((-88716679/36028797018963968), (8723453/18014398509481984)), (194035/576460752303423488), by norm_num⟩
  | 5 => ⟨((-431058295/1152921504606846976), (-79009953/288230376151711744)), (486437/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-146914797/18446744073709551616), (-1269655903/18446744073709551616)), (2298481/18446744073709551616), by norm_num⟩
  | 7 => ⟨((817470559/147573952589676412928), (-483877219/73786976294838206464)), (1444089/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1055564801/1180591620717411303424), (-66502365/1180591620717411303424)), (68054395/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((35084747/590295810358705651712), (999243415/18889465931478580854784)), (469643413/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((2278287/4722366482869645213696), (227929727/37778931862957161709568)), (1777429861/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-2235931/9444732965739290427392), (12013249/37778931862957161709568)), (873398913/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-820849/37778931862957161709568), (239653/37778931862957161709568)), (1738383513/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((-21433/18889465931478580854784), (-2771/9444732965739290427392)), (868133229/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-879/18889465931478580854784), (-1425/37778931862957161709568)), (1735774653/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-55/37778931862957161709568), (-107/37778931862957161709568)), (1735668457/37778931862957161709568), by norm_num⟩
  | 16 => ⟨(0, (-3/18889465931478580854784)), (433911755/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((632613065/1125899906842624), (395128579/562949953421312)), (23365/1125899906842624), by norm_num⟩
  | 1 => ⟨((-44117469/70368744177664), (1056073/549755813888)), (3453/70368744177664), by norm_num⟩
  | 2 => ⟨((-501232921/562949953421312), (-4652195/70368744177664)), (79877/1125899906842624), by norm_num⟩
  | 3 => ⟨((-314820581/4503599627370496), (-20943257/281474976710656)), (375285/4503599627370496), by norm_num⟩
  | 4 => ⟨((-410739285/9007199254740992), (-253288479/9007199254740992)), (1527645/18014398509481984), by norm_num⟩
  | 5 => ⟨((312255409/72057594037927936), (-554544151/36028797018963968)), (1416327/18014398509481984), by norm_num⟩
  | 6 => ⟨((584712055/288230376151711744), (1563297/9007199254740992)), (2504787/36028797018963968), by norm_num⟩
  | 7 => ⟨((392630625/9223372036854775808), (697984539/9223372036854775808)), (282832549/4611686018427387904), by norm_num⟩
  | 8 => ⟨((261718825/18446744073709551616), (34737081/4611686018427387904)), (32069313/576460752303423488), by norm_num⟩
  | 9 => ⟨((-16783117/36893488147419103232), (85532101/36893488147419103232)), (241335195/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-4770763/36893488147419103232), (277903/36893488147419103232)), (934837167/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-106519/36893488147419103232), (3897/2305843009213693952)), (230323121/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-24691/36893488147419103232), (-2815/18446744073709551616)), (457936501/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-43/18446744073709551616), (-1223/36893488147419103232)), (1827788043/36893488147419103232), by norm_num⟩
  | 14 => ⟨((-7/18446744073709551616), (-17/18446744073709551616)), (1826456265/36893488147419103232), by norm_num⟩
  | 15 => ⟨((5/36893488147419103232), (-1/9223372036854775808)), (1826040145/36893488147419103232), by norm_num⟩
  | 16 => ⟨(0, (1/36893488147419103232)), (1825918773/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((632613043/1125899906842624), (49391075/70368744177664)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-705879589/1125899906842624), (540709381/281474976710656)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-1002465889/1125899906842624), (-18608791/281474976710656)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((-78705121/1125899906842624), (-41886521/562949953421312)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-51342421/1125899906842624), (-31661059/1125899906842624)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((4878999/1125899906842624), (-17329509/1125899906842624)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((1142015/562949953421312), (195413/1125899906842624)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((23965/562949953421312), (42601/562949953421312)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((7987/562949953421312), (8481/1125899906842624)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((-1/2199023255552), (1305/562949953421312)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-73/562949953421312), (9/1125899906842624)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((-3/1125899906842624), (1/562949953421312)), (1/4294967296), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/4294967296), by norm_num⟩
  | 13 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 14 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 15 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 16 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨30,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨30,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(1635/536870912)) (L:=(530724937456859/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile030
