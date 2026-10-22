/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile032Gamma
import XiBand97.Tile032Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile032
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6267079/18014398509481984), (1476718105/18014398509481984)), (3589/18014398509481984), by norm_num⟩
  | 1 => ⟨((-278163599/4503599627370496), (232528533/2251799813685248)), (1713/4503599627370496), by norm_num⟩
  | 2 => ⟨((-691836017/9007199254740992), (759594615/18014398509481984)), (7403/18014398509481984), by norm_num⟩
  | 3 => ⟨((-760102447/18014398509481984), (-33533415/36028797018963968)), (11331/36028797018963968), by norm_num⟩
  | 4 => ⟨((-934851701/72057594037927936), (-70051009/9007199254740992)), (14027/72057594037927936), by norm_num⟩
  | 5 => ⟨((-615737937/288230376151711744), (-538293669/144115188075855872)), (31917/288230376151711744), by norm_num⟩
  | 6 => ⟨((-9121049/576460752303423488), (-1166719971/1152921504606846976)), (77563/1152921504606846976), by norm_num⟩
  | 7 => ⟨((26963625/288230376151711744), (-51761219/288230376151711744)), (1769/36028797018963968), by norm_num⟩
  | 8 => ⟨((1068886529/36893488147419103232), (-184142875/9223372036854775808)), (787239/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1580100635/295147905179352825856), (-49879493/73786976294838206464)), (1501723/36893488147419103232), by norm_num⟩
  | 10 => ⟨((205720291/295147905179352825856), (73248257/295147905179352825856)), (23710885/590295810358705651712), by norm_num⟩
  | 11 => ⟨((150954309/2361183241434822606848), (620415067/9444732965739290427392)), (189067281/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((62697193/18889465931478580854784), (185261839/18889465931478580854784)), (755717307/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-4347853/37778931862957161709568), (10091551/9444732965739290427392)), (755604493/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-983119/18889465931478580854784), (3366349/37778931862957161709568)), (1511166281/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-280863/37778931862957161709568), (206223/37778931862957161709568)), (377789687/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((-28331/37778931862957161709568), (6847/37778931862957161709568)), (1511157503/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile032Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-46709957/33554432), (655114669/67108864)), (14547/67108864), by norm_num⟩
  | 1 => ⟨((-26553239/4194304), (645035651/33554432)), (16073/67108864), by norm_num⟩
  | 2 => ⟨((282093867/33554432), (-49881693/4194304)), (16859/67108864), by norm_num⟩
  | 3 => ⟨((-321629095/67108864), (648738407/134217728)), (8289/33554432), by norm_num⟩
  | 4 => ⟨((126307519/67108864), (-387770861/268435456)), (125427/536870912), by norm_num⟩
  | 5 => ⟨((-76950453/134217728), (44715817/134217728)), (471785/2147483648), by norm_num⟩
  | 6 => ⟨((77106017/536870912), (-32057789/536870912)), (1802163/8589934592), by norm_num⟩
  | 7 => ⟨((-8206821/268435456), (4233959/536870912)), (1754299/8589934592), by norm_num⟩
  | 8 => ⟨((1514085/268435456), (-1210991/2147483648)), (27708847/137438953472), by norm_num⟩
  | 9 => ⟨((-3920631/4294967296), (-254945/4294967296)), (110253499/549755813888), by norm_num⟩
  | 10 => ⟨((2241639/17179869184), (551131/17179869184)), (1760714157/8796093022208), by norm_num⟩
  | 11 => ⟨((-1134291/68719476736), (-517759/68719476736)), (1759642541/8796093022208), by norm_num⟩
  | 12 => ⟨((506007/274877906944), (365555/274877906944)), (1759329197/8796093022208), by norm_num⟩
  | 13 => ⟨((-98135/549755813888), (-215711/1099511627776)), (1759245333/8796093022208), by norm_num⟩
  | 14 => ⟨((31915/2199023255552), (55409/2199023255552)), (1759224627/8796093022208), by norm_num⟩
  | 15 => ⟨((-3893/4398046511104), (-6319/2199023255552)), (439804969/2199023255552), by norm_num⟩
  | 16 => ⟨((11/549755813888), (2585/8796093022208)), (1759218857/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile032Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63841/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63841/2560))
  have he : value ((69/80), (63841/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-29933855/2097152)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-11681650948861/140737488355328), (-340424538420881/562949953421312)), (83936123/2251799813685248), by norm_num⟩
  | 1 => ⟨((102022819/2147483648), (743282591/2147483648)), (47/2147483648), by norm_num⟩
  | 2 => ⟨((-58394285/4294967296), (-212714449/2147483648)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((178255155/68719476736), (1298669797/68719476736)), (43/34359738368), by norm_num⟩
  | 4 => ⟨((-204054003/549755813888), (-1486626129/549755813888)), (101/549755813888), by norm_num⟩
  | 5 => ⟨((186869373/4398046511104), (21272317/68719476736)), (95/4398046511104), by norm_num⟩
  | 6 => ⟨((-142609971/35184372088832), (-1038978433/35184372088832)), (37/17592186044416), by norm_num⟩
  | 7 => ⟨((93285655/281474976710656), (679628379/281474976710656)), (99/562949953421312), by norm_num⟩
  | 8 => ⟨((-106786877/4503599627370496), (-777990917/4503599627370496)), (29/2251799813685248), by norm_num⟩
  | 9 => ⟨((217319341/144115188075855872), (395817535/36028797018963968)), (121/144115188075855872), by norm_num⟩
  | 10 => ⟨((-49754389/576460752303423488), (-724966659/1152921504606846976)), (113/2305843009213693952), by norm_num⟩
  | 11 => ⟨((82844125/18446744073709551616), (1207114183/36893488147419103232)), (3/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-252891055/1180591620717411303424), (-921213121/590295810358705651712)), (149/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((178148891/18889465931478580854784), (324473905/4722366482869645213696)), (107/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-116532777/302231454903657293676544), (-1697988463/604462909807314587353088)), (71/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((142291789/9671406556917033397649408), (1036660341/9671406556917033397649408)), (89/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-162885663/309485009821345068724781056), (-593348037/154742504910672534362390528)), (13/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-2223823478909/10141204801825835211973625643008)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111325357154263/39614081257132168796771975168), (-1319323097543/316912650057057350374175801344)), (34673/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892482925519441/39614081257132168796771975168), (-1484169163607/19807040628566084398385987584)), (39013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892428729728661/2475880078570760549798248448), (-3153699765947/2475880078570760549798248448)), (41459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774094319690819/154742504910672534362390528), (-1576760024737/77371252455336267181195264)), (41467/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776137439992491/4835703278458516698824704), (-739058513731/2417851639229258349412352)), (9721/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630584627919787/302231454903657293676544), (-1293256879287/302231454903657293676544)), (2127/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((236457395186863/9444732965739290427392), (-2101363278317/37778931862957161709568)), (55317/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300438641392383/4722366482869645213696), (-787932825521/1180591620717411303424)), (41503/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625432630563849/590295810358705651712), (-4333120724243/590295810358705651712)), (223/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1828452461766021/73786976294838206464), (-5415635846861/73786976294838206464)), (71395/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828253102760367/9223372036854775808), (-3045768914763/4611686018427387904)), (80367/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599496774477445/1152921504606846976), (-6090221393135/1152921504606846976)), (40213/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199397376323135/144115188075855872), (-5327461610253/144115188075855872)), (8805/18014398509481984), by norm_num⟩
  | 4 => ⟨((1498851456708365/36028797018963968), (-1997056351577/9007199254740992)), (105793/36028797018963968), by norm_num⟩
  | 3 => ⟨((749128126022579/4503599627370496), (-9980083218939/9007199254740992)), (132475/9007199254740992), by norm_num⟩
  | 2 => ⟨((561472073823157/1125899906842624), (-9972272884397/2251799813685248)), (66413/1125899906842624), by norm_num⟩
  | 1 => ⟨((560717989909483/562949953421312), (-14938839738921/1125899906842624)), (100059/562949953421312), by norm_num⟩
  | 0 => ⟨((1116851202604929/1125899906842624), (-29799139340253/1125899906842624)), (403757/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116851202604929/1125899906842624), (-29799139340253/1125899906842624)), (1540210728171920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1107086529165941/1125899906842624), (-29559647715119/562949953421312)), (411199/562949953421312), by norm_num⟩
  | 2 => ⟨((542741625850117/562949953421312), (-3633214594989/35184372088832)), (851839/562949953421312), by norm_num⟩
  | 3 => ⟨((1034511885462161/1125899906842624), (-112089355545021/562949953421312)), (1818447/562949953421312), by norm_num⟩
  | 4 => ⟨((905905347764675/1125899906842624), (-411964757578851/1125899906842624)), (8131673/1125899906842624), by norm_num⟩
  | 5 => ⟨((578159331629311/1125899906842624), (-662938285567199/1125899906842624)), (19036309/1125899906842624), by norm_num⟩
  | 6 => ⟨((-11681650948861/140737488355328), (-340424538420881/562949953421312)), (83936123/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-29933855/2097152)), (3/134217728), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((893514451/18014398509481984), (-59391207/9007199254740992)), (631/4503599627370496), by norm_num⟩
  | 1 => ⟨((352923113/9007199254740992), (586421447/18014398509481984)), (6269/18014398509481984), by norm_num⟩
  | 2 => ⟨((95310699/72057594037927936), (914977439/36028797018963968)), (33389/72057594037927936), by norm_num⟩
  | 3 => ⟨((-52113997/9007199254740992), (106842675/18014398509481984)), (62049/144115188075855872), by norm_num⟩
  | 4 => ⟨((-142494795/72057594037927936), (-14824881/288230376151711744)), (90923/288230376151711744), by norm_num⟩
  | 5 => ⟨((-562059737/2305843009213693952), (-318246171/1152921504606846976)), (459807/2305843009213693952), by norm_num⟩
  | 6 => ⟨((96200893/18446744073709551616), (-15931653/288230376151711744)), (2219621/18446744073709551616), by norm_num⟩
  | 7 => ⟨((201628925/36893488147419103232), (-633216239/147573952589676412928)), (5765573/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1716771119/2361183241434822606848), (117125317/1180591620717411303424)), (70110113/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((188811621/4722366482869645213696), (994515755/18889465931478580854784)), (985941605/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-10755747/18889465931478580854784), (96051415/18889465931478580854784)), (940008881/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-9563571/37778931862957161709568), (8700443/37778931862957161709568)), (926087923/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-753007/37778931862957161709568), (30785/18889465931478580854784)), (922260617/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-69/73786976294838206464), (-4581/9444732965739290427392)), (1842593567/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-1205/37778931862957161709568), (-1627/37778931862957161709568)), (460536341/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-23/37778931862957161709568), (-103/37778931862957161709568)), (1842048503/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((1/18889465931478580854784), (-5/37778931862957161709568)), (230253617/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2633753/562949953421312), (555488343/1125899906842624)), (30949/2251799813685248), by norm_num⟩
  | 1 => ⟨((-39376717/70368744177664), (1500164207/1125899906842624)), (41063/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1767706647/2251799813685248), (-271601149/2251799813685248)), (30397/562949953421312), by norm_num⟩
  | 3 => ⟨((-321623113/9007199254740992), (-545176403/4503599627370496)), (148391/2251799813685248), by norm_num⟩
  | 4 => ⟨((-803030075/36028797018963968), (-376860209/18014398509481984)), (2469813/36028797018963968), by norm_num⟩
  | 5 => ⟨((139692295/36028797018963968), (-818598291/72057594037927936)), (4612983/72057594037927936), by norm_num⟩
  | 6 => ⟨((259809199/144115188075855872), (18274711/72057594037927936)), (32399905/576460752303423488), by norm_num⟩
  | 7 => ⟨((3390757/144115188075855872), (976055607/9223372036854775808)), (449563823/9223372036854775808), by norm_num⟩
  | 8 => ⟨((280829043/36893488147419103232), (224276927/36893488147419103232)), (799649533/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-8547509/18446744073709551616), (2145357/1152921504606846976)), (46270603/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-2412851/18446744073709551616), (-85675/36893488147419103232)), (1419772725/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-82579/36893488147419103232), (-29511/36893488147419103232)), (1392197477/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-19041/36893488147419103232), (-5671/36893488147419103232)), (690494551/18446744073709551616), by norm_num⟩
  | 13 => ⟨((1/9223372036854775808), (-155/4611686018427387904)), (688424245/18446744073709551616), by norm_num⟩
  | 14 => ⟨((1/9223372036854775808), (-5/9223372036854775808)), (687722557/18446744073709551616), by norm_num⟩
  | 15 => ⟨((3/36893488147419103232), (-1/36893488147419103232)), (1375005371/36893488147419103232), by norm_num⟩
  | 16 => ⟨(0, (1/36893488147419103232)), (1374877289/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-5267501/1125899906842624), (555488341/1125899906842624)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-630027481/1125899906842624), (1500164217/1125899906842624)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-883853325/1125899906842624), (-67900297/562949953421312)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((-20101441/562949953421312), (-136294091/1125899906842624)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-25094697/1125899906842624), (-11776883/562949953421312)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((4365387/1125899906842624), (-6395299/562949953421312)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((1014879/562949953421312), (285543/1125899906842624)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((26491/1125899906842624), (119147/1125899906842624)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((4285/562949953421312), (6845/1125899906842624)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((-261/562949953421312), (2095/1125899906842624)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-147/1125899906842624), (-3/1125899906842624)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((-3/1125899906842624), (-1/1125899906842624)), (1/4294967296), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨32,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨32,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(161751/1048576)) (K:=(2347/1073741824)) (L:=(582497930177741/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile032
