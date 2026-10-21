/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile006Gamma
import XiBand58.Tile006Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile006
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
  | 0 => ⟨((494190751/35184372088832), (-77560411/4398046511104)), (545/17592186044416), by norm_num⟩
  | 1 => ⟨((989921739/35184372088832), (-313296417/35184372088832)), (149/2199023255552), by norm_num⟩
  | 2 => ⟨((1288209789/70368744177664), (183218571/35184372088832)), (5303/70368744177664), by norm_num⟩
  | 3 => ⟨((186917315/35184372088832), (426608199/70368744177664)), (7945/140737488355328), by norm_num⟩
  | 4 => ⟨((110804009/281474976710656), (1402016075/562949953421312)), (18011/562949953421312), by norm_num⟩
  | 5 => ⟨((-33462317/140737488355328), (1292604443/2251799813685248)), (8237/562949953421312), by norm_num⟩
  | 6 => ⟨((-113141701/1125899906842624), (679995071/9007199254740992)), (25377/4503599627370496), by norm_num⟩
  | 7 => ⟨((-191952019/9007199254740992), (198720273/72057594037927936)), (136387/72057594037927936), by norm_num⟩
  | 8 => ⟨((-427212285/144115188075855872), (-327640351/288230376151711744)), (167505/288230376151711744), by norm_num⟩
  | 9 => ⟨((-79602771/288230376151711744), (-707521063/2305843009213693952)), (418877/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-249642985/18446744073709551616), (-212345969/4611686018427387904)), (1358711/18446744073709551616), by norm_num⟩
  | 11 => ⟨((202082359/295147905179352825856), (-1479216261/295147905179352825856)), (6984875/147573952589676412928), by norm_num⟩
  | 12 => ⟨((586788845/2361183241434822606848), (-497542817/1180591620717411303424)), (48966853/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((40794737/1180591620717411303424), (-127607055/4722366482869645213696)), (760808931/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((66109465/18889465931478580854784), (-21150735/18889465931478580854784)), (1512994847/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((10926973/37778931862957161709568), (287521/37778931862957161709568)), (1511461233/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((191211/9444732965739290427392), (34453/4722366482869645213696)), (1511204833/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile006Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43769763/8388608), (1084960625/33554432)), (1735/8388608), by norm_num⟩
  | 1 => ⟨((222647943/33554432), (-851191871/67108864)), (7193/33554432), by norm_num⟩
  | 2 => ⟨((-221185531/67108864), (755743227/134217728)), (7323/33554432), by norm_num⟩
  | 3 => ⟨((90667505/67108864), (-227310795/134217728)), (116179/536870912), by norm_num⟩
  | 4 => ⟨((-7148309/16777216), (12558661/33554432)), (454313/2147483648), by norm_num⟩
  | 5 => ⟨((28959119/268435456), (-8174023/134217728)), (1775363/8589934592), by norm_num⟩
  | 6 => ⟨((-12059495/536870912), (3480679/536870912)), (1746275/8589934592), by norm_num⟩
  | 7 => ⟨((2094409/536870912), (-54887/536870912)), (27681839/137438953472), by norm_num⟩
  | 8 => ⟨((-38143/67108864), (-153681/1073741824)), (110246587/549755813888), by norm_num⟩
  | 9 => ⟨((593209/8589934592), (351223/8589934592)), (1760831405/8796093022208), by norm_num⟩
  | 10 => ⟨((-58367/8589934592), (-8057/1073741824)), (1759719341/8796093022208), by norm_num⟩
  | 11 => ⟨((33611/68719476736), (74261/68719476736)), (1759361069/8796093022208), by norm_num⟩
  | 12 => ⟨((-3761/274877906944), (-2221/17179869184)), (1759255757/8796093022208), by norm_num⟩
  | 13 => ⟨((-1617/549755813888), (7189/549755813888)), (1759227637/8796093022208), by norm_num⟩
  | 14 => ⟨((1511/2199023255552), (-4883/4398046511104)), (1759220653/8796093022208), by norm_num⟩
  | 15 => ⟨((-103/1099511627776), (667/8796093022208)), (1759219039/8796093022208), by norm_num⟩
  | 16 => ⟨((87/8796093022208), (-31/8796093022208)), (439804673/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile006Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (559/32)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (559/32))
  have he : value ((15/16), (559/32))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-1341975967/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1105888670252573/2251799813685248), (357330589998061/1125899906842624)), (3630735/140737488355328), by norm_num⟩
  | 1 => ⟨((1207298099/4294967296), (-780195247/4294967296)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((-172753777/2147483648), (55819551/1073741824)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((1054700861/68719476736), (-681581955/68719476736)), (63/68719476736), by norm_num⟩
  | 4 => ⟨((-1207347597/549755813888), (390113617/274877906944)), (75/549755813888), by norm_num⟩
  | 5 => ⟨((552834751/2199023255552), (-357259773/2199023255552)), (71/4398046511104), by norm_num⟩
  | 6 => ⟨((-421897641/17592186044416), (545287919/35184372088832)), (7/4398046511104), by norm_num⟩
  | 7 => ⟨((1103905917/562949953421312), (-178344965/140737488355328)), (19/140737488355328), by norm_num⟩
  | 8 => ⟨((-1263674095/9007199254740992), (408313623/4503599627370496)), (89/9007199254740992), by norm_num⟩
  | 9 => ⟨((1285836003/144115188075855872), (-830948991/144115188075855872)), (47/72057594037927936), by norm_num⟩
  | 10 => ⟨((-1177547921/2305843009213693952), (760969715/2305843009213693952)), (11/288230376151711744), by norm_num⟩
  | 11 => ⟨((61271559/2305843009213693952), (-316765373/18446744073709551616)), (19/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-748153437/590295810358705651712), (483481053/590295810358705651712)), (15/147573952589676412928), by norm_num⟩
  | 13 => ⟨((527036061/9444732965739290427392), (-170293911/4722366482869645213696)), (87/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-344750817/151115727451828646838272), (445578353/302231454903657293676544)), (59/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((841912669/9671406556917033397649408), (-272035657/4835703278458516698824704)), (37/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-481881297/154742504910672534362390528), (622814693/309485009821345068724781056)), (87/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (3344938047533/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890567343976569/316912650057057350374175801344), (3968608330971/633825300114114700748351602688)), (23149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946201369727879/19807040628566084398385987584), (4464446993191/39614081257132168796771975168)), (407/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1892343189836023/2475880078570760549798248448), (2371606253127/1237940039285380274899124224)), (27683/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774008394852189/154742504910672534362390528), (4742917096983/154742504910672534362390528)), (27691/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388048479129181/2417851639229258349412352), (4446170737415/9671406556917033397649408)), (25969/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261098003954961/604462909807314587353088), (1945042582315/302231454903657293676544)), (5683/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891542610763563/75557863725914323419136), (395049925461/4722366482869645213696)), (36955/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162543819737777/590295810358705651712), (74063793999/73786976294838206464)), (27731/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625310426625247/590295810358705651712), (1629193536703/147573952589676412928)), (4769/73786976294838206464), by norm_num⟩
  | 8 => ⟨((457074518427007/18446744073709551616), (2036176694047/18446744073709551616)), (11931/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828077171569773/9223372036854775808), (9161059232483/9223372036854775808)), (26869/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599318038909353/1152921504606846976), (9158886156663/1152921504606846976)), (26899/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199237829710087/144115188075855872), (2002894065873/36028797018963968)), (11785/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498605835650007/36028797018963968), (750778445385/2251799813685248)), (17711/9007199254740992), by norm_num⟩
  | 3 => ⟨((1497938209650711/9007199254740992), (7503476459353/4503599627370496)), (88789/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122609603047999/2251799813685248), (7496989738501/1125899906842624)), (89143/2251799813685248), by norm_num⟩
  | 1 => ⟨((560446492172937/562949953421312), (22458362858943/1125899906842624)), (134597/1125899906842624), by norm_num⟩
  | 0 => ⟨((139450120141505/140737488355328), (44785266593661/1125899906842624)), (272737/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((139450120141505/140737488355328), (44785266593661/1125899906842624)), (1040409092429732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1103614785668997/1125899906842624), (88751204530345/1125899906842624)), (562183/1125899906842624), by norm_num⟩
  | 2 => ⟨((537387387407779/562949953421312), (173989074819797/1125899906842624)), (595371/562949953421312), by norm_num⟩
  | 3 => ⟨((999084031881367/1125899906842624), (332177074664157/1125899906842624)), (2641365/1125899906842624), by norm_num⟩
  | 4 => ⟨((788549042798695/1125899906842624), (294762268863401/562949953421312)), (6246287/1125899906842624), by norm_num⟩
  | 5 => ⟨((487202122763965/2251799813685248), (1651546490431645/2251799813685248)), (30581203/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1105888670252573/2251799813685248), (357330589998061/1125899906842624)), (3630735/140737488355328), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-1341975967/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-91557547/70368744177664), (1846282031/140737488355328)), (3641/140737488355328), by norm_num⟩
  | 1 => ⟨((-180264785/17592186044416), (12740749/2199023255552)), (2483/35184372088832), by norm_num⟩
  | 2 => ⟨((-1284992251/281474976710656), (-622741677/281474976710656)), (27503/281474976710656), by norm_num⟩
  | 3 => ⟨((-56586789/281474976710656), (-1558247949/1125899906842624)), (12825/140737488355328), by norm_num⟩
  | 4 => ⟨((230985197/1125899906842624), (-103216601/562949953421312)), (72273/1125899906842624), by norm_num⟩
  | 5 => ⟨((1414095155/36028797018963968), (388603785/36028797018963968)), (656051/18014398509481984), by norm_num⟩
  | 6 => ⟨((1495961/1125899906842624), (1276549597/288230376151711744)), (2498431/144115188075855872), by norm_num⟩
  | 7 => ⟨((-619288617/2305843009213693952), (683627447/2305843009213693952)), (16449089/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-222958865/9223372036854775808), (-193873527/36893488147419103232)), (96164019/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-252590929/1180591620717411303424), (-915662535/1180591620717411303424)), (518270291/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-102831975/4722366482869645213696), (112569877/4722366482869645213696)), (349908075/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-30767823/4722366482869645213696), (-11574235/4722366482869645213696)), (571299377/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((90851/4722366482869645213696), (-5207551/9444732965739290427392)), (688942347/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((251623/9444732965739290427392), (-13525/9444732965739290427392)), (1149992759/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-12143/18889465931478580854784), (19083/18889465931478580854784)), (548528013/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-1003/18889465931478580854784), (-467/4722366482869645213696)), (1085605873/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((147/18889465931478580854784), (-15/4722366482869645213696)), (1083286323/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-114732171/274877906944), (-60759249/549755813888)), (8695/2199023255552), by norm_num⟩
  | 1 => ⟨((105052373/4398046511104), (-1134721993/4398046511104)), (5255/549755813888), by norm_num⟩
  | 2 => ⟨((137542157/4398046511104), (-320532703/17592186044416)), (466229/35184372088832), by norm_num⟩
  | 3 => ⟨((159298787/17592186044416), (-909247721/70368744177664)), (253687/17592186044416), by norm_num⟩
  | 4 => ⟨((1431744201/281474976710656), (464039833/281474976710656)), (3856203/281474976710656), by norm_num⟩
  | 5 => ⟨((-136312385/1125899906842624), (852202759/1125899906842624)), (27155777/2251799813685248), by norm_num⟩
  | 6 => ⟨((-427737187/9007199254740992), (132355433/36028797018963968)), (187642783/18014398509481984), by norm_num⟩
  | 7 => ⟨((-96605587/72057594037927936), (160233819/144115188075855872)), (1327694445/144115188075855872), by norm_num⟩
  | 8 => ⟨((-6965789/18014398509481984), (-10922015/144115188075855872)), (1224060799/144115188075855872), by norm_num⟩
  | 9 => ⟨((-387769/144115188075855872), (-2879921/144115188075855872)), (1171060659/144115188075855872), by norm_num⟩
  | 10 => ⟨((-86579/144115188075855872), (-72635/144115188075855872)), (4481315/562949953421312), by norm_num⟩
  | 11 => ⟨((911/72057594037927936), (-7839/72057594037927936)), (568804369/72057594037927936), by norm_num⟩
  | 12 => ⟨((391/144115188075855872), (-247/144115188075855872)), (567047907/72057594037927936), by norm_num⟩
  | 13 => ⟨((17/72057594037927936), (-49/144115188075855872)), (1132918609/144115188075855872), by norm_num⟩
  | 14 => ⟨((3/72057594037927936), (3/144115188075855872)), (1132554171/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1/144115188075855872), 0), (1132449235/144115188075855872), by norm_num⟩
  | 16 => ⟨(0, 0), (141552621/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-469942970793/1125899906842624), (-124434956261/1125899906842624)), (1/134217728), by norm_num⟩
  | 1 => ⟨((26893417141/1125899906842624), (-290488828943/1125899906842624)), (1/33554432), by norm_num⟩
  | 2 => ⟨((17605395489/562949953421312), (-10257044859/562949953421312)), (1/33554432), by norm_num⟩
  | 3 => ⟨((5097561065/562949953421312), (-14547965169/1125899906842624)), (1/16777216), by norm_num⟩
  | 4 => ⟨((5726977443/1125899906842624), (1856160611/1125899906842624)), (1/16777216), by norm_num⟩
  | 5 => ⟨((-136313153/1125899906842624), (426101273/562949953421312)), (1/16777216), by norm_num⟩
  | 6 => ⟨((-53467035/1125899906842624), (517027/140737488355328)), (1/16777216), by norm_num⟩
  | 7 => ⟨((-1509633/1125899906842624), (1251775/1125899906842624)), (1/16777216), by norm_num⟩
  | 8 => ⟨((-435329/1125899906842624), (-42677/562949953421312)), (1/16777216), by norm_num⟩
  | 9 => ⟨((-379/140737488355328), (-22499/1125899906842624)), (1/16777216), by norm_num⟩
  | 10 => ⟨((-671/1125899906842624), (-283/562949953421312)), (1/16777216), by norm_num⟩
  | 11 => ⟨((7/562949953421312), (-15/140737488355328)), (1/16777216), by norm_num⟩
  | 12 => ⟨((3/1125899906842624), (-1/1125899906842624)), (1/16777216), by norm_num⟩
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
    (r:=(163873/524288)) (K:=(570075/1073741824)) (L:=(509752962052879249/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile006
