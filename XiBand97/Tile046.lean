/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import XiBand97.Tile046Gamma
import XiBand97.Tile046Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile046
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨46,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1262439871/288230376151711744), (1501675763/1152921504606846976)), (27375/576460752303423488), by norm_num⟩
  | 1 => ⟨((700860923/144115188075855872), (2903252015/576460752303423488)), (2059/36028797018963968), by norm_num⟩
  | 2 => ⟨((392503617/288230376151711744), (2971045199/576460752303423488)), (17193/288230376151711744), by norm_num⟩
  | 3 => ⟨((-1514536383/2305843009213693952), (751736835/288230376151711744)), (126899/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-3168845659/4611686018427387904), (1711641743/2305843009213693952)), (112169/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-2640237897/9223372036854775808), (1803654965/18446744073709551616)), (811473/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-5458207075/73786976294838206464), (-880952495/73786976294838206464)), (1532585/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-933805609/73786976294838206464), (-699794623/73786976294838206464)), (5978587/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-46699005/36893488147419103232), (-3085189689/1180591620717411303424)), (23700365/590295810358705651712), by norm_num⟩
  | 9 => ⟨((20740997/2361183241434822606848), (-2224897087/4722366482869645213696)), (94540011/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1196510351/37778931862957161709568), (-4585214605/75557863725914323419136)), (3023017517/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1093982493/151115727451828646838272), (-403167157/75557863725914323419136)), (1511233493/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((19999163/18889465931478580854784), (-15278991/75557863725914323419136)), (6044690087/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((8693533/75557863725914323419136), (2212213/75557863725914323419136)), (377790027/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((1423263/151115727451828646838272), (1146677/151115727451828646838272)), (3022315533/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((19715/37778931862957161709568), (77091/75557863725914323419136)), (1511157355/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((239/37778931862957161709568), (3827/37778931862957161709568)), (6044629149/151115727451828646838272), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile046Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((265393919/8388608), (2713560249/67108864)), (6901/33554432), by norm_num⟩
  | 1 => ⟨((-1152837471/33554432), (-40042935/4194304)), (28533/134217728), by norm_num⟩
  | 2 => ⟨((6029149591/268435456), (1110474575/268435456)), (7253/33554432), by norm_num⟩
  | 3 => ⟨((-698436489/67108864), (-779899191/536870912)), (115221/536870912), by norm_num⟩
  | 4 => ⟨((2042702215/536870912), (286351745/536870912)), (225809/1073741824), by norm_num⟩
  | 5 => ⟨((-612071405/536870912), (-218445749/1073741824)), (442299/2147483648), by norm_num⟩
  | 6 => ⟨((77063911/268435456), (152190047/2147483648)), (1743167/8589934592), by norm_num⟩
  | 7 => ⟨((-265785479/4294967296), (-45399113/2147483648)), (1728745/8589934592), by norm_num⟩
  | 8 => ⟨((49708425/4294967296), (46063503/8589934592)), (27552879/137438953472), by norm_num⟩
  | 9 => ⟨((-8139377/4294967296), (-20110409/17179869184)), (110039515/549755813888), by norm_num⟩
  | 10 => ⟨((9375833/34359738368), (7668807/34359738368)), (1759653549/8796093022208), by norm_num⟩
  | 11 => ⟨((-1185355/34359738368), (-10353483/274877906944)), (3518681881/17592186044416), by norm_num⟩
  | 12 => ⟨((2082009/549755813888), (1563181/274877906944)), (3518500841/17592186044416), by norm_num⟩
  | 13 => ⟨((-1537713/4398046511104), (-425825/549755813888)), (3518452521/17592186044416), by norm_num⟩
  | 14 => ⟨((216683/8796093022208), (1684655/17592186044416)), (3518440647/17592186044416), by norm_num⟩
  | 15 => ⟨((-13591/17592186044416), (-189827/17592186044416)), (7036875865/35184372088832), by norm_num⟩
  | 16 => ⟨((-2283/17592186044416), (39067/35184372088832)), (7036874705/35184372088832), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile046Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36843/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36843/1280))
  have he : value ((69/80), (36843/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-2211199487/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-989841582321659/2251799813685248), (953608678488277/2251799813685248)), (7623295/562949953421312), by norm_num⟩
  | 1 => ⟨((4322438207/17179869184), (-4164216437/17179869184)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((-2474012097/34359738368), (2383451503/34359738368)), (5/2147483648), by norm_num⟩
  | 3 => ⟨((944025195/68719476736), (-909469389/68719476736)), (125/274877906944), by norm_num⟩
  | 4 => ⟨((-2161307707/1099511627776), (4164387159/2199023255552)), (73/1099511627776), by norm_num⟩
  | 5 => ⟨((3958581639/17592186044416), (-3813678749/17592186044416)), (17/2199023255552), by norm_num⟩
  | 6 => ⟨((-377625559/17592186044416), (2910421359/140737488355328)), (53/70368744177664), by norm_num⟩
  | 7 => ⟨((3952267547/2251799813685248), (-3807595783/2251799813685248)), (71/1125899906842624), by norm_num⟩
  | 8 => ⟨((-2262139389/18014398509481984), (2179334343/18014398509481984)), (83/18014398509481984), by norm_num⟩
  | 9 => ⟨((2301812057/288230376151711744), (-2217554803/288230376151711744)), (43/144115188075855872), by norm_num⟩
  | 10 => ⟨((-4215924885/9223372036854775808), (2030801005/4611686018427387904)), (5/288230376151711744), by norm_num⟩
  | 11 => ⟨((3509887427/147573952589676412928), (-845352219/36893488147419103232)), (17/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-1339291011/1180591620717411303424), (1290266599/1180591620717411303424)), (53/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((3773849713/75557863725914323419136), (-1817854445/37778931862957161709568)), (19/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-1234296729/604462909807314587353088), (2378231213/1208925819614629174706176)), (51/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((3014264221/38685626227668133590597632), (-1451963917/19342813113834066795298816)), (127/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-3450518337/1237940039285380274899124224), (1662106489/618970019642690137449562112)), (37/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (193343059233/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781202247662603/633825300114114700748351602688), (917633854359/158456325028528675187087900672)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236559851712721/4951760157141521099596496896), (2064575721861/19807040628566084398385987584)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946212052135301/1237940039285380274899124224), (4387000256589/2475880078570760549798248448)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887044702758315/77371252455336267181195264), (548343633539/19342813113834066795298816)), (13841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552269966232909/9671406556917033397649408), (1028077557581/2417851639229258349412352)), (3245/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261164649645721/604462909807314587353088), (3598004280027/604462909807314587353088)), (5681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891651101553575/75557863725914323419136), (5846255689213/75557863725914323419136)), (18469/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650216046766183/2361183241434822606848), (2192126420087/2361183241434822606848)), (13859/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406355702562225/147573952589676412928), (3013816900587/295147905179352825856)), (9533/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457109740307975/18446744073709551616), (7533470424173/73786976294838206464)), (2981/9223372036854775808), by norm_num⟩
  | 7 => ⟨((914118115347249/4611686018427387904), (8473678765561/9223372036854775808)), (6713/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599477798361281/1152921504606846976), (264744746611/36028797018963968)), (26879/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199378406412621/144115188075855872), (115793307383/2251799813685248)), (23551/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498818273350281/36028797018963968), (1388998287935/4503599627370496)), (35387/36028797018963968), by norm_num⟩
  | 3 => ⟨((374551626258775/2251799813685248), (6941331813777/4503599627370496)), (22171/4503599627370496), by norm_num⟩
  | 2 => ⟨((280720503264475/562949953421312), (13871645521533/2251799813685248)), (44505/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121311858670831/1125899906842624), (20779785973783/1125899906842624)), (33583/562949953421312), by norm_num⟩
  | 0 => ⟨((1116479582838955/1125899906842624), (41448022501071/1125899906842624)), (4249/35184372088832), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116479582838955/1125899906842624), (41448022501071/1125899906842624)), (16208648815858353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((138201530256121/140737488355328), (10275307465223/140737488355328)), (34959/140737488355328), by norm_num⟩
  | 2 => ⟨((539844251694281/562949953421312), (80721248170105/562949953421312)), (73763/140737488355328), by norm_num⟩
  | 3 => ⟨((506112300835359/562949953421312), (154816255155121/562949953421312)), (650499/562949953421312), by norm_num⟩
  | 4 => ⟨((824874704351705/1125899906842624), (556741576241907/1125899906842624)), (3054861/1125899906842624), by norm_num⟩
  | 5 => ⟨((329031997348563/1125899906842624), (203944436051471/281474976710656)), (3748687/562949953421312), by norm_num⟩
  | 6 => ⟨((-989841582321659/2251799813685248), (953608678488277/2251799813685248)), (7623295/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-2211199487/134217728)), (1/134217728), by norm_num⟩, -3, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-2855703655/1152921504606846976), (369601389/288230376151711744)), (47343/1152921504606846976), by norm_num⟩
  | 1 => ⟨((-1644570175/576460752303423488), (-512076503/576460752303423488)), (84119/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-107023565/144115188075855872), (-801552771/576460752303423488)), (199701/2305843009213693952), by norm_num⟩
  | 3 => ⟨((1420279081/9223372036854775808), (-4826918691/9223372036854775808)), (797321/9223372036854775808), by norm_num⟩
  | 4 => ⟨((2239983433/18446744073709551616), (-626893083/9223372036854775808)), (1464543/18446744073709551616), by norm_num⟩
  | 5 => ⟨((3974531137/147573952589676412928), (1060973751/147573952589676412928)), (1321801/18446744073709551616), by norm_num⟩
  | 6 => ⟨((1391424495/590295810358705651712), (4610072693/1180591620717411303424)), (39084317/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-1278873837/9444732965739290427392), (5773099713/9444732965739290427392)), (597480239/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-4583255061/75557863725914323419136), (3131190661/75557863725914323419136)), (1170002333/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-279391763/37778931862957161709568), (-80955995/75557863725914323419136)), (4641655757/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-32316307/75557863725914323419136), (-9642713/18889465931478580854784)), (2314350473/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((13565/18889465931478580854784), (-3962681/75557863725914323419136)), (2312393085/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((179077/75557863725914323419136), (-53155/18889465931478580854784)), (2311856923/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((1069/4722366482869645213696), (-945/18889465931478580854784)), (1155861213/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((927/75557863725914323419136), (385/75557863725914323419136)), (288961409/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((31/75557863725914323419136), (43/75557863725914323419136)), (2311684563/37778931862957161709568), by norm_num⟩
  | 16 => ⟨(0, (3/75557863725914323419136)), (4623366425/75557863725914323419136), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-4691459995/36028797018963968), (-2146812699/36028797018963968)), (67243/18014398509481984), by norm_num⟩
  | 1 => ⟨((774692191/18014398509481984), (-46125289/281474976710656)), (155465/18014398509481984), by norm_num⟩
  | 2 => ⟨((4419156903/72057594037927936), (82563567/36028797018963968)), (453391/36028797018963968), by norm_num⟩
  | 3 => ⟨((3177684419/576460752303423488), (1747227979/576460752303423488)), (8455907/576460752303423488), by norm_num⟩
  | 4 => ⟨((4229377393/1152921504606846976), (1103711309/576460752303423488)), (17411371/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-128623381/576460752303423488), (4914821005/4611686018427387904)), (67149541/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-1000462755/9223372036854775808), (462316057/36893488147419103232)), (506188633/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-127993791/18446744073709551616), (2437261929/590295810358705651712)), (3831558703/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1394316157/590295810358705651712), (-248097549/295147905179352825856)), (920749715/73786976294838206464), by norm_num⟩
  | 9 => ⟨((527923/18446744073709551616), (-154998177/590295810358705651712)), (1798758307/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1275443/147573952589676412928), (-1195201/295147905179352825856)), (7108787213/590295810358705651712), by norm_num⟩
  | 11 => ⟨((332431/590295810358705651712), (-579955/590295810358705651712)), (441863137/36893488147419103232), by norm_num⟩
  | 12 => ⟨((38661/295147905179352825856), (423/18446744073709551616)), (7053806039/590295810358705651712), by norm_num⟩
  | 13 => ⟨((551/590295810358705651712), (1511/295147905179352825856)), (7047776205/590295810358705651712), by norm_num⟩
  | 14 => ⟨((53/295147905179352825856), (85/590295810358705651712)), (3522838697/295147905179352825856), by norm_num⟩
  | 15 => ⟨((-3/590295810358705651712), (1/36893488147419103232)), (3522500311/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-1/590295810358705651712), 0), (1761199991/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-36652031/281474976710656), (-8385987/140737488355328)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((12104565/281474976710656), (-184501155/1125899906842624)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((69049327/1125899906842624), (2580111/1125899906842624)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((3103207/562949953421312), (3412555/1125899906842624)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((4130251/1125899906842624), (1077843/562949953421312)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-125609/562949953421312), (299977/281474976710656)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((-122127/1125899906842624), (14109/1125899906842624)), (1/34359738368), by norm_num⟩
  | 7 => ⟨((-1953/281474976710656), (4649/1125899906842624)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-2659/1125899906842624), (-473/562949953421312)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((1/35184372088832), (-37/140737488355328)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((5/562949953421312), (-5/1125899906842624)), (1/34359738368), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨46,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨46,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(361/1073741824)) (L:=(84530328123583/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile046
