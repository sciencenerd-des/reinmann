/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile007Gamma
import XiBand97.Tile007Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile007
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((118563379/8796093022208), (-369463813/35184372088832)), (223/8796093022208), by norm_num⟩
  | 1 => ⟨((1579044873/70368744177664), (-112887945/70368744177664)), (3787/70368744177664), by norm_num⟩
  | 2 => ⟨((447981273/35184372088832), (251343477/35184372088832)), (2075/35184372088832), by norm_num⟩
  | 3 => ⟨((204592457/70368744177664), (774492865/140737488355328)), (773/17592186044416), by norm_num⟩
  | 4 => ⟨((-21093679/140737488355328), (1100361977/562949953421312)), (14001/562949953421312), by norm_num⟩
  | 5 => ⟨((-642268407/2251799813685248), (13871075/35184372088832)), (25633/2251799813685248), by norm_num⟩
  | 6 => ⟨((-204849967/2251799813685248), (177917465/4503599627370496)), (39573/9007199254740992), by norm_num⟩
  | 7 => ⟨((-1224128407/72057594037927936), (-132377757/72057594037927936)), (106889/72057594037927936), by norm_num⟩
  | 8 => ⟨((-1205960923/576460752303423488), (-834424107/576460752303423488)), (66589/144115188075855872), by norm_num⟩
  | 9 => ⟨((-723395735/4611686018427387904), (-42371071/144115188075855872)), (43403/288230376151711744), by norm_num⟩
  | 10 => ⟨((-55541749/36893488147419103232), (-359485701/9223372036854775808)), (1222895/18446744073709551616), by norm_num⟩
  | 11 => ⟨((57752373/36893488147419103232), (-564905063/147573952589676412928)), (6748805/147573952589676412928), by norm_num⟩
  | 12 => ⟨((84347409/295147905179352825856), (-667668637/2361183241434822606848)), (48587599/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((629680889/18889465931478580854784), (-532890969/37778931862957161709568)), (1519349311/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((114859363/37778931862957161709568), (-588681/4722366482869645213696)), (1512597571/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((4336975/18889465931478580854784), (2683601/37778931862957161709568)), (1511395691/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((549337/37778931862957161709568), (395951/37778931862957161709568)), (1511194597/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile007Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-3965457/2097152), (1166790705/33554432)), (6957/33554432), by norm_num⟩
  | 1 => ⟨((122444815/33554432), (-505591047/33554432)), (7267/33554432), by norm_num⟩
  | 2 => ⟨((-265458361/134217728), (471291929/67108864)), (29755/134217728), by norm_num⟩
  | 3 => ⟨((131374509/134217728), (-302680999/134217728)), (118131/536870912), by norm_num⟩
  | 4 => ⟨((-5991141/16777216), (73290821/134217728)), (460377/2147483648), by norm_num⟩
  | 5 => ⟨((6812057/67108864), (-13766765/134217728)), (1790563/8589934592), by norm_num⟩
  | 6 => ⟨((-781443/33554432), (3943649/268435456)), (1754147/8589934592), by norm_num⟩
  | 7 => ⟨((4741995/1073741824), (-766581/536870912)), (27738927/137438953472), by norm_num⟩
  | 8 => ⟨((-1508719/2147483648), (66901/2147483648)), (110336699/549755813888), by norm_num⟩
  | 9 => ⟨((404999/4294967296), (98777/4294967296)), (1761332141/8796093022208), by norm_num⟩
  | 10 => ⟨((-182225/17179869184), (-108087/17179869184)), (1759880109/8796093022208), by norm_num⟩
  | 11 => ⟨((4161/4294967296), (37297/34359738368)), (1759407021/8796093022208), by norm_num⟩
  | 12 => ⟨((-8855/137438953472), (-40417/274877906944)), (1759268269/8796093022208), by norm_num⟩
  | 13 => ⟨((103/68719476736), (2281/137438953472)), (1759230725/8796093022208), by norm_num⟩
  | 14 => ⟨((425/1099511627776), (-6995/4398046511104)), (1759221367/8796093022208), by norm_num⟩
  | 15 => ⟨((-723/8796093022208), (1131/8796093022208)), (1759219195/8796093022208), by norm_num⟩
  | 16 => ⟨((93/8796093022208), (-37/4398046511104)), (439804681/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile007Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11351/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11351/640))
  have he : value ((69/80), (11351/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1362501717/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1027280636188787/2251799813685248), (456577037391469/1125899906842624)), (30489995/1125899906842624), by norm_num⟩
  | 1 => ⟨((280370437/1073741824), (-996889839/4294967296)), (69/4294967296), by norm_num⟩
  | 2 => ⟨((-641896837/8589934592), (142646199/2147483648)), (41/8589934592), by norm_num⟩
  | 3 => ⟨((244932831/17179869184), (-870887291/68719476736)), (65/68719476736), by norm_num⟩
  | 4 => ⟨((-1121527727/549755813888), (498465355/274877906944)), (77/549755813888), by norm_num⟩
  | 5 => ⟨((513538523/2199023255552), (-912973103/4398046511104)), (73/4398046511104), by norm_num⟩
  | 6 => ⟨((-783817193/35184372088832), (348369199/17592186044416)), (29/17592186044416), by norm_num⟩
  | 7 => ⟨((512719409/281474976710656), (-911516877/562949953421312)), (79/562949953421312), by norm_num⟩
  | 8 => ⟨((-586925231/4503599627370496), (521720305/4503599627370496)), (47/4503599627370496), by norm_num⟩
  | 9 => ⟨((74652317/9007199254740992), (-530870067/72057594037927936)), (49/72057594037927936), by norm_num⟩
  | 10 => ⟨((-1093846251/2305843009213693952), (486162265/1152921504606846976)), (23/576460752303423488), by norm_num⟩
  | 11 => ⟨((910660723/36893488147419103232), (-25296567/1152921504606846976)), (79/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-694973697/590295810358705651712), (38610315/36893488147419103232)), (31/295147905179352825856), by norm_num⟩
  | 13 => ⟨((979147275/18889465931478580854784), (-6799751/147573952589676412928)), (45/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-320245471/151115727451828646838272), (284667545/151115727451828646838272)), (61/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((391034199/4835703278458516698824704), (-347591943/4835703278458516698824704)), (77/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-223814267/77371252455336267181195264), (795797771/309485009821345068724781056)), (91/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (3145731269969/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890601001649119/316912650057057350374175801344), (1866261401813/316912650057057350374175801344)), (11571/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892478523872505/39614081257132168796771975168), (2099441642055/19807040628566084398385987584)), (26041/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892423778237103/2475880078570760549798248448), (1115271624379/618970019642690137449562112)), (27675/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221761132391569/19342813113834066795298816), (4460830981883/154742504910672534362390528)), (27683/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776134809939343/4835703278458516698824704), (4181757418899/9671406556917033397649408)), (25961/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630582162485189/302231454903657293676544), (3658765956111/604462909807314587353088)), (5681/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945825266717629/37778931862957161709568), (5944984743649/75557863725914323419136)), (18471/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300431631995845/4722366482869645213696), (4458292027353/4722366482869645213696)), (27719/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50794441189017/18446744073709551616), (6129425293701/590295810358705651712)), (4767/73786976294838206464), by norm_num⟩
  | 8 => ⟨((457109502406573/18446744073709551616), (3830345572869/36893488147419103232)), (23851/36893488147419103232), by norm_num⟩
  | 7 => ⟨((914117520721323/4611686018427387904), (8616776345339/9223372036854775808)), (26855/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799738230402169/576460752303423488), (2153724290477/288230376151711744)), (53765/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599688534647867/72057594037927936), (7535917237513/144115188075855872)), (11777/36028797018963968), by norm_num⟩
  | 4 => ⟨((749407967194053/18014398509481984), (5649815531075/18014398509481984)), (17697/9007199254740992), by norm_num⟩
  | 3 => ⟨((749101499291103/4503599627370496), (7058544840653/4503599627370496)), (44353/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122877633487547/2251799813685248), (7052937254097/1125899906842624)), (89037/2251799813685248), by norm_num⟩
  | 1 => ⟨((560651555033903/562949953421312), (21130629011549/1125899906842624)), (134387/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116453390070167/1125899906842624), (42147660271081/1125899906842624)), (136051/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116453390070167/1125899906842624), (42147660271081/1125899906842624)), (518993379833030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((138188543600575/140737488355328), (83588066589567/1125899906842624)), (560011/1125899906842624), by norm_num⟩
  | 2 => ⟨((269820109455419/281474976710656), (82074174545711/562949953421312)), (1182889/1125899906842624), by norm_num⟩
  | 3 => ⟨((252664907430835/281474976710656), (314703111703621/1125899906842624)), (1306367/562949953421312), by norm_num⟩
  | 4 => ⟨((819251190119787/1125899906842624), (282492012313153/562949953421312)), (6151205/1125899906842624), by norm_num⟩
  | 5 => ⟨((312608218804077/1125899906842624), (822211338256139/1125899906842624)), (3781293/281474976710656), by norm_num⟩
  | 6 => ⟨((-1027280636188787/2251799813685248), (456577037391469/1125899906842624)), (30489995/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1362501717/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-266123243/140737488355328), (1443484535/140737488355328)), (3167/140737488355328), by norm_num⟩
  | 1 => ⟨((-1196857275/140737488355328), (557474441/140737488355328)), (8433/140737488355328), by norm_num⟩
  | 2 => ⟨((-993109189/281474976710656), (-575027593/281474976710656)), (23077/281474976710656), by norm_num⟩
  | 3 => ⟨((-97378889/1125899906842624), (-1274049533/1125899906842624)), (42737/562949953421312), by norm_num⟩
  | 4 => ⟨((99857049/562949953421312), (-157443895/1125899906842624)), (239991/4503599627370496), by norm_num⟩
  | 5 => ⟨((579098669/18014398509481984), (387462343/36028797018963968)), (1088071/36028797018963968), by norm_num⟩
  | 6 => ⟨((274547991/288230376151711744), (274322623/72057594037927936)), (4145353/288230376151711744), by norm_num⟩
  | 7 => ⟨((-561358595/2305843009213693952), (576861261/2305843009213693952)), (13671013/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-814520041/36893488147419103232), (-194375535/36893488147419103232)), (160599575/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-36124835/147573952589676412928), (-245057955/295147905179352825856)), (876810089/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-50211305/4722366482869645213696), (42192113/4722366482869645213696)), (1226905695/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-46315195/9444732965739290427392), (-18515965/9444732965739290427392)), (1077143377/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((91095/18889465931478580854784), (-8716855/18889465931478580854784)), (349930769/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((444341/18889465931478580854784), (-9607/2361183241434822606848)), (1210060777/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-305/1180591620717411303424), (2121/2361183241434822606848)), (1165974115/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-223/4722366482869645213696), (-1247/18889465931478580854784)), (1156431693/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((27/4722366482869645213696), (-61/18889465931478580854784)), (577248633/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-776424787/2199023255552), (-374480467/4398046511104)), (7353/2199023255552), by norm_num⟩
  | 1 => ⟨((114281501/4398046511104), (-65224913/274877906944)), (34453/4398046511104), by norm_num⟩
  | 2 => ⟨((669764179/17592186044416), (-172332891/17592186044416)), (382729/35184372088832), by norm_num⟩
  | 3 => ⟨((863573963/140737488355328), (-592075383/70368744177664)), (1664293/140737488355328), by norm_num⟩
  | 4 => ⟨((293412399/70368744177664), (345955439/281474976710656)), (3163335/281474976710656), by norm_num⟩
  | 5 => ⟨((-116182541/1125899906842624), (191110189/281474976710656)), (22269821/2251799813685248), by norm_num⟩
  | 6 => ⟨((-434729431/9007199254740992), (20380251/18014398509481984)), (153606455/18014398509481984), by norm_num⟩
  | 7 => ⟨((-139930549/144115188075855872), (55082511/144115188075855872)), (1083542933/144115188075855872), by norm_num⟩
  | 8 => ⟨((-96893621/288230376151711744), (-19195467/288230376151711744)), (1991414517/288230376151711744), by norm_num⟩
  | 9 => ⟨((-332311/288230376151711744), (-751061/36028797018963968)), (1900395719/288230376151711744), by norm_num⟩
  | 10 => ⟨((-22243/72057594037927936), (-110505/288230376151711744)), (929434001/144115188075855872), by norm_num⟩
  | 11 => ⟨((2341/144115188075855872), (-13955/144115188075855872)), (920943365/144115188075855872), by norm_num⟩
  | 12 => ⟨((495/144115188075855872), (-107/288230376151711744)), (1835583481/288230376151711744), by norm_num⟩
  | 13 => ⟨((27/144115188075855872), (-5/288230376151711744)), (1833438839/288230376151711744), by norm_num⟩
  | 14 => ⟨((-1/72057594037927936), (19/288230376151711744)), (1832764911/288230376151711744), by norm_num⟩
  | 15 => ⟨((-1/72057594037927936), (1/144115188075855872)), (458142007/72057594037927936), by norm_num⟩
  | 16 => ⟨((-1/288230376151711744), 0), (1832514271/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-397529484387/1125899906842624), (-95866996113/1125899906842624)), (1/134217728), by norm_num⟩
  | 1 => ⟨((29256065635/1125899906842624), (-267161237637/1125899906842624)), (1/67108864), by norm_num⟩
  | 2 => ⟨((21432451029/562949953421312), (-5514651825/562949953421312)), (1/33554432), by norm_num⟩
  | 3 => ⟨((863574295/140737488355328), (-592075543/70368744177664)), (1/33554432), by norm_num⟩
  | 4 => ⟨((4694597217/1125899906842624), (345955983/281474976710656)), (1/33554432), by norm_num⟩
  | 5 => ⟨((-116182155/1125899906842624), (11944367/17592186044416)), (1/33554432), by norm_num⟩
  | 6 => ⟨((-54341119/1125899906842624), (637207/562949953421312)), (1/33554432), by norm_num⟩
  | 7 => ⟨((-546653/562949953421312), (6721/17592186044416)), (1/33554432), by norm_num⟩
  | 8 => ⟨((-378459/1125899906842624), (-74911/1125899906842624)), (1/33554432), by norm_num⟩
  | 9 => ⟨((-1325/1125899906842624), (-11739/562949953421312)), (1/33554432), by norm_num⟩
  | 10 => ⟨((-173/562949953421312), (-429/1125899906842624)), (1/33554432), by norm_num⟩
  | 11 => ⟨((15/1125899906842624), (-109/1125899906842624)), (1/33554432), by norm_num⟩
  | 12 => ⟨((1/281474976710656), (-1/1125899906842624)), (1/33554432), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨7,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨7,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(326799/1048576)) (K:=(133943/268435456)) (L:=(107197400680808143/295147905179352825856)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile007
