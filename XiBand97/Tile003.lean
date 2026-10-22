/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile003Gamma
import XiBand97.Tile003Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile003
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1528885209/17592186044416), (-40485935/4398046511104)), (959/8796093022208), by norm_num⟩
  | 1 => ⟨((-363186199/4398046511104), (-637777865/8796093022208)), (2167/8796093022208), by norm_num⟩
  | 2 => ⟨((-288812213/17592186044416), (-1157991835/17592186044416)), (4839/17592186044416), by norm_num⟩
  | 3 => ⟨((165278705/17592186044416), (-905347919/35184372088832)), (7205/35184372088832), by norm_num⟩
  | 4 => ⟨((459078683/70368744177664), (-341944883/70368744177664)), (16211/140737488355328), by norm_num⟩
  | 5 => ⟨((1063603691/562949953421312), (-20478173/140737488355328)), (14745/281474976710656), by norm_num⟩
  | 6 => ⟨((726230135/2251799813685248), (91202369/562949953421312)), (11309/562949953421312), by norm_num⟩
  | 7 => ⟨((18086785/562949953421312), (868101915/18014398509481984)), (120611/18014398509481984), by norm_num⟩
  | 8 => ⟨((115412615/144115188075855872), (1150278599/144115188075855872)), (143665/72057594037927936), by norm_num⟩
  | 9 => ⟨((-49153953/144115188075855872), (1058356539/1152921504606846976)), (639961/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-347743443/4611686018427387904), (705420941/9223372036854775808)), (1507337/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1461683659/147573952589676412928), (309857233/73786976294838206464)), (9909621/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-18373317/18446744073709551616), (21273117/590295810358705651712)), (53749583/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-1550719769/18889465931478580854784), (-490984839/18889465931478580854784)), (775391795/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-53232605/9444732965739290427392), (-19420267/4722366482869645213696)), (379551743/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-5965393/18889465931478580854784), (-2026433/4722366482869645213696)), (756169551/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-492207/37778931862957161709568), (-1370581/37778931862957161709568)), (377836199/9444732965739290427392), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile003Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-819042957/67108864), (651987815/67108864)), (13871/67108864), by norm_num⟩
  | 1 => ⟨((674183809/67108864), (219795347/33554432)), (14429/67108864), by norm_num⟩
  | 2 => ⟨((-444411557/134217728), (-488152281/134217728)), (14711/67108864), by norm_num⟩
  | 3 => ⟨((99301167/134217728), (89366423/67108864)), (116783/536870912), by norm_num⟩
  | 4 => ⟨((-3105781/33554432), (-48399097/134217728)), (456313/2147483648), by norm_num⟩
  | 5 => ⟨((-272465/134217728), (20460109/268435456)), (1780515/8589934592), by norm_num⟩
  | 6 => ⟨((2316819/536870912), (-6905791/536870912)), (1749027/8589934592), by norm_num⟩
  | 7 => ⟨((-1371981/1073741824), (1853813/1073741824)), (110807227/549755813888), by norm_num⟩
  | 8 => ⟨((542809/2147483648), (-376483/2147483648)), (882230743/4398046511104), by norm_num⟩
  | 9 => ⟨((-10447/268435456), (22907/2147483648)), (1761016749/8796093022208), by norm_num⟩
  | 10 => ⟨((20961/4294967296), (3405/8589934592)), (1759776685/8796093022208), by norm_num⟩
  | 11 => ⟨((-34473/68719476736), (-16127/68719476736)), (1759377581/8796093022208), by norm_num⟩
  | 12 => ⟨((11251/274877906944), (5793/137438953472)), (1759260141/8796093022208), by norm_num⟩
  | 13 => ⟨((-2539/1099511627776), (-5935/1099511627776)), (1759228733/8796093022208), by norm_num⟩
  | 14 => ⟨((23/1099511627776), (2431/4398046511104)), (1759220901/8796093022208), by norm_num⟩
  | 15 => ⟨((69/4398046511104), (-51/1099511627776)), (879609547/4398046511104), by norm_num⟩
  | 16 => ⟨((-11/4398046511104), (27/8796093022208)), (109951169/549755813888), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile003Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9919/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9919/640))
  have he : value ((69/80), (9919/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-1190613561/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-584435664762105/1125899906842624), (-723115263839291/2251799813685248)), (60507925/2251799813685248), by norm_num⟩
  | 1 => ⟨((319014059/1073741824), (394712283/2147483648)), (69/4294967296), by norm_num⟩
  | 2 => ⟨((-730369855/8589934592), (-451838947/8589934592)), (41/8589934592), by norm_num⟩
  | 3 => ⟨((278692067/17179869184), (689644729/68719476736)), (65/68719476736), by norm_num⟩
  | 4 => ⟨((-1276108553/549755813888), (-197364233/137438953472)), (77/549755813888), by norm_num⟩
  | 5 => ⟨((1168639679/4398046511104), (722971955/4398046511104)), (73/4398046511104), by norm_num⟩
  | 6 => ⟨((-445925589/17592186044416), (-551738403/35184372088832)), (29/17592186044416), by norm_num⟩
  | 7 => ⟨((583387827/281474976710656), (180454697/140737488355328)), (39/281474976710656), by norm_num⟩
  | 8 => ⟨((-667821481/4503599627370496), (-206571885/2251799813685248)), (47/4503599627370496), by norm_num⟩
  | 9 => ⟨((339766759/36028797018963968), (52548669/9007199254740992)), (25/36028797018963968), by norm_num⟩
  | 10 => ⟨((-1244611723/2305843009213693952), (-96246451/288230376151711744)), (47/1152921504606846976), by norm_num⟩
  | 11 => ⟨((518088813/18446744073709551616), (641025099/36893488147419103232)), (5/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-790762331/590295810358705651712), (-61150049/73786976294838206464)), (63/590295810358705651712), by norm_num⟩
  | 13 => ⟨((1114103721/18889465931478580854784), (689233611/18889465931478580854784)), (91/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-364385093/151115727451828646838272), (-225424661/151115727451828646838272)), (61/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((444930673/4835703278458516698824704), (275253703/4835703278458516698824704)), (19/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((-1018650877/309485009821345068724781056), (-78772785/38685626227668133590597632)), (89/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-1685303966219/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781200904714527/633825300114114700748351602688), (-3999347016705/633825300114114700748351602688)), (23149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473119305223303/9903520314283042199192993792), (-4499043102385/39614081257132168796771975168)), (26049/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892422312496295/2475880078570760549798248448), (-597498716997/309485009821345068724781056)), (6921/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((887043750951143/77371252455336267181195264), (-4779715543439/154742504910672534362390528)), (6923/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552268062782799/9671406556917033397649408), (-4480691815399/9671406556917033397649408)), (12985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261162865335869/604462909807314587353088), (-3920313632913/604462909807314587353088)), (22733/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472911994840219/18889465931478580854784), (-6369962282853/75557863725914323419136)), (36957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650214778539399/2361183241434822606848), (-4776992340289/4722366482869645213696)), (6933/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625419006143165/590295810358705651712), (-1641896174175/147573952589676412928)), (38155/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457108432880353/18446744073709551616), (-4104154914427/36893488147419103232)), (2983/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1828229694960743/9223372036854775808), (-9232736124947/9223372036854775808)), (53741/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599470447595057/1152921504606846976), (-4615358605955/576460752303423488)), (26901/576460752303423488), by norm_num⟩
  | 5 => ⟨((599685529034549/72057594037927936), (-8074601649797/144115188075855872)), (5893/18014398509481984), by norm_num⟩
  | 4 => ⟨((187350677401703/4503599627370496), (-12107339080567/36028797018963968)), (70851/36028797018963968), by norm_num⟩
  | 3 => ⟨((749093617396331/4503599627370496), (-15126161901639/9007199254740992)), (88801/9007199254740992), by norm_num⟩
  | 2 => ⟨((35089310766083/70368744177664), (-3778523008381/562949953421312)), (89157/2251799813685248), by norm_num⟩
  | 1 => ⟨((140157972458073/140737488355328), (-5660195477127/281474976710656)), (134625/1125899906842624), by norm_num⟩
  | 0 => ⟨((558167819161175/562949953421312), (-22579526550209/562949953421312)), (136409/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558167819161175/562949953421312), (-22579526550209/562949953421312)), (520359041454124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1105041318282611/1125899906842624), (-22387718509659/281474976710656)), (562887/1125899906842624), by norm_num⟩
  | 2 => ⟨((1077446537385895/1125899906842624), (-87891841272571/562949953421312)), (1194459/1125899906842624), by norm_num⟩
  | 3 => ⟨((501816871556803/562949953421312), (-5256837190193/17592186044416)), (2659087/1125899906842624), by norm_num⟩
  | 4 => ⟨((794111838477107/1125899906842624), (-37487802630183/70368744177664)), (6329811/1125899906842624), by norm_num⟩
  | 5 => ⟨((481122276993355/2251799813685248), (-846100302485455/1125899906842624)), (3918301/281474976710656), by norm_num⟩
  | 6 => ⟨((-584435664762105/1125899906842624), (-723115263839291/2251799813685248)), (60507925/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-1190613561/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((185403481/4398046511104), (575029635/17592186044416)), (829/8796093022208), by norm_num⟩
  | 1 => ⟨((-39997367/8796093022208), (1599018501/35184372088832)), (4665/17592186044416), by norm_num⟩
  | 2 => ⟨((-1190545879/70368744177664), (284076505/35184372088832)), (6505/17592186044416), by norm_num⟩
  | 3 => ⟨((-567008263/140737488355328), (-773256649/281474976710656)), (96885/281474976710656), by norm_num⟩
  | 4 => ⟨((94506171/1125899906842624), (-500568909/562949953421312)), (271813/1125899906842624), by norm_num⟩
  | 5 => ⟨((252015841/2251799813685248), (-100303251/2251799813685248)), (1227615/9007199254740992), by norm_num⟩
  | 6 => ⟨((622612501/72057594037927936), (301535131/36028797018963968)), (4654363/72057594037927936), by norm_num⟩
  | 7 => ⟨((-214956237/576460752303423488), (220360117/288230376151711744)), (15250575/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1207663443/36893488147419103232), (-355914719/18446744073709551616)), (353304385/36893488147419103232), by norm_num⟩
  | 9 => ⟨((110947391/36893488147419103232), (-2538229/147573952589676412928)), (1848474891/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-43454233/590295810358705651712), (231327501/590295810358705651712)), (141406851/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-9658029/295147905179352825856), (-7147221/1180591620717411303424)), (1417584125/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((473151/590295810358705651712), (-18679243/9444732965739290427392)), (1124115505/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((1920919/18889465931478580854784), (1063213/9444732965739290427392)), (1383042771/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-109335/9444732965739290427392), (11259/2361183241434822606848)), (1180551001/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-2403/18889465931478580854784), (-4363/4722366482869645213696)), (284096019/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((1191/18889465931478580854784), (211/18889465931478580854784)), (1127354817/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1829724715/2199023255552), (5843709/549755813888)), (19281/1099511627776), by norm_num⟩
  | 1 => ⟨((-1553779409/8796093022208), (24937975/4398046511104)), (18583/549755813888), by norm_num⟩
  | 2 => ⟨((-1038082025/4398046511104), (-107404499/1099511627776)), (200035/4398046511104), by norm_num⟩
  | 3 => ⟨((184844427/8796093022208), (-391193927/4398046511104)), (874919/17592186044416), by norm_num⟩
  | 4 => ⟨((1021817817/70368744177664), (64046699/35184372088832)), (3383383/70368744177664), by norm_num⟩
  | 5 => ⟨((13006621/281474976710656), (1148981957/1125899906842624)), (49066187/1125899906842624), by norm_num⟩
  | 6 => ⟨((361787687/18014398509481984), (402465485/18014398509481984)), (1401349205/36028797018963968), by norm_num⟩
  | 7 => ⟨((-24865317/18014398509481984), (79771429/9007199254740992)), (1276273741/36028797018963968), by norm_num⟩
  | 8 => ⟨((-8772293/18014398509481984), (466911/9007199254740992)), (1201628033/36028797018963968), by norm_num⟩
  | 9 => ⟨((-89747/9007199254740992), (71275/4503599627370496)), (72737089/2251799813685248), by norm_num⟩
  | 10 => ⟨((-102295/36028797018963968), (-959/4503599627370496)), (1147006027/36028797018963968), by norm_num⟩
  | 11 => ⟨((-1013/36028797018963968), (-1773/36028797018963968)), (1140352779/36028797018963968), by norm_num⟩
  | 12 => ⟨((-187/18014398509481984), (-13/9007199254740992)), (284490663/9007199254740992), by norm_num⟩
  | 13 => ⟨((5/18014398509481984), (-3/9007199254740992)), (568587853/18014398509481984), by norm_num⟩
  | 14 => ⟨((-5/36028797018963968), (1/9007199254740992)), (1136936077/36028797018963968), by norm_num⟩
  | 15 => ⟨(0, 0), (568434051/18014398509481984), by norm_num⟩
  | 16 => ⟨(0, 0), (1136850031/36028797018963968), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-936819043367/1125899906842624), (11967931579/1125899906842624)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-198883763529/1125899906842624), (6384124257/1125899906842624)), (1/16777216), by norm_num⟩
  | 2 => ⟨((-66437251299/281474976710656), (-6873887313/70368744177664)), (1/8388608), by norm_num⟩
  | 3 => ⟨((23660091759/1125899906842624), (-100145652847/1125899906842624)), (1/8388608), by norm_num⟩
  | 4 => ⟨((16349081681/1125899906842624), (512375245/281474976710656)), (1/4194304), by norm_num⟩
  | 5 => ⟨((6503545/140737488355328), (574488299/562949953421312)), (1/4194304), by norm_num⟩
  | 6 => ⟨((11306273/562949953421312), (25156483/1125899906842624)), (1/4194304), by norm_num⟩
  | 7 => ⟨((-777099/562949953421312), (9970911/1125899906842624)), (1/4194304), by norm_num⟩
  | 8 => ⟨((-548285/1125899906842624), (14697/281474976710656)), (1/4194304), by norm_num⟩
  | 9 => ⟨((-11393/1125899906842624), (2213/140737488355328)), (1/4194304), by norm_num⟩
  | 10 => ⟨((-797/281474976710656), (-263/1125899906842624)), (1/4194304), by norm_num⟩
  | 11 => ⟨((-17/562949953421312), (-69/1125899906842624)), (1/4194304), by norm_num⟩
  | 12 => ⟨((-1/140737488355328), (-1/562949953421312)), (1/4194304), by norm_num⟩
  | 13 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | 14 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | 15 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | 16 => ⟨(0, 0), (1/4194304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨3,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨3,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(326799/1048576)) (K:=(167907/268435456)) (L:=(982406120967982037/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile003
