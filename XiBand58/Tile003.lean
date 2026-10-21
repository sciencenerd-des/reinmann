/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile003Gamma
import XiBand58.Tile003Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile003
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
  | 0 => ⟨((-180324097/2199023255552), (-220420675/8796093022208)), (987/8796093022208), by norm_num⟩
  | 1 => ⟨((-292271523/4398046511104), (-187336037/2199023255552)), (2251/8796093022208), by norm_num⟩
  | 2 => ⟨((-70497889/17592186044416), (-587051911/8796093022208)), (1259/4398046511104), by norm_num⟩
  | 3 => ⟨((482507941/35184372088832), (-821299359/35184372088832)), (1875/8796093022208), by norm_num⟩
  | 4 => ⟨((507987505/70368744177664), (-506420023/140737488355328)), (16865/140737488355328), by norm_num⟩
  | 5 => ⟨((528344297/281474976710656), (103630757/562949953421312)), (15323/281474976710656), by norm_num⟩
  | 6 => ⟨((652969757/2251799813685248), (241699109/1125899906842624)), (46943/2251799813685248), by norm_num⟩
  | 7 => ⟨((426080271/18014398509481984), (957595079/18014398509481984)), (124941/18014398509481984), by norm_num⟩
  | 8 => ⟨((-79042089/144115188075855872), (582412925/72057594037927936)), (296989/144115188075855872), by norm_num⟩
  | 9 => ⟨((-71550117/144115188075855872), (993348023/1152921504606846976)), (82403/144115188075855872), by norm_num⟩
  | 10 => ⟨((-409918907/4611686018427387904), (147966939/2305843009213693952)), (1542303/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1584109489/147573952589676412928), (375876011/147573952589676412928)), (5013261/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-600391647/590295810358705651712), (-160599617/1180591620717411303424)), (53931319/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-373298745/4722366482869645213696), (-192838597/4722366482869645213696)), (193979749/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-23758823/4722366482869645213696), (-196324717/37778931862957161709568)), (759192949/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-4665815/18889465931478580854784), (-18738875/37778931862957161709568)), (378091901/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((-129281/18889465931478580854784), (-1496787/37778931862957161709568)), (1511349067/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile003Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-819506933/67108864), (772690059/67108864)), (6909/33554432), by norm_num⟩
  | 1 => ⟨((349322761/33554432), (344041659/67108864)), (28579/134217728), by norm_num⟩
  | 2 => ⟨((-243298145/67108864), (-203363957/67108864)), (29031/134217728), by norm_num⟩
  | 3 => ⟨((14905221/16777216), (19556489/16777216)), (115303/536870912), by norm_num⟩
  | 4 => ⟨((-37772921/268435456), (-44288361/134217728)), (451889/2147483648), by norm_num⟩
  | 5 => ⟨((1303657/134217728), (19578445/268435456)), (1770307/8589934592), by norm_num⟩
  | 6 => ⟨((276981/134217728), (-6951333/536870912)), (27901487/137438953472), by norm_num⟩
  | 7 => ⟨((-1001471/1073741824), (1994147/1073741824)), (110662331/549755813888), by norm_num⟩
  | 8 => ⟨((28325/134217728), (-451681/2147483648)), (881776087/4398046511104), by norm_num⟩
  | 9 => ⟨((-151291/4294967296), (73083/4294967296)), (1760703405/8796093022208), by norm_num⟩
  | 10 => ⟨((81139/17179869184), (-8645/17179869184)), (1759680429/8796093022208), by norm_num⟩
  | 11 => ⟨((-17907/34359738368), (-4503/34359738368)), (1759350189/8796093022208), by norm_num⟩
  | 12 => ⟨((6441/137438953472), (4465/137438953472)), (1759253101/8796093022208), by norm_num⟩
  | 13 => ⟨((-3533/1099511627776), (-5185/1099511627776)), (1759226997/8796093022208), by norm_num⟩
  | 14 => ⟨((133/1099511627776), (145/274877906944)), (1759220517/8796093022208), by norm_num⟩
  | 15 => ⟨((1/137438953472), (-53/1099511627776)), (1759219011/8796093022208), by norm_num⟩
  | 16 => ⟨((-19/8796093022208), (1/274877906944)), (879609343/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile003Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2501/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2501/160))
  have he : value ((15/16), (2501/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-300204105/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-584565740018071/1125899906842624), (-605691287352595/2251799813685248)), (14395197/562949953421312), by norm_num⟩
  | 1 => ⟨((638170121/2147483648), (661232871/4294967296)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((-365266205/4294967296), (-378466515/8589934592)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((1115016377/68719476736), (144413977/17179869184)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((-638196285/274877906944), (-330629991/274877906944)), (19/137438953472), by norm_num⟩
  | 5 => ⟨((1168899777/4398046511104), (605571251/4398046511104)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((-111506209/4398046511104), (-462143673/35184372088832)), (57/35184372088832), by norm_num⟩
  | 7 => ⟨((1167035337/562949953421312), (302302671/281474976710656)), (77/562949953421312), by norm_num⟩
  | 8 => ⟨((-1335940229/9007199254740992), (-173027451/2251799813685248)), (91/9007199254740992), by norm_num⟩
  | 9 => ⟨((1359369517/144115188075855872), (352123901/72057594037927936)), (95/144115188075855872), by norm_num⟩
  | 10 => ⟨((-622444365/1152921504606846976), (-644938805/2305843009213693952)), (89/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1036408243/36893488147419103232), (134232859/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-790938327/590295810358705651712), (-204880487/295147905179352825856)), (15/147573952589676412928), by norm_num⟩
  | 13 => ⟨((1114351681/18889465931478580854784), (144327887/4722366482869645213696)), (87/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-728932385/302231454903657293676544), (-188818795/151115727451828646838272)), (59/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((890059399/9671406556917033397649408), (461112571/9671406556917033397649408)), (37/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-1018877595/309485009821345068724781056), (-527849341/309485009821345068724781056)), (87/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (-3469628853151/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222641756365779/79228162514264337593543950336), (-4116547982749/633825300114114700748351602688)), (1447/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((59137561999617/1237940039285380274899124224), (-289429287221/2475880078570760549798248448)), (6513/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((473085585001091/618970019642690137449562112), (-4920025472591/2475880078570760549798248448)), (3461/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110875468248829/9671406556917033397649408), (-4919718805917/154742504910672534362390528)), (27697/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776096506865245/4835703278458516698824704), (-2305955178479/4835703278458516698824704)), (12987/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261097157682917/604462909807314587353088), (-2017547662441/302231454903657293676544)), (22737/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945770564983869/37778931862957161709568), (-3278208876701/37778931862957161709568)), (36963/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300349354924755/4722366482869645213696), (-4916777230095/4722366482869645213696)), (13869/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625308622455381/590295810358705651712), (-6759696702255/590295810358705651712)), (38163/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914147796728295/36893488147419103232), (-8448311405545/73786976294838206464)), (47739/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828074071979713/9223372036854775808), (-4751273694699/4611686018427387904)), (13439/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49978579777127/36028797018963968), (-9500290088501/1152921504606846976)), (26909/576460752303423488), by norm_num⟩
  | 5 => ⟨((599617172459129/72057594037927936), (-519388086607/9007199254740992)), (5895/18014398509481984), by norm_num⟩
  | 4 => ⟨((1498599740082589/36028797018963968), (-12460212762269/36028797018963968)), (70879/36028797018963968), by norm_num⟩
  | 3 => ⟨((748964535976813/4503599627370496), (-15566310710353/9007199254740992)), (44421/4503599627370496), by norm_num⟩
  | 2 => ⟨((17540596732195/35184372088832), (-7776411028085/1125899906842624)), (11151/281474976710656), by norm_num⟩
  | 1 => ⟨((560435094964545/562949953421312), (-23295316576313/1125899906842624)), (67365/562949953421312), by norm_num⟩
  | 0 => ⟨((557766364383675/562949953421312), (-11613450261081/281474976710656)), (273135/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((557766364383675/562949953421312), (-11613450261081/281474976710656)), (1041927341941451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1103344361048343/1125899906842624), (-23013029455661/281474976710656)), (140945/281474976710656), by norm_num⟩
  | 2 => ⟨((1073714616472137/1125899906842624), (-180416011236723/1125899906842624)), (149645/140737488355328), by norm_num⟩
  | 3 => ⟨((497518977356099/562949953421312), (-344107512813833/1125899906842624)), (1333507/562949953421312), by norm_num⟩
  | 4 => ⟨((774216736004007/1125899906842624), (-304112322658925/562949953421312)), (3172147/562949953421312), by norm_num⟩
  | 5 => ⟨((50953538085857/281474976710656), (-836482349440325/1125899906842624)), (31159483/2251799813685248), by norm_num⟩
  | 6 => ⟨((-584565740018071/1125899906842624), (-605691287352595/2251799813685248)), (14395197/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-300204105/33554432)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((315207163/8796093022208), (308457121/8796093022208)), (1605/17592186044416), by norm_num⟩
  | 1 => ⟨((-78478867/8796093022208), (369739399/8796093022208)), (9073/35184372088832), by norm_num⟩
  | 2 => ⟨((-1170537775/70368744177664), (6515809/1099511627776)), (25347/70368744177664), by norm_num⟩
  | 3 => ⟨((-995415087/281474976710656), (-12940319/4398046511104)), (94519/281474976710656), by norm_num⟩
  | 4 => ⟨((170549049/1125899906842624), (-467581161/562949953421312)), (16579/70368744177664), by norm_num⟩
  | 5 => ⟨((122629627/1125899906842624), (-154190101/4503599627370496)), (598825/4503599627370496), by norm_num⟩
  | 6 => ⟨((34924817/4503599627370496), (75770245/9007199254740992)), (1134359/18014398509481984), by norm_num⟩
  | 7 => ⟨((-430364273/1152921504606846976), (415152657/576460752303423488)), (14851897/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1142813787/36893488147419103232), (-589742525/36893488147419103232)), (343609389/36893488147419103232), by norm_num⟩
  | 9 => ⟨((725798883/295147905179352825856), (5482737/36893488147419103232)), (1794596531/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-26530691/295147905179352825856), (50408541/147573952589676412928)), (1095223513/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-17180811/590295810358705651712), (-15364935/2361183241434822606848)), (1364712035/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((6711113/9444732965739290427392), (-4055189/2361183241434822606848)), (2142062823/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((1560937/18889465931478580854784), (1831971/18889465931478580854784)), (1304672921/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-5899/590295810358705651712), (67843/18889465931478580854784)), (554471411/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-3031/37778931862957161709568), (-29735/37778931862957161709568)), (1066302275/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((987/18889465931478580854784), (203/18889465931478580854784)), (2115189791/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-462547137/549755813888), (-17183475/1099511627776)), (36865/2199023255552), by norm_num⟩
  | 1 => ⟨((-799328157/4398046511104), (-295767633/4398046511104)), (145687/4398046511104), by norm_num⟩
  | 2 => ⟨((-433491735/2199023255552), (-236957943/2199023255552)), (193477/4398046511104), by norm_num⟩
  | 3 => ⟨((212808585/8796093022208), (-1421483003/17592186044416)), (420935/8796093022208), by norm_num⟩
  | 4 => ⟨((487320163/35184372088832), (157245345/70368744177664)), (811047/17592186044416), by norm_num⟩
  | 5 => ⟨((19244355/562949953421312), (36723201/35184372088832)), (46994583/1125899906842624), by norm_num⟩
  | 6 => ⟨((405806727/36028797018963968), (457846125/18014398509481984)), (1343545607/36028797018963968), by norm_num⟩
  | 7 => ⟨((-31228573/18014398509481984), (150525087/18014398509481984)), (1225918575/36028797018963968), by norm_num⟩
  | 8 => ⟨((-18404109/36028797018963968), (436313/9007199254740992)), (144509717/4503599627370496), by norm_num⟩
  | 9 => ⟨((-213319/18014398509481984), (213185/18014398509481984)), (280194155/9007199254740992), by norm_num⟩
  | 10 => ⟨((-99751/36028797018963968), (-1457/4503599627370496)), (1105136069/36028797018963968), by norm_num⟩
  | 11 => ⟨((-1297/36028797018963968), (-2581/36028797018963968)), (68683855/2251799813685248), by norm_num⟩
  | 12 => ⟨((-65/9007199254740992), (-17/9007199254740992)), (1096717283/36028797018963968), by norm_num⟩
  | 13 => ⟨((-7/36028797018963968), (-15/36028797018963968)), (547992539/18014398509481984), by norm_num⟩
  | 14 => ⟨((-1/36028797018963968), (1/36028797018963968)), (136970277/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1/36028797018963968), 0), (34240595/1125899906842624), by norm_num⟩
  | 16 => ⟨(0, 0), (547841131/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-947296564443/1125899906842624), (-4398967605/281474976710656)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-204628017999/1125899906842624), (-75716518929/1125899906842624)), (1/16777216), by norm_num⟩
  | 2 => ⟨((-221947774777/1125899906842624), (-121322465425/1125899906842624)), (1/8388608), by norm_num⟩
  | 3 => ⟨((27239497009/1125899906842624), (-45487459019/562949953421312)), (1/8388608), by norm_num⟩
  | 4 => ⟨((1949280953/140737488355328), (2515926277/1125899906842624)), (1/8388608), by norm_num⟩
  | 5 => ⟨((19244379/562949953421312), (293785539/281474976710656)), (1/8388608), by norm_num⟩
  | 6 => ⟨((6341047/562949953421312), (28615833/1125899906842624)), (1/8388608), by norm_num⟩
  | 7 => ⟨((-1952055/1125899906842624), (9407965/1125899906842624)), (1/8388608), by norm_num⟩
  | 8 => ⟨((-287579/562949953421312), (54447/1125899906842624)), (1/8388608), by norm_num⟩
  | 9 => ⟨((-6665/562949953421312), (6641/562949953421312)), (1/8388608), by norm_num⟩
  | 10 => ⟨((-3107/1125899906842624), (-379/1125899906842624)), (1/8388608), by norm_num⟩
  | 11 => ⟨((-37/1125899906842624), (-83/1125899906842624)), (1/8388608), by norm_num⟩
  | 12 => ⟨((-7/1125899906842624), (-3/1125899906842624)), (1/8388608), by norm_num⟩
  | 13 => ⟨(0, 0), (1/8388608), by norm_num⟩
  | 14 => ⟨(0, 0), (1/8388608), by norm_num⟩
  | 15 => ⟨(0, 0), (1/8388608), by norm_num⟩
  | 16 => ⟨(0, 0), (1/8388608), by norm_num⟩
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
    (r:=(163873/524288)) (K:=(733663/1073741824)) (L:=(993483786005696611/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile003
