/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile002Gamma
import XiBand58.Tile002Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile002
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-555469461/4398046511104), (189798381/4398046511104)), (1051/8796093022208), by norm_num⟩
  | 1 => ⟨((-1397852405/8796093022208), (-417066369/8796093022208)), (2297/8796093022208), by norm_num⟩
  | 2 => ⟨((-552956247/8796093022208), (-174004975/2199023255552)), (1255/4398046511104), by norm_num⟩
  | 3 => ⟨((-104610819/35184372088832), (-352958667/8796093022208)), (7367/35184372088832), by norm_num⟩
  | 4 => ⟨((403092493/70368744177664), (-361710539/35184372088832)), (8207/70368744177664), by norm_num⟩
  | 5 => ⟨((1333337801/562949953421312), (-726376497/562949953421312)), (7415/140737488355328), by norm_num⟩
  | 6 => ⟨((1136134867/2251799813685248), (23760469/1125899906842624)), (45321/2251799813685248), by norm_num⟩
  | 7 => ⟨((304860565/4503599627370496), (188917853/4503599627370496)), (15071/2251799813685248), by norm_num⟩
  | 8 => ⟨((797042803/144115188075855872), (672238665/72057594037927936)), (71729/36028797018963968), by norm_num⟩
  | 9 => ⟨((66960813/576460752303423488), (374393897/288230376151711744)), (638873/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-412206111/9223372036854775808), (1236069757/9223372036854775808)), (752781/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-20865023/2305843009213693952), (789963695/73786976294838206464)), (4953139/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-662258437/590295810358705651712), (749501687/1180591620717411303424)), (53750559/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-513881251/4722366482869645213696), (94475825/4722366482869645213696)), (387708607/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-166809063/18889465931478580854784), (-44466105/37778931862957161709568)), (1518224739/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-11622627/18889465931478580854784), (-664613/2361183241434822606848)), (756171851/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-1396855/37778931862957161709568), (-599871/18889465931478580854784)), (755672913/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile002Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1072799561/134217728), (53954201/8388608)), (6897/33554432), by norm_num⟩
  | 1 => ⟨((402812311/67108864), (274345983/33554432)), (3565/16777216), by norm_num⟩
  | 2 => ⟨((-178105643/134217728), (-263277357/67108864)), (28969/134217728), by norm_num⟩
  | 3 => ⟨((3274779/33554432), (168355199/134217728)), (230245/1073741824), by norm_num⟩
  | 4 => ⟨((1956679/33554432), (-9933735/33554432)), (451657/2147483648), by norm_num⟩
  | 5 => ⟨((-7634205/268435456), (7199301/134217728)), (1769955/8589934592), by norm_num⟩
  | 6 => ⟨((4087449/536870912), (-1990539/268435456)), (27902767/137438953472), by norm_num⟩
  | 7 => ⟨((-802859/536870912), (767387/1073741824)), (110672571/549755813888), by norm_num⟩
  | 8 => ⟨((499943/2147483648), (-53427/2147483648)), (881827287/4398046511104), by norm_num⟩
  | 9 => ⟨((-252805/8589934592), (-62889/8589934592)), (1760747437/8796093022208), by norm_num⟩
  | 10 => ⟨((25723/8589934592), (35449/17179869184)), (1759698349/8796093022208), by norm_num⟩
  | 11 => ⟨((-15785/68719476736), (-11535/34359738368)), (1759355309/8796093022208), by norm_num⟩
  | 12 => ⟨((2629/274877906944), (11443/274877906944)), (1759254669/8796093022208), by norm_num⟩
  | 13 => ⟨((359/549755813888), (-4597/1099511627776)), (1759227429/8796093022208), by norm_num⟩
  | 14 => ⟨((-903/4398046511104), (1501/4398046511104)), (1759220617/8796093022208), by norm_num⟩
  | 15 => ⟨((253/8796093022208), (-47/2199023255552)), (1759219035/8796093022208), by norm_num⟩
  | 16 => ⟨((-13/4398046511104), (7/8796093022208)), (439804673/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile002Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2403/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2403/160))
  have he : value ((15/16), (2403/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-1153763237/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-111250450220181/281474976710656), (-242593273561705/562949953421312)), (29200401/1125899906842624), by norm_num⟩
  | 1 => ⟨((30363015/134217728), (529677907/2147483648)), (67/4294967296), by norm_num⟩
  | 2 => ⟨((-556119211/8589934592), (-303169065/4294967296)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((848808375/68719476736), (462728919/34359738368)), (63/68719476736), by norm_num⟩
  | 4 => ⟨((-971656315/549755813888), (-529699623/274877906944)), (75/549755813888), by norm_num⟩
  | 5 => ⟨((444913609/2199023255552), (970180783/4398046511104)), (71/4398046511104), by norm_num⟩
  | 6 => ⟨((-169768635/8796093022208), (-740396625/35184372088832)), (7/4398046511104), by norm_num⟩
  | 7 => ⟨((444203955/281474976710656), (242158327/140737488355328)), (19/140737488355328), by norm_num⟩
  | 8 => ⟨((-508493543/4503599627370496), (-138602937/1125899906842624)), (45/4503599627370496), by norm_num⟩
  | 9 => ⟨((258705669/36028797018963968), (282067421/36028797018963968)), (3/4503599627370496), by norm_num⟩
  | 10 => ⟨((-947673955/2305843009213693952), (-516625611/1152921504606846976)), (91/2305843009213693952), by norm_num⟩
  | 11 => ⟨((788967781/36893488147419103232), (430106747/18446744073709551616)), (39/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-150525833/147573952589676412928), (-328237365/295147905179352825856)), (61/590295810358705651712), by norm_num⟩
  | 13 => ⟨((424151187/9444732965739290427392), (924906145/18889465931478580854784)), (11/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-554901189/302231454903657293676544), (-302505059/151115727451828646838272)), (15/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((42347465/604462909807314587353088), (184686177/2417851639229258349412352)), (75/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-775622541/309485009821345068724781056), (-422831573/154742504910672534362390528)), (89/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (-1506483842807/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781136270288309/633825300114114700748351602688), (-446842680199/79228162514264337593543950336)), (11569/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((473101153997817/9903520314283042199192993792), (-4021373875667/39614081257132168796771975168)), (26037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946172650383793/1237940039285380274899124224), (-4272473802595/2475880078570760549798248448)), (13835/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887005318765237/77371252455336267181195264), (-4272208240501/154742504910672534362390528)), (27677/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((194024519873129/1208925819614629174706176), (-1001228236709/2417851639229258349412352)), (25955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315275026511439/151115727451828646838272), (-3504016416157/604462909807314587353088)), (22719/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891546288975651/75557863725914323419136), (-5693496869159/75557863725914323419136)), (9233/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300353546030319/4722366482869645213696), (-4269658786793/4722366482869645213696)), (433/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1625314908083093/590295810358705651712), (-2935013259547/295147905179352825856)), (38125/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914152117259021/36893488147419103232), (-7336400749263/73786976294838206464)), (47687/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828084870788283/9223372036854775808), (-515743267649/576460752303423488)), (26845/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599326698059811/1152921504606846976), (-8249941816763/1152921504606846976)), (3359/72057594037927936), by norm_num⟩
  | 5 => ⟨((599623242883591/72057594037927936), (-7216501704257/144115188075855872)), (47087/144115188075855872), by norm_num⟩
  | 4 => ⟨((46831905524219/1125899906842624), (-5410175007383/18014398509481984)), (35375/18014398509481984), by norm_num⟩
  | 3 => ⟨((748980453675653/4503599627370496), (-3379428902197/2251799813685248)), (44325/4503599627370496), by norm_num⟩
  | 2 => ⟨((561318975306687/1125899906842624), (-3376524469203/562949953421312)), (88967/2251799813685248), by norm_num⟩
  | 1 => ⟨((560474802731527/562949953421312), (-2528747587781/140737488355328)), (67123/562949953421312), by norm_num⟩
  | 0 => ⟨((1115770452094451/1125899906842624), (-40342568281417/1125899906842624)), (4245/17592186044416), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1115770452094451/1125899906842624), (-40342568281417/1125899906842624)), (16193389959686989/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1104286599008755/1125899906842624), (-79959231502627/1125899906842624)), (278971/562949953421312), by norm_num⟩
  | 2 => ⟨((1077409640657685/1125899906842624), (-19606074056575/140737488355328)), (73357/70368744177664), by norm_num⟩
  | 3 => ⟨((252289312291989/281474976710656), (-75046718009739/281474976710656)), (2573345/1125899906842624), by norm_num⟩
  | 4 => ⟨((824483766063103/1125899906842624), (-269061002831675/562949953421312)), (5985247/1125899906842624), by norm_num⟩
  | 5 => ⟨((43320701195443/140737488355328), (-394060657731953/562949953421312)), (452723/35184372088832), by norm_num⟩
  | 6 => ⟨((-111250450220181/281474976710656), (-242593273561705/562949953421312)), (29200401/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-1153763237/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((301334541/4398046511104), (657414349/17592186044416)), (1815/17592186044416), by norm_num⟩
  | 1 => ⟨((55629171/17592186044416), (579080905/8796093022208)), (4931/17592186044416), by norm_num⟩
  | 2 => ⟨((-784096813/35184372088832), (64047075/4398046511104)), (1685/4398046511104), by norm_num⟩
  | 3 => ⟨((-847319871/140737488355328), (-442708267/140737488355328)), (49371/140737488355328), by norm_num⟩
  | 4 => ⟨((-3497985/1125899906842624), (-683802891/562949953421312)), (273739/1125899906842624), by norm_num⟩
  | 5 => ⟨((1288300223/9007199254740992), (-619729529/9007199254740992)), (1225911/9007199254740992), by norm_num⟩
  | 6 => ⟨((804320027/72057594037927936), (368911459/36028797018963968)), (2309753/36028797018963968), by norm_num⟩
  | 7 => ⟨((-285760827/576460752303423488), (499856539/576460752303423488)), (30142479/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-522607415/18446744073709551616), (-674057683/18446744073709551616)), (174073717/18446744073709551616), by norm_num⟩
  | 9 => ⟨((774418717/147573952589676412928), (65020125/73786976294838206464)), (909101629/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-94067705/590295810358705651712), (691991071/1180591620717411303424)), (34738345/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-209914909/4722366482869645213696), (-18388293/1180591620717411303424)), (1392616315/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1133493/590295810358705651712), (-23631135/9444732965739290427392)), (552350075/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((33809/295147905179352825856), (4181617/18889465931478580854784)), (1359730729/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-47553/2361183241434822606848), (8221/2361183241434822606848)), (290203797/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((795/4722366482869645213696), (-28265/18889465931478580854784)), (1117404217/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((905/9444732965739290427392), (891/18889465931478580854784)), (277130713/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1732828569/2199023255552), (312230639/2199023255552)), (25567/1099511627776), by norm_num⟩
  | 1 => ⟨((-754248269/2199023255552), (612712725/2199023255552)), (23193/549755813888), by norm_num⟩
  | 2 => ⟨((-833733415/2199023255552), (-172740175/1099511627776)), (30309/549755813888), by norm_num⟩
  | 3 => ⟨((258736867/8796093022208), (-1042828937/8796093022208)), (261309/4398046511104), by norm_num⟩
  | 4 => ⟨((595018767/35184372088832), (17359405/8796093022208)), (1022529/17592186044416), by norm_num⟩
  | 5 => ⟨((39522353/281474976710656), (1047322605/1125899906842624)), (7654605/140737488355328), by norm_num⟩
  | 6 => ⟨((939330105/18014398509481984), (144585499/4503599627370496)), (113731355/2251799813685248), by norm_num⟩
  | 7 => ⟨((-47877165/36028797018963968), (382653981/36028797018963968)), (858303781/18014398509481984), by norm_num⟩
  | 8 => ⟨((-7152925/18014398509481984), (1063825/9007199254740992)), (206919151/4503599627370496), by norm_num⟩
  | 9 => ⟨((-236721/18014398509481984), (4201/140737488355328)), (1624378431/36028797018963968), by norm_num⟩
  | 10 => ⟨((-111627/36028797018963968), (-967/18014398509481984)), (1610633215/36028797018963968), by norm_num⟩
  | 11 => ⟨((-1881/36028797018963968), (-31/1125899906842624)), (200646477/4503599627370496), by norm_num⟩
  | 12 => ⟨((-249/36028797018963968), (-5/2251799813685248)), (1603201605/36028797018963968), by norm_num⟩
  | 13 => ⟨((-3/18014398509481984), (5/36028797018963968)), (200318659/4503599627370496), by norm_num⟩
  | 14 => ⟨((-7/36028797018963968), (1/18014398509481984)), (1602349465/36028797018963968), by norm_num⟩
  | 15 => ⟨((-1/18014398509481984), (-1/18014398509481984)), (400573117/9007199254740992), by norm_num⟩
  | 16 => ⟨((1/36028797018963968), 0), (200284655/4503599627370496), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-887208242849/1125899906842624), (159862056957/1125899906842624)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-193087560173/562949953421312), (313708894879/1125899906842624)), (1/8388608), by norm_num⟩
  | 2 => ⟨((-13339734559/35184372088832), (-88442971987/562949953421312)), (1/4194304), by norm_num⟩
  | 3 => ⟨((33118322175/1125899906842624), (-133482112559/1125899906842624)), (1/4194304), by norm_num⟩
  | 4 => ⟨((9520302169/562949953421312), (2222009069/1125899906842624)), (1/4194304), by norm_num⟩
  | 5 => ⟨((79043263/562949953421312), (1047320675/1125899906842624)), (1/4194304), by norm_num⟩
  | 6 => ⟨((58709291/1125899906842624), (9036615/281474976710656)), (1/4194304), by norm_num⟩
  | 7 => ⟨((-748349/562949953421312), (5978929/562949953421312)), (1/4194304), by norm_num⟩
  | 8 => ⟨((-55861/140737488355328), (66365/562949953421312)), (1/4194304), by norm_num⟩
  | 9 => ⟨((-14751/1125899906842624), (33619/1125899906842624)), (1/4194304), by norm_num⟩
  | 10 => ⟨((-865/281474976710656), (-65/1125899906842624)), (1/4194304), by norm_num⟩
  | 11 => ⟨((-55/1125899906842624), (-17/1125899906842624)), (1/4194304), by norm_num⟩
  | 12 => ⟨((-11/1125899906842624), (-1/562949953421312)), (1/4194304), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨2,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨2,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(163873/524288)) (K:=(162895/134217728)) (L:=(945286665743874569/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile002
