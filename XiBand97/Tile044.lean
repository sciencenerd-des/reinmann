/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile044Gamma
import XiBand97.Tile044Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile044
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨44,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((901450811/144115188075855872), (-110140471/36028797018963968)), (253/4503599627370496), by norm_num⟩
  | 1 => ⟨((1525466497/144115188075855872), (47380687/72057594037927936)), (11053/144115188075855872), by norm_num⟩
  | 2 => ⟨((971227117/144115188075855872), (628454719/144115188075855872)), (11763/144115188075855872), by norm_num⟩
  | 3 => ⟨((272421541/144115188075855872), (1024179123/288230376151711744)), (20613/288230376151711744), by norm_num⟩
  | 4 => ⟨((-5900347/288230376151711744), (433468175/288230376151711744)), (66825/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-503553423/2305843009213693952), (898815787/2305843009213693952)), (111237/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-854139033/9223372036854775808), (546186447/9223372036854775808)), (398177/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-1693812503/73786976294838206464), (142664109/73786976294838206464)), (378637/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-1144326545/295147905179352825856), (-237959017/147573952589676412928)), (11896625/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-258953911/590295810358705651712), (-607818171/1180591620717411303424)), (47318513/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-110525675/4722366482869645213696), (-894053819/9444732965739290427392)), (2952883/73786976294838206464), by norm_num⟩
  | 11 => ⟨((12680321/4722366482869645213696), (-234713675/18889465931478580854784)), (1511313085/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((34993781/37778931862957161709568), (-22567673/18889465931478580854784)), (755594221/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((5554321/37778931862957161709568), (-711571/9444732965739290427392)), (377790767/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((630147/37778931862957161709568), (-28443/37778931862957161709568)), (755579141/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((55205/37778931862957161709568), (10825/18889465931478580854784)), (23611835/590295810358705651712), by norm_num⟩
  | 16 => ⟨((3695/37778931862957161709568), (3675/37778931862957161709568)), (1511157301/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile044Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((10421031/524288), (950416399/16777216)), (3721/16777216), by norm_num⟩
  | 1 => ⟨((-699792757/33554432), (-1034649377/33554432)), (4193/16777216), by norm_num⟩
  | 2 => ⟨((457133829/33554432), (629975443/33554432)), (8895/33554432), by norm_num⟩
  | 3 => ⟨((-816866219/134217728), (-70706495/8388608)), (34839/134217728), by norm_num⟩
  | 4 => ⟨((280193917/134217728), (821014327/268435456)), (32531/134217728), by norm_num⟩
  | 5 => ⟨((-76241179/134217728), (-250249629/268435456)), (241285/1073741824), by norm_num⟩
  | 6 => ⟨((8367875/67108864), (65398539/268435456)), (455745/2147483648), by norm_num⟩
  | 7 => ⟨((-2963735/134217728), (-59437231/1073741824)), (1763107/8589934592), by norm_num⟩
  | 8 => ⟨((6558185/2147483648), (23741851/2147483648)), (27762479/137438953472), by norm_num⟩
  | 9 => ⟨((-307033/1073741824), (-8410591/4294967296)), (110326715/549755813888), by norm_num⟩
  | 10 => ⟨((40771/17179869184), (5321927/17179869184)), (880538071/4398046511104), by norm_num⟩
  | 11 => ⟨((429723/68719476736), (-3022845/68719476736)), (1759744685/8796093022208), by norm_num⟩
  | 12 => ⟨((-479113/274877906944), (1545685/274877906944)), (1759356045/8796093022208), by norm_num⟩
  | 13 => ⟨((180529/549755813888), (-177895/274877906944)), (1759251893/8796093022208), by norm_num⟩
  | 14 => ⟨((-55525/1099511627776), (293741/4398046511104)), (1759226123/8796093022208), by norm_num⟩
  | 15 => ⟨((59181/8796093022208), (-6719/1099511627776)), (1759220195/8796093022208), by norm_num⟩
  | 16 => ⟨((-7019/8796093022208), (4243/8796093022208)), (879609461/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile044Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36127/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36127/1280))
  have he : value ((69/80), (36127/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-33129281/67108864), (-271028431/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-619832518960607/1125899906842624), (593621505411901/2251799813685248)), (119680845/2251799813685248), by norm_num⟩
  | 1 => ⟨((338335423/1073741824), (-81007037/536870912)), (133/4294967296), by norm_num⟩
  | 2 => ⟨((-774605341/8589934592), (370924705/8589934592)), (39/4294967296), by norm_num⟩
  | 3 => ⟨((591142589/34359738368), (-283072397/34359738368)), (61/34359738368), by norm_num⟩
  | 4 => ⟨((-1353397177/549755813888), (324041433/274877906944)), (71/274877906944), by norm_num⟩
  | 5 => ⟨((1239419357/4398046511104), (-148375965/1099511627776)), (133/4398046511104), by norm_num⟩
  | 6 => ⟨((-118233365/4398046511104), (113233601/8796093022208)), (13/4398046511104), by norm_num⟩
  | 7 => ⟨((309360609/140737488355328), (-592557199/562949953421312)), (139/562949953421312), by norm_num⟩
  | 8 => ⟨((-1416537339/9007199254740992), (678317935/9007199254740992)), (161/9007199254740992), by norm_num⟩
  | 9 => ⟨((1441380113/144115188075855872), (-86276757/18014398509481984)), (167/144115188075855872), by norm_num⟩
  | 10 => ⟨((-659996357/1152921504606846976), (316043463/1152921504606846976)), (155/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1098934625/36893488147419103232), (-526231851/36893488147419103232)), (131/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-838655539/590295810358705651712), (401595551/590295810358705651712)), (51/295147905179352825856), by norm_num⟩
  | 13 => ⟨((1181580381/18889465931478580854784), (-282903649/9444732965739290427392)), (73/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-386454393/151115727451828646838272), (370112299/302231454903657293676544)), (49/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((235939143/2417851639229258349412352), (-451923851/9671406556917033397649408)), (61/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((-1080346353/309485009821345068724781056), (517330739/309485009821345068724781056)), (71/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98958294602637/633825300114114700748351602688), (3510541743097/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781200182839825/633825300114114700748351602688), (4165383494275/633825300114114700748351602688)), (46305/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892476364710335/39614081257132168796771975168), (4685823011139/39614081257132168796771975168)), (26053/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473105337340901/618970019642690137449562112), (4978433043583/2475880078570760549798248448)), (27689/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887043239325741/77371252455336267181195264), (4978147186395/154742504910672534362390528)), (55395/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552267039619581/9671406556917033397649408), (583338632759/1208925819614629174706176)), (51951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261161906213599/604462909807314587353088), (255191642323/37778931862957161709568)), (11369/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891646301083777/75557863725914323419136), (6634411932965/75557863725914323419136)), (73931/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300428193654217/4722366482869645213696), (4975309046239/4722366482869645213696)), (55479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625416961314189/590295810358705651712), (1710059173021/147573952589676412928)), (76331/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914215460191521/36893488147419103232), (2137268603823/18446744073709551616)), (47743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828226181791821/9223372036854775808), (4808013328761/4611686018427387904)), (53761/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599466496319581/1152921504606846976), (9613920236139/1152921504606846976)), (107647/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599683554048463/72057594037927936), (8409805197311/144115188075855872)), (23583/36028797018963968), by norm_num⟩
  | 4 => ⟨((749399254852359/18014398509481984), (1576243072053/4503599627370496)), (35445/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498176876437725/9007199254740992), (7877032708945/4503599627370496)), (88859/4503599627370496), by norm_num⟩
  | 2 => ⟨((561422503480823/1125899906842624), (15741458211249/2251799813685248)), (178459/2251799813685248), by norm_num⟩
  | 1 => ⟨((560618967963673/562949953421312), (23580462295437/1125899906842624)), (33693/140737488355328), by norm_num⟩
  | 0 => ⟨((69766141581023/70368744177664), (47032785518909/1125899906842624)), (17079/35184372088832), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((69766141581023/70368744177664), (47032785518909/1125899906842624)), (65151214733827103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1104734465621239/1125899906842624), (46630020356447/562949953421312)), (1129357/1125899906842624), by norm_num⟩
  | 2 => ⟨((538121016341397/562949953421312), (91506874291957/562949953421312)), (2403347/1125899906842624), by norm_num⟩
  | 3 => ⟨((999025645091983/1125899906842624), (87470958824931/281474976710656)), (2688009/562949953421312), by norm_num⟩
  | 4 => ⟨((777718814990365/1125899906842624), (620912964186651/1125899906842624)), (12881717/1125899906842624), by norm_num⟩
  | 5 => ⟨((97394823803649/562949953421312), (1715590140063473/2251799813685248)), (32004229/1125899906842624), by norm_num⟩
  | 6 => ⟨((-619832518960607/1125899906842624), (593621505411901/2251799813685248)), (119680845/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-33129281/67108864), (-271028431/16777216)), (1/33554432), by norm_num⟩, -3, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-380127061/144115188075855872), (240090115/72057594037927936)), (6663/144115188075855872), by norm_num⟩
  | 1 => ⟨((-161803085/36028797018963968), (150276641/288230376151711744)), (25799/288230376151711744), by norm_num⟩
  | 2 => ⟨((-1070595167/576460752303423488), (-423205493/288230376151711744)), (31909/288230376151711744), by norm_num⟩
  | 3 => ⟨((-222166047/2305843009213693952), (-465201839/576460752303423488)), (62643/576460752303423488), by norm_num⟩
  | 4 => ⟨((582500905/4611686018427387904), (-373808081/2305843009213693952)), (216583/2305843009213693952), by norm_num⟩
  | 5 => ⟨((1491365457/36893488147419103232), (-196987811/36893488147419103232)), (722679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((195078205/36893488147419103232), (583337869/147573952589676412928)), (9970229/147573952589676412928), by norm_num⟩
  | 7 => ⟨((169956183/1180591620717411303424), (521816311/590295810358705651712)), (72914121/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-551628103/9444732965739290427392), (404839987/4722366482869645213696)), (69865659/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-95756405/9444732965739290427392), (21816475/9444732965739290427392)), (1099189631/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-1878447/2361183241434822606848), (-8406389/18889465931478580854784)), (1092904787/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-452541/18889465931478580854784), (-1251939/18889465931478580854784)), (545504751/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((30459/18889465931478580854784), (-5391/1180591620717411303424)), (545245563/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((2355/9444732965739290427392), (-1551/9444732965739290427392)), (1090361229/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((79/4722366482869645213696), (3/9444732965739290427392)), (545165581/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((7/9444732965739290427392), (9/18889465931478580854784)), (1090324689/18889465931478580854784), by norm_num⟩
  | 16 => ⟨(0, (1/18889465931478580854784)), (1090323387/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1086170363/4503599627370496), (-187337263/2251799813685248)), (21897/4503599627370496), by norm_num⟩
  | 1 => ⟨((87706039/2251799813685248), (-1045742689/4503599627370496)), (26669/2251799813685248), by norm_num⟩
  | 2 => ⟨((1036002435/18014398509481984), (-49165169/4503599627370496)), (163655/9007199254740992), by norm_num⟩
  | 3 => ⟨((751148139/72057594037927936), (-159776723/18014398509481984)), (775311/36028797018963968), by norm_num⟩
  | 4 => ⟨((1025362513/144115188075855872), (43800903/18014398509481984)), (3148657/144115188075855872), by norm_num⟩
  | 5 => ⟨((-146360433/1152921504606846976), (1586605329/1152921504606846976)), (11673389/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1246989443/18446744073709551616), (218533761/4611686018427387904)), (333618791/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-201407439/18446744073709551616), (656730893/36893488147419103232)), (149669387/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-278222853/73786976294838206464), (-67173065/73786976294838206464)), (552298985/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-333331/73786976294838206464), (-21297837/73786976294838206464)), (2103116249/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-25189/73786976294838206464), (-292443/36893488147419103232)), (1025028277/73786976294838206464), by norm_num⟩
  | 11 => ⟨((101129/147573952589676412928), (-145457/73786976294838206464)), (2026358777/147573952589676412928), by norm_num⟩
  | 12 => ⟨((23747/147573952589676412928), (27/2305843009213693952)), (1008387457/73786976294838206464), by norm_num⟩
  | 13 => ⟨((169/73786976294838206464), (207/73786976294838206464)), (2013229341/147573952589676412928), by norm_num⟩
  | 14 => ⟨((33/73786976294838206464), (29/147573952589676412928)), (1006010081/73786976294838206464), by norm_num⟩
  | 15 => ⟨(0, (7/147573952589676412928)), (2011638085/147573952589676412928), by norm_num⟩
  | 16 => ⟨((-1/147573952589676412928), 0), (2011526223/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-271542585/1125899906842624), (-46834319/562949953421312)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((10963257/281474976710656), (-130717835/562949953421312)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((64750153/1125899906842624), (-6145643/562949953421312)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((11736689/1125899906842624), (-9986047/1125899906842624)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((4005323/562949953421312), (1368779/562949953421312)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-142931/1125899906842624), (1549419/1125899906842624)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((-38055/562949953421312), (53353/1125899906842624)), (1/34359738368), by norm_num⟩
  | 7 => ⟨((-12293/1125899906842624), (10021/562949953421312)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-4245/1125899906842624), (-1025/1125899906842624)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((-5/1125899906842624), (-325/1125899906842624)), (1/34359738368), by norm_num⟩
  | 10 => ⟨(0, (-9/1125899906842624)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1/1125899906842624), (-1/562949953421312)), (1/34359738368), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨44,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨44,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(217/536870912)) (L:=(301197299022329/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile044
