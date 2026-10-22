/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile042Gamma
import XiBand97.Tile042Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile042
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((70514543/18014398509481984), (-355052125/36028797018963968)), (999/18014398509481984), by norm_num⟩
  | 1 => ⟨((452305473/36028797018963968), (-360705125/36028797018963968)), (1341/18014398509481984), by norm_num⟩
  | 2 => ⟨((214879463/18014398509481984), (-274192485/144115188075855872)), (11357/144115188075855872), by norm_num⟩
  | 3 => ⟨((203526977/36028797018963968), (18690427/9007199254740992)), (9979/144115188075855872), by norm_num⟩
  | 4 => ⟨((843161043/576460752303423488), (60842233/36028797018963968)), (32619/576460752303423488), by norm_num⟩
  | 5 => ⟨((161723183/1152921504606846976), (1485102065/2305843009213693952)), (54835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-408748449/9223372036854775808), (1427813931/9223372036854775808)), (24725/576460752303423488), by norm_num⟩
  | 7 => ⟨((-53528215/2305843009213693952), (222788305/9223372036854775808)), (1510939/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-423732117/73786976294838206464), (286063447/147573952589676412928)), (2971977/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-1131522611/1180591620717411303424), (-167153139/1180591620717411303424)), (47309255/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1072140493/9444732965739290427392), (-187684709/2361183241434822606848)), (377951421/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-163550005/18889465931478580854784), (-148212155/9444732965739290427392)), (1511297849/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-4579921/37778931862957161709568), (-39869691/18889465931478580854784)), (755592701/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((1605939/18889465931478580854784), (-502477/2361183241434822606848)), (188895313/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((313653/18889465931478580854784), (-599799/37778931862957161709568)), (188894773/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((19039/9444732965739290427392), (-27393/37778931862957161709568)), (94447339/2361183241434822606848), by norm_num⟩
  | 16 => ⟨((3521/18889465931478580854784), (219/18889465931478580854784)), (1511157299/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile042Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-4631/524288), (1035124113/16777216)), (7359/33554432), by norm_num⟩
  | 1 => ⟨((1848491/524288), (-1247818115/33554432)), (8235/33554432), by norm_num⟩
  | 2 => ⟨((-90281065/33554432), (379590777/16777216)), (273/1048576), by norm_num⟩
  | 3 => ⟨((55036691/33554432), (-166773207/16777216)), (34357/134217728), by norm_num⟩
  | 4 => ⟨((-12721805/16777216), (462289325/134217728)), (32231/134217728), by norm_num⟩
  | 5 => ⟨((38514783/134217728), (-65812221/67108864)), (240029/1073741824), by norm_num⟩
  | 6 => ⟨((-48866859/536870912), (63106439/268435456)), (454613/2147483648), by norm_num⟩
  | 7 => ⟨((26341421/1073741824), (-12946123/268435456)), (1761331/8589934592), by norm_num⟩
  | 8 => ⟨((-12224659/2147483648), (18378267/2147483648)), (27752303/137438953472), by norm_num⟩
  | 9 => ⟨((4947485/4294967296), (-11344047/8589934592)), (110312763/549755813888), by norm_num⟩
  | 10 => ⟨((-1766525/8589934592), (3040217/17179869184)), (880505815/4398046511104), by norm_num⟩
  | 11 => ⟨((2247877/68719476736), (-1397075/68719476736)), (1759726637/8796093022208), by norm_num⟩
  | 12 => ⟨((-642179/137438953472), (33097/17179869184)), (1759351213/8796093022208), by norm_num⟩
  | 13 => ⟨((331473/549755813888), (-145733/1099511627776)), (1759250749/8796093022208), by norm_num⟩
  | 14 => ⟨((-310357/4398046511104), (5087/2199023255552)), (1759225869/8796093022208), by norm_num⟩
  | 15 => ⟨((4125/549755813888), (331/274877906944)), (879610071/4398046511104), by norm_num⟩
  | 16 => ⟨((-6367/8796093022208), (-597/2199023255552)), (1759218911/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile042Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35411/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35411/1280))
  have he : value ((69/80), (35411/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-33129281/67108864), (-1062627705/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1363496332531057/2251799813685248), (173302190136765/2251799813685248)), (56108191/1125899906842624), by norm_num⟩
  | 1 => ⟨((1488528253/4294967296), (-189193913/4294967296)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((-851981389/8589934592), (108287963/8589934592)), (73/8589934592), by norm_num⟩
  | 3 => ⟨((1300384745/68719476736), (-165280623/68719476736)), (57/34359738368), by norm_num⟩
  | 4 => ⟨((-1488589281/549755813888), (189201669/549755813888)), (133/549755813888), by norm_num⟩
  | 5 => ⟨((1363226111/4398046511104), (-43316961/1099511627776)), (31/1099511627776), by norm_num⟩
  | 6 => ⟨((-1040350447/35184372088832), (4132185/1099511627776)), (97/35184372088832), by norm_num⟩
  | 7 => ⟨((1361051713/562949953421312), (-43247869/140737488355328)), (129/562949953421312), by norm_num⟩
  | 8 => ⟨((-1558036573/9007199254740992), (198028513/9007199254740992)), (75/4503599627370496), by norm_num⟩
  | 9 => ⟨((1585360915/144115188075855872), (-201501473/144115188075855872)), (155/144115188075855872), by norm_num⟩
  | 10 => ⟨((-90740501/144115188075855872), (184531807/2305843009213693952)), (9/144115188075855872), by norm_num⟩
  | 11 => ⟨((302177057/9223372036854775808), (-76814209/18446744073709551616)), (61/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-1844859243/1180591620717411303424), (234484055/1180591620717411303424)), (189/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((1299609545/18889465931478580854784), (-10323881/1180591620717411303424)), (135/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-1700230727/604462909807314587353088), (216101579/604462909807314587353088)), (45/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((519014647/4835703278458516698824704), (-131934899/9671406556917033397649408)), (7/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-297065789/77371252455336267181195264), (75514911/154742504910672534362390528)), (65/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98958294602637/633825300114114700748351602688), (1963797264381/5070602400912917605986812821504)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781197857211853/633825300114114700748351602688), (4660231559553/633825300114114700748351602688)), (23165/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((473118401597659/9903520314283042199192993792), (5242492506447/39614081257132168796771975168)), (52135/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236552280812149/309485009821345068724781056), (5569863375543/2475880078570760549798248448)), (27705/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774083182109599/154742504910672534362390528), (1392385636145/38685626227668133590597632)), (55429/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552263743363425/9671406556917033397649408), (5221104963455/9671406556917033397649408)), (25993/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630579408138671/302231454903657293676544), (2284062672949/302231454903657293676544)), (11377/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891640894303793/75557863725914323419136), (7422562689495/75557863725914323419136)), (18497/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300423801216641/4722366482869645213696), (5566360454007/4722366482869645213696)), (55525/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812705186829407/295147905179352825856), (1913207947641/147573952589676412928)), (4775/36893488147419103232), by norm_num⟩
  | 8 => ⟨((914210931993115/36893488147419103232), (597791670305/4611686018427387904)), (95581/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914107431872283/4611686018427387904), (10758358497169/9223372036854775808)), (107641/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599453766891199/1152921504606846976), (2688997131953/288230376151711744)), (107781/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199354382898615/144115188075855872), (4704408088627/72057594037927936)), (47233/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498776250157195/36028797018963968), (7053928895697/18014398509481984)), (71007/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498143506295039/9007199254740992), (8812694209791/4503599627370496)), (89035/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122803328024581/2251799813685248), (2201394103861/281474976710656)), (44725/562949953421312), by norm_num⟩
  | 1 => ⟨((280288669997705/281474976710656), (13190421902989/562949953421312)), (270429/1125899906842624), by norm_num⟩
  | 0 => ⟨((279002253039855/281474976710656), (13154092839971/281474976710656)), (274595/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279002253039855/281474976710656), (13154092839971/281474976710656)), (1047496797801780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1103746101348303/1125899906842624), (104308285786127/1125899906842624)), (1140063/1125899906842624), by norm_num⟩
  | 2 => ⟨((268091157664227/281474976710656), (102255860467759/562949953421312)), (2446503/1125899906842624), by norm_num⟩
  | 3 => ⟨((492113397624969/562949953421312), (194787418271525/562949953421312)), (2774565/562949953421312), by norm_num⟩
  | 4 => ⟨((725582999212921/1125899906842624), (681108490284971/1125899906842624)), (6770943/562949953421312), by norm_num⟩
  | 5 => ⟨((27783070603491/562949953421312), (877876866614631/1125899906842624)), (67676553/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1363496332531057/2251799813685248), (173302190136765/2251799813685248)), (56108191/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-33129281/67108864), (-1062627705/67108864)), (1/33554432), by norm_num⟩, -3, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-907339/562949953421312), (903371457/144115188075855872)), (2777/72057594037927936), by norm_num⟩
  | 1 => ⟨((-851519147/144115188075855872), (495830543/144115188075855872)), (1333/18014398509481984), by norm_num⟩
  | 2 => ⟨((-988741475/288230376151711744), (-266883631/288230376151711744)), (26093/288230376151711744), by norm_num⟩
  | 3 => ⟨((-690158861/1152921504606846976), (-1211948139/1152921504606846976)), (102089/1152921504606846976), by norm_num⟩
  | 4 => ⟨((186230561/2305843009213693952), (-336864807/1152921504606846976)), (354053/4611686018427387904), by norm_num⟩
  | 5 => ⟨((955048409/18446744073709551616), (-542824129/18446744073709551616)), (594507/9223372036854775808), by norm_num⟩
  | 6 => ⟨((339739385/36893488147419103232), (366073749/147573952589676412928)), (1032983/18446744073709551616), by norm_num⟩
  | 7 => ⟨((767572983/1180591620717411303424), (324788659/295147905179352825856)), (60791185/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-317306067/9444732965739290427392), (671073359/4722366482869645213696)), (233761937/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-227098587/18889465931478580854784), (150158575/18889465931478580854784)), (1841490643/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-46344673/37778931862957161709568), (-1803313/9444732965739290427392)), (915951631/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-286213/4722366482869645213696), (-2718955/37778931862957161709568)), (1829022193/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-859/9444732965739290427392), (-119445/18889465931478580854784)), (1828235975/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((4231/18889465931478580854784), (-11639/37778931862957161709568)), (1828039213/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((741/37778931862957161709568), (-137/18889465931478580854784)), (913996849/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((5/4722366482869645213696), (7/37778931862957161709568)), (913991951/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/18889465931478580854784), (1/37778931862957161709568)), (1827981931/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-870849151/2251799813685248), (-224049429/2251799813685248)), (289/70368744177664), by norm_num⟩
  | 1 => ⟨((68474531/4503599627370496), (-636228057/2251799813685248)), (45575/4503599627370496), by norm_num⟩
  | 2 => ⟨((482500857/18014398509481984), (-74566449/2251799813685248)), (267985/18014398509481984), by norm_num⟩
  | 3 => ⟨((578470503/36028797018963968), (-1054140843/36028797018963968)), (625159/36028797018963968), by norm_num⟩
  | 4 => ⟨((401513629/36028797018963968), (89749401/36028797018963968)), (2530625/144115188075855872), by norm_num⟩
  | 5 => ⟨((64901687/576460752303423488), (208331461/144115188075855872)), (591369/36028797018963968), by norm_num⟩
  | 6 => ⟨((362652271/9223372036854775808), (902672495/9223372036854775808)), (68630557/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-136065497/9223372036854775808), (2727203/72057594037927936)), (500901661/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-95074621/18446744073709551616), (-27884425/36893488147419103232)), (117124335/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-8991587/147573952589676412928), (-36369449/147573952589676412928)), (1800127069/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-2345039/147573952589676412928), (-1809057/147573952589676412928)), (440815081/36893488147419103232), by norm_num⟩
  | 11 => ⟨((51519/73786976294838206464), (-227893/73786976294838206464)), (1746807683/147573952589676412928), by norm_num⟩
  | 12 => ⟨((12275/73786976294838206464), (-1471/147573952589676412928)), (870074909/73786976294838206464), by norm_num⟩
  | 13 => ⟨((275/73786976294838206464), (-65/36893488147419103232)), (1737681515/147573952589676412928), by norm_num⟩
  | 14 => ⟨((7/9223372036854775808), (27/147573952589676412928)), (1736836723/147573952589676412928), by norm_num⟩
  | 15 => ⟨(0, (3/73786976294838206464)), (1736568505/147573952589676412928), by norm_num⟩
  | 16 => ⟨(0, 0), (1736489589/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-435424569/1125899906842624), (-112024723/1125899906842624)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((8559321/562949953421312), (-159057013/562949953421312)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((30156303/1125899906842624), (-37283221/1125899906842624)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((4519301/281474976710656), (-16470951/562949953421312)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((3136825/281474976710656), (1402335/562949953421312)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((126761/1125899906842624), (1627589/1125899906842624)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((44269/1125899906842624), (55095/562949953421312)), (1/34359738368), by norm_num⟩
  | 7 => ⟨((-8305/562949953421312), (10653/281474976710656)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-5803/1125899906842624), (-851/1125899906842624)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((-69/1125899906842624), (-277/1125899906842624)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((-9/562949953421312), (-7/562949953421312)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1/1125899906842624), (-3/1125899906842624)), (1/34359738368), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨42,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨42,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(231/536870912)) (L:=(29465272307823/73786976294838206464)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile042
