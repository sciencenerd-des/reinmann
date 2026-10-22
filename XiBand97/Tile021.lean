/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile021Gamma
import XiBand97.Tile021Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile021
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-297152877/1125899906842624), (-362164423/562949953421312)), (563/562949953421312), by norm_num⟩
  | 1 => ⟨((22643619/140737488355328), (-272907733/281474976710656)), (639/281474976710656), by norm_num⟩
  | 2 => ⟨((126535699/281474976710656), (-586184105/1125899906842624)), (23/8796093022208), by norm_num⟩
  | 3 => ⟨((1359800893/4503599627370496), (-446708249/4503599627370496)), (9099/4503599627370496), by norm_num⟩
  | 4 => ⟨((119912249/1125899906842624), (210758457/9007199254740992)), (10639/9007199254740992), by norm_num⟩
  | 5 => ⟨((196842557/9007199254740992), (721217001/36028797018963968)), (5097/9007199254740992), by norm_num⟩
  | 6 => ⟨((295167445/144115188075855872), (227825627/36028797018963968)), (4365/18014398509481984), by norm_num⟩
  | 7 => ⟨((-139513591/576460752303423488), (1432304481/1152921504606846976)), (123309/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-610907445/4611686018427387904), (372669081/2305843009213693952)), (274349/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-1032266315/36893488147419103232), (109874593/9223372036854775808)), (1662973/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-72755869/18446744073709551616), (-76473933/295147905179352825856)), (12159467/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-951220323/2361183241434822606848), (-543639239/2361183241434822606848)), (95058937/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-8437375/295147905179352825856), (-383671507/9444732965739290427392)), (189139051/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((-34996505/37778931862957161709568), (-181406679/37778931862957161709568)), (377880177/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((903725/9444732965739290427392), (-16460849/37778931862957161709568)), (1511220497/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((409085/18889465931478580854784), (-1177617/37778931862957161709568)), (1511167619/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((47627/18889465931478580854784), (-63477/37778931862957161709568)), (755579437/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile021Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-290031855/33554432), (1178643987/67108864)), (14199/67108864), by norm_num⟩
  | 1 => ⟨((237793737/16777216), (77989685/67108864)), (30581/134217728), by norm_num⟩
  | 2 => ⟨((-315514425/33554432), (10001925/67108864)), (31903/134217728), by norm_num⟩
  | 3 => ⟨((71811891/16777216), (5715495/134217728)), (15823/67108864), by norm_num⟩
  | 4 => ⟨((-95308095/67108864), (-18825499/134217728)), (242941/1073741824), by norm_num⟩
  | 5 => ⟨((98890763/268435456), (22563495/268435456)), (463313/2147483648), by norm_num⟩
  | 6 => ⟨((-41737435/536870912), (-4124391/134217728)), (1786611/8589934592), by norm_num⟩
  | 7 => ⟨((7320241/536870912), (8954887/1073741824)), (1748155/8589934592), by norm_num⟩
  | 8 => ⟨((-4295117/2147483648), (-977351/536870912)), (110700219/549755813888), by norm_num⟩
  | 9 => ⟨((1040231/4294967296), (1431807/4294967296)), (110211259/549755813888), by norm_num⟩
  | 10 => ⟨((-393503/17179869184), (-901925/17179869184)), (1760526765/8796093022208), by norm_num⟩
  | 11 => ⟨((91813/68719476736), (495877/68719476736)), (1759594413/8796093022208), by norm_num⟩
  | 12 => ⟨((3329/68719476736), (-59953/68719476736)), (1759318125/8796093022208), by norm_num⟩
  | 13 => ⟨((-15979/549755813888), (12767/137438953472)), (1759242997/8796093022208), by norm_num⟩
  | 14 => ⟨((11903/2199023255552), (-38025/4398046511104)), (1759224169/8796093022208), by norm_num⟩
  | 15 => ⟨((-6517/8796093022208), (1511/2199023255552)), (879609897/4398046511104), by norm_num⟩
  | 16 => ⟨((371/4398046511104), (-3/68719476736)), (439804711/2199023255552), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile021Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28251/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28251/1280))
  have he : value ((69/80), (28251/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-423883755/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((171430172860047/281474976710656), (-91128497761415/2251799813685248)), (22024189/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1497201861/4294967296), (99484935/4294967296)), (27/4294967296), by norm_num⟩
  | 2 => ⟨((428472929/4294967296), (-56941689/8589934592)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((-653981023/34359738368), (86910471/68719476736)), (27/68719476736), by norm_num⟩
  | 4 => ⟨((374315811/137438953472), (-49744507/274877906944)), (33/549755813888), by norm_num⟩
  | 5 => ⟨((-685584793/2199023255552), (45555219/2199023255552)), (1/137438953472), by norm_num⟩
  | 6 => ⟨((130801567/4398046511104), (-17382807/8796093022208)), (13/17592186044416), by norm_num⟩
  | 7 => ⟨((-684491259/281474976710656), (45482557/281474976710656)), (9/140737488355328), by norm_num⟩
  | 8 => ⟨((783557601/4503599627370496), (-104130485/9007199254740992)), (11/2251799813685248), by norm_num⟩
  | 9 => ⟨((-797299381/72057594037927936), (26489173/36028797018963968)), (47/144115188075855872), by norm_num⟩
  | 10 => ⟨((1460307887/2305843009213693952), (-48516717/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-303937833/9223372036854775808), (80783325/36893488147419103232)), (5/4611686018427387904), by norm_num⟩
  | 12 => ⟨((1855609179/1180591620717411303424), (-123300115/1180591620717411303424)), (1/18446744073709551616), by norm_num⟩
  | 13 => ⟨((-1307182329/18889465931478580854784), (86858663/18889465931478580854784)), (47/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((1710137919/604462909807314587353088), (-113633951/604462909807314587353088)), (1/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-1044077859/9671406556917033397649408), (2168003/302231454903657293676544)), (41/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((1195187129/309485009821345068724781056), (-39708445/154742504910672534362390528)), (49/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-43213950713/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781209416406967/633825300114114700748351602688), (-6409362507/39614081257132168796771975168)), (23053/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892487316217665/39614081257132168796771975168), (-115363376723/39614081257132168796771975168)), (25935/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236554208615549/309485009821345068724781056), (-122567410359/2475880078570760549798248448)), (6889/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((887049783594145/77371252455336267181195264), (-122560461277/154742504910672534362390528)), (6889/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552280127034651/9671406556917033397649408), (-57446524801/4835703278458516698824704)), (12917/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630587087236401/302231454903657293676544), (-50262018091/302231454903657293676544)), (22605/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236458471018909/9444732965739290427392), (-81668859229/37778931862957161709568)), (36733/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325111408352069/1180591620717411303424), (-61245589937/2361183241434822606848)), (27551/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625443117025751/590295810358705651712), (-84202848869/295147905179352825856)), (37883/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828466878112567/73786976294838206464), (-105238807319/36893488147419103232)), (23677/36893488147419103232), by norm_num⟩
  | 7 => ⟨((914135559692479/4611686018427387904), (-236746750675/9223372036854775808)), (26637/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599517037942097/1152921504606846976), (-14793503377/72057594037927936)), (13319/288230376151711744), by norm_num⟩
  | 5 => ⟨((299854408309619/36028797018963968), (-51763007031/36028797018963968)), (23309/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498886891569333/36028797018963968), (-310464040291/36028797018963968)), (69931/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498309374842551/9007199254740992), (-193940314475/4503599627370496)), (87419/9007199254740992), by norm_num⟩
  | 2 => ⟨((35094078109401/70368744177664), (-775163321121/4503599627370496)), (87427/2251799813685248), by norm_num⟩
  | 1 => ⟨((2243137056982329/2251799813685248), (-290312821311/562949953421312)), (32791/281474976710656), by norm_num⟩
  | 0 => ⟨((558624036334433/562949953421312), (-579133663201/562949953421312)), (262419/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558624036334433/562949953421312), (-579133663201/562949953421312)), (1001049046043014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2217323061691261/2251799813685248), (-2298733537845/1125899906842624)), (1042691/2251799813685248), by norm_num⟩
  | 2 => ⟨((1091682394084169/1125899906842624), (-9054152780669/2251799813685248)), (128607/140737488355328), by norm_num⟩
  | 3 => ⟨((2116973183654911/2251799813685248), (-17557971403911/2251799813685248)), (1001725/562949953421312), by norm_num⟩
  | 4 => ⟨((248760300023087/281474976710656), (-33013373920329/2251799813685248)), (1899115/562949953421312), by norm_num⟩
  | 5 => ⟨((879149658998219/1125899906842624), (-14588182752809/562949953421312)), (3412463/562949953421312), by norm_num⟩
  | 6 => ⟨((171430172860047/281474976710656), (-91128497761415/2251799813685248)), (22024189/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-423883755/33554432)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-105145837/562949953421312), (-429121387/1125899906842624)), (371/562949953421312), by norm_num⟩
  | 1 => ⟨((373027097/2251799813685248), (-853132695/2251799813685248)), (1049/562949953421312), by norm_num⟩
  | 2 => ⟨((106116061/562949953421312), (-252208227/4503599627370496)), (3003/1125899906842624), by norm_num⟩
  | 3 => ⟨((14267795/281474976710656), (300781843/9007199254740992)), (46095/18014398509481984), by norm_num⟩
  | 4 => ⟨((56961337/36028797018963968), (976024991/72057594037927936)), (133423/72057594037927936), by norm_num⟩
  | 5 => ⟨((-936083827/576460752303423488), (993877465/576460752303423488)), (624917/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1517008463/4611686018427387904), (-81939241/4611686018427387904)), (2507035/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-840193115/36893488147419103232), (-548897641/18446744073709551616)), (1156469/4611686018427387904), by norm_num⟩
  | 8 => ⟨((25625701/36893488147419103232), (-254805107/73786976294838206464)), (17696069/147573952589676412928), by norm_num⟩
  | 9 => ⟨((276819483/1180591620717411303424), (-335321793/2361183241434822606848)), (164833133/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((80661969/4722366482869645213696), (152712705/37778931862957161709568)), (2000510975/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((21810399/37778931862957161709568), (1697337/2361183241434822606848)), (113054511/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((13085/1180591620717411303424), (1579721/37778931862957161709568)), (1756587477/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((1177/18889465931478580854784), (23271/9444732965739290427392)), (1743517275/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-2475/37778931862957161709568), (2747/18889465931478580854784)), (870249001/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-277/37778931862957161709568), (157/37778931862957161709568)), (1739848969/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-3/9444732965739290427392), (-1/37778931862957161709568)), (1739718381/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((292325351/35184372088832), (30813/2199023255552)), (19343/140737488355328), by norm_num⟩
  | 1 => ⟨((424725915/140737488355328), (159064815/281474976710656)), (42721/140737488355328), by norm_num⟩
  | 2 => ⟨((1113395089/281474976710656), (76467119/35184372088832)), (116971/281474976710656), by norm_num⟩
  | 3 => ⟨((-322165843/562949953421312), (1111716303/562949953421312)), (262023/562949953421312), by norm_num⟩
  | 4 => ⟨((-1797137201/4503599627370496), (-223145135/4503599627370496)), (2070247/4503599627370496), by norm_num⟩
  | 5 => ⟨((-64336809/9007199254740992), (-1044943801/36028797018963968)), (1907289/4503599627370496), by norm_num⟩
  | 6 => ⟨((-889170061/288230376151711744), (-661548803/288230376151711744)), (27372861/72057594037927936), by norm_num⟩
  | 7 => ⟨((272195203/1152921504606846976), (-259058925/288230376151711744)), (99078095/288230376151711744), by norm_num⟩
  | 8 => ⟨((380692077/4611686018427387904), (13855451/2305843009213693952)), (1474469337/4611686018427387904), by norm_num⟩
  | 9 => ⟨((602267/576460752303423488), (9099857/4611686018427387904)), (1411871797/4611686018427387904), by norm_num⟩
  | 10 => ⟨((658505/2305843009213693952), (503621/4611686018427387904)), (690444327/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-9319/4611686018427387904), (16037/576460752303423488)), (341799395/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-71/144115188075855872), (719/2305843009213693952)), (1361723517/4611686018427387904), by norm_num⟩
  | 13 => ⟨((-81/4611686018427387904), (75/1152921504606846976)), (1359723011/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-15/4611686018427387904), (1/1152921504606846976)), (339762349/1152921504606846976), by norm_num⟩
  | 15 => ⟨(0, (1/4611686018427387904)), (679419523/2305843009213693952), by norm_num⟩
  | 16 => ⟨(0, 0), (1358777807/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1169301431/140737488355328), (1972039/140737488355328)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((3397807531/1125899906842624), (636259193/1125899906842624)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((2226790225/562949953421312), (2446948003/1125899906842624)), (1/1073741824), by norm_num⟩
  | 3 => ⟨((-644331701/1125899906842624), (277929077/140737488355328)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((-449284313/1125899906842624), (-55786261/1125899906842624)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((-2010525/281474976710656), (-32654509/1125899906842624)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((-1736655/562949953421312), (-646043/281474976710656)), (1/1073741824), by norm_num⟩
  | 7 => ⟨((33227/140737488355328), (-505973/562949953421312)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((92943/1125899906842624), (6765/1125899906842624)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((1177/1125899906842624), (1111/562949953421312)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((161/562949953421312), (123/1125899906842624)), (1/1073741824), by norm_num⟩
  | 11 => ⟨((-1/562949953421312), (31/1125899906842624)), (1/1073741824), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/1073741824), by norm_num⟩
  | 13 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 14 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 15 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | 16 => ⟨(0, 0), (1/1073741824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨21,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨21,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(6871/1073741824)) (L:=(4904412644086911/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile021
