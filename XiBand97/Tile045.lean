/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile045Gamma
import XiBand97.Tile045Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile045
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨45,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((810068925/144115188075855872), (-135520733/288230376151711744)), (17897/288230376151711744), by norm_num⟩
  | 1 => ⟨((563960825/72057594037927936), (519706341/144115188075855872)), (3253/36028797018963968), by norm_num⟩
  | 2 => ⟨((553999261/144115188075855872), (762862651/144115188075855872)), (14013/144115188075855872), by norm_num⟩
  | 3 => ⟨((230478887/576460752303423488), (58836787/18014398509481984)), (48177/576460752303423488), by norm_num⟩
  | 4 => ⟨((-526869599/1152921504606846976), (660520039/576460752303423488)), (18727/288230376151711744), by norm_num⟩
  | 5 => ⟨((-650986345/2305843009213693952), (271587475/1152921504606846976)), (118741/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-102455591/1152921504606846976), (341157759/18446744073709551616)), (204901/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-677134087/36893488147419103232), (-193842205/36893488147419103232)), (1530037/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-93735121/36893488147419103232), (-707319821/295147905179352825856)), (11932909/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-112503821/590295810358705651712), (-313786335/590295810358705651712)), (94713019/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((182637427/18889465931478580854784), (-1532876753/18889465931478580854784)), (378041113/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((13702773/2361183241434822606848), (-169712487/18889465931478580854784)), (1511375653/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((41109471/37778931862957161709568), (-25244893/37778931862957161709568)), (1511200963/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((5259187/37778931862957161709568), (-596191/37778931862957161709568)), (1511165395/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((510513/37778931862957161709568), (20855/4722366482869645213696)), (1511158685/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((9399/9444732965739290427392), (34001/37778931862957161709568)), (1511157505/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((1847/37778931862957161709568), (4073/37778931862957161709568)), (1511157311/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile045Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((457428625/16777216), (415222291/8388608)), (1867/8388608), by norm_num⟩
  | 1 => ⟨((-995943625/33554432), (-359803073/16777216)), (1051/4194304), by norm_num⟩
  | 2 => ⟨((327585219/16777216), (415345987/33554432)), (17805/67108864), by norm_num⟩
  | 3 => ⟨((-300736971/33554432), (-364411259/67108864)), (4351/16777216), by norm_num⟩
  | 4 => ⟨((860157065/268435456), (134206363/67108864)), (16233/67108864), by norm_num⟩
  | 5 => ⟨((-248951285/268435456), (-5346165/8388608)), (240821/1073741824), by norm_num⟩
  | 6 => ⟨((59811959/268435456), (11885505/67108864)), (455121/2147483648), by norm_num⟩
  | 7 => ⟨((-48528069/1073741824), (-46283037/1073741824)), (1761763/8589934592), by norm_num⟩
  | 8 => ⟨((16776629/2147483648), (9921931/1073741824)), (1734543/8589934592), by norm_num⟩
  | 9 => ⟨((-4943511/4294967296), (-15092133/8589934592)), (110310651/549755813888), by norm_num⟩
  | 10 => ⟨((2446079/17179869184), (1281499/4294967296)), (880493527/4398046511104), by norm_num⟩
  | 11 => ⟨((-482383/34359738368), (-391223/8589934592)), (1759716141/8796093022208), by norm_num⟩
  | 12 => ⟨((247465/274877906944), (863265/137438953472)), (1759347821/8796093022208), by norm_num⟩
  | 13 => ⟨((20583/1099511627776), (-863703/1099511627776)), (1759249725/8796093022208), by norm_num⟩
  | 14 => ⟨((-79081/4398046511104), (98139/1099511627776)), (1759225593/8796093022208), by norm_num⟩
  | 15 => ⟨((2033/549755813888), (-40503/4398046511104)), (439805019/2199023255552), by norm_num⟩
  | 16 => ⟨((-4869/8796093022208), (3779/4398046511104)), (109951181/549755813888), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile045Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (7297/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (7297/256))
  have he : value ((69/80), (7297/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-33129281/67108864), (-547428367/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1129191142601111/2251799813685248), (783634647908657/2251799813685248)), (30364753/562949953421312), by norm_num⟩
  | 1 => ⟨((308184349/1073741824), (-855493547/4294967296)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((-352787835/4294967296), (489654515/8589934592)), (5/536870912), by norm_num⟩
  | 3 => ⟨((538462371/34359738368), (-186840719/17179869184)), (31/17179869184), by norm_num⟩
  | 4 => ⟨((-1232787937/549755813888), (213882155/137438953472)), (145/549755813888), by norm_num⟩
  | 5 => ⟨((282241839/1099511627776), (-48967459/274877906944)), (135/4398046511104), by norm_num⟩
  | 6 => ⟨((-861575115/35184372088832), (298957407/17592186044416)), (105/35184372088832), by norm_num⟩
  | 7 => ⟨((563583305/281474976710656), (-782229665/562949953421312)), (35/140737488355328), by norm_num⟩
  | 8 => ⟨((-645150653/4503599627370496), (223860419/2251799813685248)), (41/2251799813685248), by norm_num⟩
  | 9 => ⟨((656465097/72057594037927936), (-455572821/72057594037927936)), (43/36028797018963968), by norm_num⟩
  | 10 => ⟨((-1202360345/2305843009213693952), (417206259/1152921504606846976)), (5/72057594037927936), by norm_num⟩
  | 11 => ⟨((250250513/9223372036854775808), (-694674143/36893488147419103232)), (17/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-763917977/590295810358705651712), (530142835/590295810358705651712)), (53/295147905179352825856), by norm_num⟩
  | 13 => ⟨((269070689/4722366482869645213696), (-373458675/9444732965739290427392)), (19/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-704030307/302231454903657293676544), (488582065/302231454903657293676544)), (51/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((859652835/9671406556917033397649408), (-596580791/9671406556917033397649408)), (127/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-246017573/77371252455336267181195264), (682923861/309485009821345068724781056)), (147/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98958294602637/633825300114114700748351602688), (206375958785/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445300311964053/158456325028528675187087900672), (489744931265/79228162514264337593543950336)), (46293/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892477627876979/39614081257132168796771975168), (4407487463079/39614081257132168796771975168)), (13023/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892422770317391/2475880078570760549798248448), (1170679232565/618970019642690137449562112)), (55361/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774087988299041/154742504910672534362390528), (2341224221687/77371252455336267181195264)), (27689/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((388067137284173/2417851639229258349412352), (2194754991397/4835703278458516698824704)), (25967/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261163321247175/604462909807314587353088), (1920267807979/302231454903657293676544)), (45459/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891648777114849/75557863725914323419136), (1560083611241/18889465931478580854784)), (73903/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300430205168857/4722366482869645213696), (4679781498907/4722366482869645213696)), (55455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625419978129543/590295810358705651712), (3216968075599/295147905179352825856)), (9537/73786976294838206464), by norm_num⟩
  | 8 => ⟨((914217533880573/36893488147419103232), (4020636889333/36893488147419103232)), (95439/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828231364898147/9223372036854775808), (9044854582569/9223372036854775808)), (107463/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799736162888185/576460752303423488), (9042878405263/1152921504606846976)), (26895/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199372935627071/144115188075855872), (7910291071381/144115188075855872)), (94265/144115188075855872), by norm_num⟩
  | 4 => ⟨((749404351767773/18014398509481984), (2965242679083/9007199254740992)), (70831/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498192158460209/9007199254740992), (7409186879883/4503599627370496)), (88771/4503599627370496), by norm_num⟩
  | 2 => ⟨((561432047077989/1125899906842624), (14806565722151/2251799813685248)), (178239/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121276064046387/1125899906842624), (22180158758215/1125899906842624)), (269103/1125899906842624), by norm_num⟩
  | 0 => ⟨((558186208215797/562949953421312), (44240542343071/1125899906842624)), (545199/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558186208215797/562949953421312), (44240542343071/1125899906842624)), (2079769138816451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((276296795794219/281474976710656), (21933086973193/281474976710656)), (562009/562949953421312), by norm_num⟩
  | 2 => ⟨((269504806247691/281474976710656), (86118371492733/562949953421312)), (595463/281474976710656), by norm_num⟩
  | 3 => ⟨((125728311519185/140737488355328), (329824203838537/1125899906842624)), (2644929/562949953421312), by norm_num⟩
  | 4 => ⟨((200484723684735/281474976710656), (589299137442065/1125899906842624)), (12550677/1125899906842624), by norm_num⟩
  | 5 => ⟨((525504115787269/2251799813685248), (419737044189095/562949953421312)), (62033861/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1129191142601111/2251799813685248), (783634647908657/2251799813685248)), (30364753/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-33129281/67108864), (-547428367/33554432)), (1/33554432), by norm_num⟩, -3, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-765275207/288230376151711744), (631772397/288230376151711744)), (15299/288230376151711744), by norm_num⟩
  | 1 => ⟨((-527460773/144115188075855872), (-97788125/288230376151711744)), (15521/144115188075855872), by norm_num⟩
  | 2 => ⟨((-714847879/576460752303423488), (-854038835/576460752303423488)), (39213/288230376151711744), by norm_num⟩
  | 3 => ⟨((7947455/144115188075855872), (-765125833/1152921504606846976)), (306869/2305843009213693952), by norm_num⟩
  | 4 => ⟨((591327215/4611686018427387904), (-254328615/2305843009213693952)), (64735/576460752303423488), by norm_num⟩
  | 5 => ⟨((1241506227/36893488147419103232), (39748177/18446744073709551616)), (3322103/36893488147419103232), by norm_num⟩
  | 6 => ⟨((544270077/147573952589676412928), (599883417/147573952589676412928)), (10993749/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-24223161/1180591620717411303424), (220995037/295147905179352825856)), (39017779/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-582305275/9444732965739290427392), (292065109/4722366482869645213696)), (588861595/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-83224381/9444732965739290427392), (1707483/4722366482869645213696)), (1150558557/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-1418837/2361183241434822606848), (-9382701/18889465931478580854784)), (1141396255/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-23953/2361183241434822606848), (-1133227/18889465931478580854784)), (1138630521/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((39577/18889465931478580854784), (-69303/18889465931478580854784)), (142234193/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((4581/18889465931478580854784), (-485/4722366482869645213696)), (1137683759/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((69/4722366482869645213696), (57/18889465931478580854784)), (1137639813/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((11/18889465931478580854784), (5/9444732965739290427392)), (568815175/9444732965739290427392), by norm_num⟩
  | 16 => ⟨(0, (1/18889465931478580854784)), (1137628445/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-203659467/1125899906842624), (-322729229/4503599627370496)), (11605/2251799813685248), by norm_num⟩
  | 1 => ⟨((48208851/1125899906842624), (-447054135/2251799813685248)), (29467/2251799813685248), by norm_num⟩
  | 2 => ⟨((557604871/9007199254740992), (-59081723/18014398509481984)), (369965/18014398509481984), by norm_num⟩
  | 3 => ⟨((1127253481/144115188075855872), (-281468041/144115188075855872)), (3535397/144115188075855872), by norm_num⟩
  | 4 => ⟨((380594103/72057594037927936), (317958347/144115188075855872)), (3567757/144115188075855872), by norm_num⟩
  | 5 => ⟨((-6832807/36028797018963968), (1427173891/1152921504606846976)), (6490969/288230376151711744), by norm_num⟩
  | 6 => ⟨((-873642501/9223372036854775808), (129144399/4611686018427387904)), (180422103/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-327913653/36893488147419103232), (375351327/36893488147419103232)), (157024797/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-225012951/73786976294838206464), (-1033303/1152921504606846976)), (1129098653/73786976294838206464), by norm_num⟩
  | 9 => ⟨((136185/9223372036854775808), (-41596969/147573952589676412928)), (65998659/4611686018427387904), by norm_num⟩
  | 10 => ⟨((362411/73786976294838206464), (-869433/147573952589676412928)), (2038249535/147573952589676412928), by norm_num⟩
  | 11 => ⟨((46639/73786976294838206464), (-26781/18446744073709551616)), (2005034047/147573952589676412928), by norm_num⟩
  | 12 => ⟨((21813/147573952589676412928), (2657/147573952589676412928)), (1991464081/147573952589676412928), by norm_num⟩
  | 13 => ⟨((237/147573952589676412928), (605/147573952589676412928)), (1986386581/147573952589676412928), by norm_num⟩
  | 14 => ⟨((3/9223372036854775808), (11/73786976294838206464)), (496158275/36893488147419103232), by norm_num⟩
  | 15 => ⟨(0, (3/73786976294838206464)), (992035577/73786976294838206464), by norm_num⟩
  | 16 => ⟨(0, 0), (991951883/73786976294838206464), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-203659457/1125899906842624), (-80682307/1125899906842624)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((24104425/562949953421312), (-55881765/281474976710656)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((69700609/1125899906842624), (-3692605/1125899906842624)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((8806665/1125899906842624), (-2198969/1125899906842624)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((185837/35184372088832), (2484049/1125899906842624)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-106763/562949953421312), (1393725/1125899906842624)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((-53323/562949953421312), (31529/1125899906842624)), (1/34359738368), by norm_num⟩
  | 7 => ⟨((-10007/1125899906842624), (11455/1125899906842624)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((-3433/1125899906842624), (-1009/1125899906842624)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((17/1125899906842624), (-317/1125899906842624)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((3/562949953421312), (-7/1125899906842624)), (1/34359738368), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨45,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨45,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(399/1073741824)) (L:=(229699922883177/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile045
