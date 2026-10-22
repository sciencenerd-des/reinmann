/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile038Gamma
import XiBand97.Tile038Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile038
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-97643485/4503599627370496), (-104083257/9007199254740992)), (213/2251799813685248), by norm_num⟩
  | 1 => ⟨((-349194825/18014398509481984), (-1124867101/36028797018963968)), (5761/36028797018963968), by norm_num⟩
  | 2 => ⟨((-68483195/72057594037927936), (-1965497263/72057594037927936)), (1559/9007199254740992), by norm_num⟩
  | 3 => ⟨((447226949/72057594037927936), (-428639677/36028797018963968)), (10039/72057594037927936), by norm_num⟩
  | 4 => ⟨((1184655137/288230376151711744), (-24246667/9007199254740992)), (27679/288230376151711744), by norm_num⟩
  | 5 => ⟨((205355363/144115188075855872), (-124743979/1152921504606846976)), (75509/1152921504606846976), by norm_num⟩
  | 6 => ⟨((361818349/1152921504606846976), (20291107/144115188075855872)), (57357/1152921504606846976), by norm_num⟩
  | 7 => ⟨((795703493/18446744073709551616), (514075973/9223372036854775808)), (398657/9223372036854775808), by norm_num⟩
  | 8 => ⟨((162005253/73786976294838206464), (455932301/36893488147419103232)), (1510413/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-343030985/590295810358705651712), (139217473/73786976294838206464)), (23756837/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-908055091/4722366482869645213696), (473290289/2361183241434822606848)), (5773/144115188075855872), by norm_num⟩
  | 11 => ⟨((-156729495/4722366482869645213696), (228577443/18889465931478580854784)), (1511634821/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-77025475/18889465931478580854784), (-15004187/37778931862957161709568)), (377813233/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-3550389/9444732965739290427392), (-2097067/9444732965739290427392)), (1511175075/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-233329/9444732965739290427392), (-166383/4722366482869645213696)), (755580185/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-29137/37778931862957161709568), (-146193/37778931862957161709568)), (1511157781/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((1313/18889465931478580854784), (-12511/37778931862957161709568)), (1511157353/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile038Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-226202929/8388608), (607930689/16777216)), (1837/8388608), by norm_num⟩
  | 1 => ⟨((553007183/16777216), (-143457741/33554432)), (4067/16777216), by norm_num⟩
  | 2 => ⟨((-338042153/16777216), (-986483/2097152)), (17091/67108864), by norm_num⟩
  | 3 => ⟨((1186613603/134217728), (20978823/16777216)), (33507/134217728), by norm_num⟩
  | 4 => ⟨((-401810427/134217728), (-49397241/67108864)), (126239/536870912), by norm_num⟩
  | 5 => ⟨((221065747/268435456), (78369623/268435456)), (236637/1073741824), by norm_num⟩
  | 6 => ⟨((-3179605/16777216), (-24433967/268435456)), (451009/2147483648), by norm_num⟩
  | 7 => ⟨((39871811/1073741824), (395923/16777216)), (1754787/8589934592), by norm_num⟩
  | 8 => ⟨((-1678553/268435456), (-5621893/1073741824)), (27710255/137438953472), by norm_num⟩
  | 9 => ⟨((3891935/4294967296), (2173825/2147483648)), (110253755/549755813888), by norm_num⟩
  | 10 => ⟨((-1921249/17179869184), (-1483913/8589934592)), (880354263/4398046511104), by norm_num⟩
  | 11 => ⟨((24361/2147483648), (1805471/68719476736)), (1759638701/8796093022208), by norm_num⟩
  | 12 => ⟨((-230997/274877906944), (-985709/274877906944)), (1759327917/8796093022208), by norm_num⟩
  | 13 => ⟨((2617/137438953472), (242605/549755813888)), (1759244997/8796093022208), by norm_num⟩
  | 14 => ⟨((4157/549755813888), (-215801/4398046511104)), (1759224535/8796093022208), by norm_num⟩
  | 15 => ⟨((-8083/4398046511104), (21657/4398046511104)), (109951241/549755813888), by norm_num⟩
  | 16 => ⟨((39/137438953472), (-975/2199023255552)), (879609427/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile038Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33979/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33979/1280))
  have he : value ((69/80), (33979/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-509827833/33554432)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-598462386581641/1125899906842624), (-42229236631057/140737488355328)), (11304863/281474976710656), by norm_num⟩
  | 1 => ⟨((653341083/2147483648), (737626179/4294967296)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((-93487383/1073741824), (-211095683/4294967296)), (15/2147483648), by norm_num⟩
  | 3 => ⟨((570761607/34359738368), (80549179/8589934592)), (47/34359738368), by norm_num⟩
  | 4 => ⟨((-1306735739/549755813888), (-184414105/137438953472)), (55/274877906944), by norm_num⟩
  | 5 => ⟨((1196687563/4398046511104), (84441735/549755813888)), (103/4398046511104), by norm_num⟩
  | 6 => ⟨((-228314003/8796093022208), (-515535881/35184372088832)), (5/2199023255552), by norm_num⟩
  | 7 => ⟨((1194778801/562949953421312), (337228189/281474976710656)), (107/562949953421312), by norm_num⟩
  | 8 => ⟨((-1367699001/9007199254740992), (-772070373/9007199254740992)), (125/9007199254740992), by norm_num⟩
  | 9 => ⟨((86980329/9007199254740992), (392805347/72057594037927936)), (65/72057594037927936), by norm_num⟩
  | 10 => ⟨((-1274482971/2305843009213693952), (-22482801/72057594037927936)), (61/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1061046361/36893488147419103232), (598963997/36893488147419103232)), (13/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-809740987/590295810358705651712), (-457101325/590295810358705651712)), (41/295147905179352825856), by norm_num⟩
  | 13 => ⟨((1140842717/18889465931478580854784), (322004645/9444732965739290427392)), (59/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-373130501/151115727451828646838272), (-421266675/302231454903657293676544)), (79/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((911218423/9671406556917033397649408), (64298207/1208925819614629174706176)), (99/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-521549481/154742504910672534362390528), (-588832633/309485009821345068724781056)), (29/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-53482035381/158456325028528675187087900672)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55662519957591/19807040628566084398385987584), (-2030667207205/316912650057057350374175801344)), (17363/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59139903291187/1237940039285380274899124224), (-4568774796659/39614081257132168796771975168)), (39075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946210978750647/1237940039285380274899124224), (-4854075802079/2475880078570760549798248448)), (5191/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774087124749035/154742504910672534362390528), (-2426898629317/77371252455336267181195264)), (41541/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776133842831067/4835703278458516698824704), (-2275069395751/4835703278458516698824704)), (19479/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157645313977487/75557863725914323419136), (-3981075094937/604462909807314587353088)), (17051/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945823680388645/37778931862957161709568), (-6468690933157/75557863725914323419136)), (3465/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((650214527272367/2361183241434822606848), (-4851031171615/4722366482869645213696)), (20801/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812709126228063/295147905179352825856), (-6669375607629/590295810358705651712)), (28619/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828432695387333/73786976294838206464), (-8335529673473/73786976294838206464)), (4475/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1828228400071987/9223372036854775808), (-9375832493307/9223372036854775808)), (80623/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199933623903667/144115188075855872), (-2343445240447/288230376151711744)), (40357/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199369602184621/144115188075855872), (-8199745498223/144115188075855872)), (8841/18014398509481984), by norm_num⟩
  | 4 => ⟨((1498802872501557/36028797018963968), (-6147490197995/18014398509481984)), (53149/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498183416903517/9007199254740992), (-15360581915731/9007199254740992)), (133233/9007199254740992), by norm_num⟩
  | 2 => ⟨((561426587991531/1125899906842624), (-7674155972929/1125899906842624)), (8361/140737488355328), by norm_num⟩
  | 1 => ⟨((1121254254157449/1125899906842624), (-22991602241395/1125899906842624)), (202019/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116307120045941/1125899906842624), (-11464650017097/281474976710656)), (102369/281474976710656), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116307120045941/1125899906842624), (-11464650017097/281474976710656)), (390506745458507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((552464107823627/562949953421312), (-45467879924815/562949953421312)), (211333/281474976710656), by norm_num⟩
  | 2 => ⟨((1077002530992739/1125899906842624), (-178483871005815/1125899906842624)), (448931/281474976710656), by norm_num⟩
  | 3 => ⟨((500967249708293/562949953421312), (-170732388950729/562949953421312)), (2002405/562949953421312), by norm_num⟩
  | 4 => ⟨((788058104616127/1125899906842624), (-607736689977211/1125899906842624)), (4778453/562949953421312), by norm_num⟩
  | 5 => ⟨((223547129169349/1125899906842624), (-850753821185037/1125899906842624)), (47391353/2251799813685248), by norm_num⟩
  | 6 => ⟨((-598462386581641/1125899906842624), (-42229236631057/140737488355328)), (11304863/281474976710656), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-509827833/33554432)), (3/134217728), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((580577749/72057594037927936), (455686943/36028797018963968)), (5765/72057594037927936), by norm_num⟩
  | 1 => ⟨((-264904343/72057594037927936), (546650721/36028797018963968)), (6515/36028797018963968), by norm_num⟩
  | 2 => ⟨((-496836263/72057594037927936), (580481531/144115188075855872)), (8485/36028797018963968), by norm_num⟩
  | 3 => ⟨((-1482661573/576460752303423488), (-417623471/576460752303423488)), (16161/72057594037927936), by norm_num⟩
  | 4 => ⟨((-359741033/1152921504606846976), (-666658845/1152921504606846976)), (404059/2305843009213693952), by norm_num⟩
  | 5 => ⟨((348663469/9223372036854775808), (-278136465/2305843009213693952)), (1149995/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1299270039/73786976294838206464), (-664569301/73786976294838206464)), (830989/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1449176193/590295810358705651712), (236388697/295147905179352825856)), (21155625/295147905179352825856), by norm_num⟩
  | 8 => ⟨((619960303/4722366482869645213696), (1202115455/4722366482869645213696)), (150008891/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-18474295/2361183241434822606848), (247312147/9444732965739290427392)), (285363857/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-18422563/9444732965739290427392), (5428791/4722366482869645213696)), (560885835/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-761243/4722366482869645213696), (-289579/9444732965739290427392)), (1115845281/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-128041/18889465931478580854784), (-151241/18889465931478580854784)), (1114225215/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-225/4722366482869645213696), (-2825/4722366482869645213696)), (69613697/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((135/9444732965739290427392), (-133/4722366482869645213696)), (1113725095/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((3/2361183241434822606848), (-9/9444732965739290427392)), (1113704829/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/9444732965739290427392), 0), (139212593/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1521238925/2251799813685248), (-13820793/281474976710656)), (21597/2251799813685248), by norm_num⟩
  | 1 => ⟨((-589980697/4503599627370496), (-720125949/4503599627370496)), (106081/4503599627370496), by norm_num⟩
  | 2 => ⟨((-194473819/1125899906842624), (-57000865/562949953421312)), (79943/2251799813685248), by norm_num⟩
  | 3 => ⟨((199814397/9007199254740992), (-1684431045/18014398509481984)), (91917/2251799813685248), by norm_num⟩
  | 4 => ⟨((288714893/18014398509481984), (-54978213/72057594037927936)), (2864703/72057594037927936), by norm_num⟩
  | 5 => ⟨((690879373/576460752303423488), (-73728553/288230376151711744)), (10082963/288230376151711744), by norm_num⟩
  | 6 => ⟨((619470105/1152921504606846976), (526074129/2305843009213693952)), (16994631/576460752303423488), by norm_num⟩
  | 7 => ⟨((-151040431/9223372036854775808), (1671189245/18446744073709551616)), (230766559/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-3404981/576460752303423488), (51176679/73786976294838206464)), (1629536631/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-4406039/18446744073709551616), (7026873/36893488147419103232)), (753720359/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-37881/576460752303423488), (-1361109/73786976294838206464)), (180846325/9223372036854775808), by norm_num⟩
  | 11 => ⟨((5607/36893488147419103232), (-349557/73786976294838206464)), (1419721015/73786976294838206464), by norm_num⟩
  | 12 => ⟨((785/18446744073709551616), (-5747/73786976294838206464)), (44023907/2305843009213693952), by norm_num⟩
  | 13 => ⟨((25/4611686018427387904), (-601/36893488147419103232)), (1404696245/73786976294838206464), by norm_num⟩
  | 14 => ⟨((73/73786976294838206464), (-1/73786976294838206464)), (1403300625/73786976294838206464), by norm_num⟩
  | 15 => ⟨(0, (-1/73786976294838206464)), (1402856051/73786976294838206464), by norm_num⟩
  | 16 => ⟨(0, (-1/73786976294838206464)), (1402724155/73786976294838206464), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-760619471/1125899906842624), (-3455199/70368744177664)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-576153/4398046511104), (-180031485/1125899906842624)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-48618457/281474976710656), (-14250217/140737488355328)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((24976807/1125899906842624), (-26319235/281474976710656)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((18044677/1125899906842624), (-429517/562949953421312)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((5271/4398046511104), (-288003/1125899906842624)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((604951/1125899906842624), (256873/1125899906842624)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((-18437/1125899906842624), (102001/1125899906842624)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-3325/562949953421312), (781/1125899906842624)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((-269/1125899906842624), (107/562949953421312)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-37/562949953421312), (-21/1125899906842624)), (1/17179869184), by norm_num⟩
  | 11 => ⟨(0, (-5/1125899906842624)), (1/17179869184), by norm_num⟩
  | 12 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 13 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 14 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 15 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | 16 => ⟨(0, 0), (1/17179869184), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨38,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨38,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(277/536870912)) (L:=(799671179107955/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile038
