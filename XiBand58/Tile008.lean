/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile008Gamma
import XiBand58.Tile008Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile008
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1163574741/140737488355328), (283494949/70368744177664)), (1415/140737488355328), by norm_num⟩
  | 1 => ⟨((443575507/70368744177664), (186091883/17592186044416)), (1465/70368744177664), by norm_num⟩
  | 2 => ⟨((-10063765/35184372088832), (1144489257/140737488355328)), (3125/140737488355328), by norm_num⟩
  | 3 => ⟨((-561474887/281474976710656), (102784021/35184372088832)), (4579/281474976710656), by norm_num⟩
  | 4 => ⟨((-585491127/562949953421312), (259877139/562949953421312)), (1285/140737488355328), by norm_num⟩
  | 5 => ⟨((-161377247/562949953421312), (-20214317/562949953421312)), (9391/2251799813685248), by norm_num⟩
  | 6 => ⟨((-431363475/9007199254740992), (-660742017/18014398509481984)), (14591/9007199254740992), by norm_num⟩
  | 7 => ⟨((-301659019/72057594037927936), (-706491795/72057594037927936)), (20263/36028797018963968), by norm_num⟩
  | 8 => ⟨((87069959/576460752303423488), (-1870864317/1152921504606846976)), (221765/1152921504606846976), by norm_num⟩
  | 9 => ⟨((545684367/4611686018427387904), (-851406707/4611686018427387904)), (184005/2305843009213693952), by norm_num⟩
  | 10 => ⟨((831679835/36893488147419103232), (-503599333/36893488147419103232)), (1823687/36893488147419103232), by norm_num⟩
  | 11 => ⟨((1681117385/590295810358705651712), (-185503647/590295810358705651712)), (24820903/590295810358705651712), by norm_num⟩
  | 12 => ⟨((642374971/2361183241434822606848), (200601723/2361183241434822606848)), (190836413/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((11886351/590295810358705651712), (316479459/18889465931478580854784)), (1514060489/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((41025999/37778931862957161709568), (74136053/37778931862957161709568)), (188958183/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((1032061/37778931862957161709568), (6724965/37778931862957161709568)), (1511241019/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-94407/37778931862957161709568), (506419/37778931862957161709568)), (1511170325/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile008Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((383642335/33554432), (1027828021/33554432)), (3493/16777216), by norm_num⟩
  | 1 => ⟨((-635931685/67108864), (-740636871/67108864)), (14585/67108864), by norm_num⟩
  | 2 => ⟨((664367083/134217728), (763638935/134217728)), (29797/134217728), by norm_num⟩
  | 3 => ⟨((-417846623/268435456), (-575752625/268435456)), (118167/536870912), by norm_num⟩
  | 4 => ⟨((46759309/134217728), (21605327/33554432)), (460273/2147483648), by norm_num⟩
  | 5 => ⟨((-14447735/268435456), (-42665619/268435456)), (1790467/8589934592), by norm_num⟩
  | 6 => ⟨((2234457/536870912), (17590983/536870912)), (1754243/8589934592), by norm_num⟩
  | 7 => ⟨((603895/1073741824), (-3055637/536870912)), (27740079/137438953472), by norm_num⟩
  | 8 => ⟨((-641193/2147483648), (897039/1073741824)), (110340283/549755813888), by norm_num⟩
  | 9 => ⟨((305085/4294967296), (-883773/8589934592)), (1761375149/8796093022208), by norm_num⟩
  | 10 => ⟨((-107041/8589934592), (177415/17179869184)), (1759895981/8796093022208), by norm_num⟩
  | 11 => ⟨((122589/68719476736), (-52709/68719476736)), (1759413549/8796093022208), by norm_num⟩
  | 12 => ⟨((-29717/137438953472), (6585/274877906944)), (1759270253/8796093022208), by norm_num⟩
  | 13 => ⟨((24711/1099511627776), (303/68719476736)), (1759231301/8796093022208), by norm_num⟩
  | 14 => ⟨((-2193/1099511627776), (-4849/4398046511104)), (1759221511/8796093022208), by norm_num⟩
  | 15 => ⟨((1291/8796093022208), (347/2199023255552)), (1759219229/8796093022208), by norm_num⟩
  | 16 => ⟨((-9/1099511627776), (-155/8796093022208)), (1759218731/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile008Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2991/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2991/160))
  have he : value ((15/16), (2991/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-359020583/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-191994248695845/1125899906842624), (314869336695535/562949953421312)), (3472657/140737488355328), by norm_num⟩
  | 1 => ⟨((419200047/4294967296), (-1374970779/4294967296)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((-239935411/8589934592), (1573970143/17179869184)), (75/17179869184), by norm_num⟩
  | 3 => ⟨((366214981/68719476736), (-600590221/34359738368)), (59/68719476736), by norm_num⟩
  | 4 => ⟨((-209608617/274877906944), (1375027151/549755813888)), (35/274877906944), by norm_num⟩
  | 5 => ⟨((383912397/4398046511104), (-1259227739/4398046511104)), (33/2199023255552), by norm_num⟩
  | 6 => ⟨((-73245999/8796093022208), (960983751/35184372088832)), (13/8796093022208), by norm_num⟩
  | 7 => ⟨((191650021/281474976710656), (-1257219223/562949953421312)), (35/281474976710656), by norm_num⟩
  | 8 => ⟨((-438775013/9007199254740992), (719588209/4503599627370496)), (83/9007199254740992), by norm_num⟩
  | 9 => ⟨((446470107/144115188075855872), (-1464416229/144115188075855872)), (87/144115188075855872), by norm_num⟩
  | 10 => ⟨((-102217535/576460752303423488), (1341088819/2305843009213693952)), (41/1152921504606846976), by norm_num⟩
  | 11 => ⟨((85099249/9223372036854775808), (-1116497783/36893488147419103232)), (71/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-64943769/147573952589676412928), (106507365/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 13 => ⟨((365996669/18889465931478580854784), (-600232191/9444732965739290427392)), (81/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-59852475/75557863725914323419136), (785261403/302231454903657293676544)), (109/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((36541289/1208925819614629174706176), (-239709919/2417851639229258349412352)), (17/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((-334639245/309485009821345068724781056), (1097612433/309485009821345068724781056)), (5/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (607903930541/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890569321619965/316912650057057350374175801344), (721248815043/158456325028528675187087900672)), (11561/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946203715070463/19807040628566084398385987584), (3245454314373/39614081257132168796771975168)), (813/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((946174233218359/1237940039285380274899124224), (1724052662525/1237940039285380274899124224)), (27/2417851639229258349412352), by norm_num⟩
  | 14 => ⟨((443503500193775/38685626227668133590597632), (1723945821769/77371252455336267181195264)), (27653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552199521915807/9671406556917033397649408), (1616085661593/4835703278458516698824704)), (25931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261103258459743/604462909807314587353088), (706980688039/151115727451828646838272)), (2837/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472887951258141/18889465931478580854784), (2297474210811/37778931862957161709568)), (36893/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300358027200367/4722366482869645213696), (1722919194077/2361183241434822606848)), (865/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1625321628741617/590295810358705651712), (2368710762469/295147905179352825856)), (9519/147573952589676412928), by norm_num⟩
  | 8 => ⟨((457078368410075/18446744073709551616), (5920867079595/73786976294838206464)), (47621/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828096417013969/9223372036854775808), (3329861870529/4611686018427387904)), (6701/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399834920969721/288230376151711744), (1664539504909/288230376151711744)), (53651/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599629733487295/72057594037927936), (2912062682375/72057594037927936)), (23497/72057594037927936), by norm_num⟩
  | 4 => ⟨((93665230218515/2251799813685248), (136447790341/562949953421312)), (70587/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497994946611039/9007199254740992), (10909638438409/9007199254740992)), (88405/9007199254740992), by norm_num⟩
  | 2 => ⟨((70167528947657/140737488355328), (5450172417201/1125899906842624)), (88661/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121034520638157/1125899906842624), (8163612948677/562949953421312)), (261/2199023255552), by norm_num⟩
  | 0 => ⟨((1116024645584277/1125899906842624), (16280471669195/562949953421312)), (33729/140737488355328), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116024645584277/1125899906842624), (16280471669195/562949953421312)), (128665924609136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1105294340071717/1125899906842624), (32275351501735/562949953421312)), (550539/1125899906842624), by norm_num⟩
  | 2 => ⟨((1081365028575769/1125899906842624), (63369333493833/562949953421312)), (1144055/1125899906842624), by norm_num⟩
  | 3 => ⟨((512162594697713/562949953421312), (30431382358203/140737488355328)), (1227585/562949953421312), by norm_num⟩
  | 4 => ⟨((27477289209687/35184372088832), (55371940806081/140737488355328)), (1382275/281474976710656), by norm_num⟩
  | 5 => ⟨((512384925080617/1125899906842624), (345942415067465/562949953421312)), (811667/70368744177664), by norm_num⟩
  | 6 => ⟨((-191994248695845/1125899906842624), (314869336695535/562949953421312)), (3472657/140737488355328), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-359020583/33554432)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-515547715/140737488355328), (1108249873/281474976710656)), (269/35184372088832), by norm_num⟩
  | 1 => ⟨((-344439931/70368744177664), (-149653769/281474976710656)), (1407/70368744177664), by norm_num⟩
  | 2 => ⟨((-38633439/35184372088832), (-265617503/140737488355328)), (14983/562949953421312), by norm_num⟩
  | 3 => ⟨((282530797/1125899906842624), (-641291645/1125899906842624)), (54485/2251799813685248), by norm_num⟩
  | 4 => ⟨((1123475945/9007199254740992), (-236651921/9007199254740992)), (151175/9007199254740992), by norm_num⟩
  | 5 => ⟨((262115593/18014398509481984), (970316127/72057594037927936)), (340181/36028797018963968), by norm_num⟩
  | 6 => ⟨((-93651165/288230376151711744), (1374429471/576460752303423488)), (2586339/576460752303423488), by norm_num⟩
  | 7 => ⟨((-58809711/288230376151711744), (481998973/4611686018427387904)), (8583397/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-1096797375/73786976294838206464), (-573793803/73786976294838206464)), (51799607/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-90394237/590295810358705651712), (-1006263929/1180591620717411303424)), (153883059/590295810358705651712), by norm_num⟩
  | 10 => ⟨((36762633/4722366482869645213696), (-404985971/18889465931478580854784)), (132818865/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-9268509/9444732965739290427392), (-8487055/4722366482869645213696)), (1282445951/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1365841/18889465931478580854784), (-8764307/37778931862957161709568)), (1052136653/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((565273/37778931862957161709568), (-108771/37778931862957161709568)), (994411561/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((8131/37778931862957161709568), (18109/37778931862957161709568)), (245258483/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((-113/9444732965739290427392), (-483/37778931862957161709568)), (489073831/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((81/37778931862957161709568), (-19/18889465931478580854784)), (488782267/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-89329093/549755813888), (-295516665/4398046511104)), (16749/8796093022208), by norm_num⟩
  | 1 => ⟨((21159059/549755813888), (-1344890827/8796093022208)), (16623/4398046511104), by norm_num⟩
  | 2 => ⟨((1591725911/35184372088832), (87719987/35184372088832)), (179417/35184372088832), by norm_num⟩
  | 3 => ⟨((399043685/140737488355328), (85300851/35184372088832)), (1548689/281474976710656), by norm_num⟩
  | 4 => ⟨((54087609/35184372088832), (505569071/562949953421312)), (2962837/562949953421312), by norm_num⟩
  | 5 => ⟨((-128420309/1125899906842624), (57239159/140737488355328)), (10682711/2251799813685248), by norm_num⟩
  | 6 => ⟨((-6194805/140737488355328), (-160015275/36028797018963968)), (38058959/9007199254740992), by norm_num⟩
  | 7 => ⟨((-159039779/288230376151711744), (-443589207/288230376151711744)), (553959179/144115188075855872), by norm_num⟩
  | 8 => ⟨((-89354841/576460752303423488), (-44074587/576460752303423488)), (260413773/72057594037927936), by norm_num⟩
  | 9 => ⟨((593871/288230376151711744), (-11403867/576460752303423488)), (2014835789/576460752303423488), by norm_num⟩
  | 10 => ⟨((72371/144115188075855872), (-146211/576460752303423488)), (495922953/144115188075855872), by norm_num⟩
  | 11 => ⟨((12307/576460752303423488), (-30677/576460752303423488)), (1971002329/576460752303423488), by norm_num⟩
  | 12 => ⟨((2369/576460752303423488), (-41/288230376151711744)), (491577753/144115188075855872), by norm_num⟩
  | 13 => ⟨((27/288230376151711744), (-37/576460752303423488)), (982360829/288230376151711744), by norm_num⟩
  | 14 => ⟨((11/576460752303423488), (1/576460752303423488)), (1964224207/576460752303423488), by norm_num⟩
  | 15 => ⟨(0, 0), (1964079391/576460752303423488), by norm_num⟩
  | 16 => ⟨(0, 0), (122752497/36028797018963968), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-11434123713/70368744177664), (-9456533289/140737488355328)), (1/268435456), by norm_num⟩
  | 1 => ⟨((21666877081/562949953421312), (-86073012139/562949953421312)), (1/134217728), by norm_num⟩
  | 2 => ⟨((50935228513/1125899906842624), (350880171/140737488355328)), (1/67108864), by norm_num⟩
  | 3 => ⟨((1596174641/562949953421312), (1364813109/562949953421312)), (1/67108864), by norm_num⟩
  | 4 => ⟨((1730803659/1125899906842624), (1011138717/1125899906842624)), (1/67108864), by norm_num⟩
  | 5 => ⟨((-64210197/562949953421312), (457913025/1125899906842624)), (1/67108864), by norm_num⟩
  | 6 => ⟨((-49558377/1125899906842624), (-1250097/281474976710656)), (1/67108864), by norm_num⟩
  | 7 => ⟨((-310625/562949953421312), (-866405/562949953421312)), (1/67108864), by norm_num⟩
  | 8 => ⟨((-87251/562949953421312), (-86067/1125899906842624)), (1/67108864), by norm_num⟩
  | 9 => ⟨((1159/562949953421312), (-22273/1125899906842624)), (1/67108864), by norm_num⟩
  | 10 => ⟨((71/140737488355328), (-285/1125899906842624)), (1/67108864), by norm_num⟩
  | 11 => ⟨((3/140737488355328), (-59/1125899906842624)), (1/67108864), by norm_num⟩
  | 12 => ⟨((5/1125899906842624), 0), (1/67108864), by norm_num⟩
  | 13 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | 14 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | 15 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | 16 => ⟨(0, 0), (1/67108864), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨8,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨8,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(163873/524288)) (K:=(232905/536870912)) (L:=(103793793083747463/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile008
