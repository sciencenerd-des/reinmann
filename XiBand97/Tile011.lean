/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile011Gamma
import XiBand97.Tile011Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile011
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((31308039/35184372088832), (618908339/140737488355328)), (357/70368744177664), by norm_num⟩
  | 1 => ⟨((-39206861/17592186044416), (399617917/70368744177664)), (1535/140737488355328), by norm_num⟩
  | 2 => ⟨((-931949667/281474976710656), (679658035/281474976710656)), (3333/281474976710656), by norm_num⟩
  | 3 => ⟨((-1017877093/562949953421312), (72763239/562949953421312)), (1219/140737488355328), by norm_num⟩
  | 4 => ⟨((-1187451267/2251799813685248), (-153881447/562949953421312)), (10847/2251799813685248), by norm_num⟩
  | 5 => ⟨((-182018397/2251799813685248), (-589134825/4503599627370496)), (9859/4503599627370496), by norm_num⟩
  | 6 => ⟨((-31198227/36028797018963968), (-147536529/4503599627370496)), (1929/2251799813685248), by norm_num⟩
  | 7 => ⟨((199492915/72057594037927936), (-753475647/144115188075855872)), (44527/144115188075855872), by norm_num⟩
  | 8 => ⟨((444003777/576460752303423488), (-143825/281474976710656)), (136345/1152921504606846976), by norm_num⟩
  | 9 => ⟨((1166065469/9223372036854775808), (-122524061/9223372036854775808)), (557287/9223372036854775808), by norm_num⟩
  | 10 => ⟨((539397337/36893488147419103232), (403423139/73786976294838206464)), (3308343/73786976294838206464), by norm_num⟩
  | 11 => ⟨((355909809/295147905179352825856), (734075033/590295810358705651712)), (24231543/590295810358705651712), by norm_num⟩
  | 12 => ⟨((564420761/9444732965739290427392), (1559594213/9444732965739290427392)), (379778299/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-17200757/18889465931478580854784), (154828163/9444732965739290427392)), (94540147/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-11458003/18889465931478580854784), (48809347/37778931862957161709568)), (1511416775/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-3161641/37778931862957161709568), (190245/2361183241434822606848)), (755599971/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-153727/18889465931478580854784), (136441/37778931862957161709568)), (755581953/18889465931478580854784), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile011Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((580089133/33554432), (40897593/2097152)), (3511/16777216), by norm_num⟩
  | 1 => ⟨((-262785237/16777216), (17348639/16777216)), (14845/67108864), by norm_num⟩
  | 2 => ⟨((146245001/16777216), (-79240613/134217728)), (30543/134217728), by norm_num⟩
  | 3 => ⟨((-108640821/33554432), (332667/8388608)), (121047/536870912), by norm_num⟩
  | 4 => ⟨((7821001/8388608), (12133441/134217728)), (234461/1073741824), by norm_num⟩
  | 5 => ⟨((-58070387/268435456), (-14698643/268435456)), (452857/2147483648), by norm_num⟩
  | 6 => ⟨((172821/4194304), (10193377/536870912)), (1764899/8589934592), by norm_num⟩
  | 7 => ⟨((-6950509/1073741824), (-2593153/536870912)), (27815087/137438953472), by norm_num⟩
  | 8 => ⟨((1776565/2147483648), (2107673/2147483648)), (110456507/549755813888), by norm_num⟩
  | 9 => ⟨((-348599/4294967296), (-1426535/8589934592)), (881005527/4398046511104), by norm_num⟩
  | 10 => ⟨((81311/17179869184), (411241/17179869184)), (1760096685/8796093022208), by norm_num⟩
  | 11 => ⟨((15507/68719476736), (-204223/68719476736)), (1759470253/8796093022208), by norm_num⟩
  | 12 => ⟨((-16293/137438953472), (21853/68719476736)), (1759284877/8796093022208), by norm_num⟩
  | 13 => ⟨((24029/1099511627776), (-7953/274877906944)), (1759234813/8796093022208), by norm_num⟩
  | 14 => ⟨((-6515/2199023255552), (9409/4398046511104)), (1759222303/8796093022208), by norm_num⟩
  | 15 => ⟨((729/2199023255552), (-241/2199023255552)), (1759219395/8796093022208), by norm_num⟩
  | 16 => ⟨((-35/1099511627776), (1/8796093022208)), (1759218763/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile011Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (25029/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (25029/1280))
  have he : value ((69/80), (25029/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-375540211/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((268207781286907/2251799813685248), (1348043195093663/2251799813685248)), (50510981/2251799813685248), by norm_num⟩
  | 1 => ⟨((-146401149/2147483648), (-1471658071/4294967296)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((335179541/17179869184), (52645343/536870912)), (69/17179869184), by norm_num⟩
  | 3 => ⟨((-255793359/68719476736), (-40176465/2147483648)), (55/68719476736), by norm_num⟩
  | 4 => ⟨((292814303/549755813888), (1471718407/549755813888)), (33/274877906944), by norm_num⟩
  | 5 => ⟨((-268154627/4398046511104), (-336944009/1099511627776)), (63/4398046511104), by norm_num⟩
  | 6 => ⟨((204643077/35184372088832), (128569959/4398046511104)), (25/17592186044416), by norm_num⟩
  | 7 => ⟨((-133863455/281474976710656), (-1345626281/562949953421312)), (17/140737488355328), by norm_num⟩
  | 8 => ⟨((306474995/9007199254740992), (385094655/2251799813685248)), (81/9007199254740992), by norm_num⟩
  | 9 => ⟨((-155924927/72057594037927936), (-783696641/72057594037927936)), (85/144115188075855872), by norm_num⟩
  | 10 => ⟨((142793539/1152921504606846976), (1435393547/2305843009213693952)), (5/144115188075855872), by norm_num⟩
  | 11 => ⟨((-118880023/18446744073709551616), (-37344043/1152921504606846976)), (69/36893488147419103232), by norm_num⟩
  | 12 => ⟨((90723677/295147905179352825856), (455987649/295147905179352825856)), (27/295147905179352825856), by norm_num⟩
  | 13 => ⟨((-31955109/2361183241434822606848), (-1284880467/18889465931478580854784)), (79/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((20902839/37778931862957161709568), (210120153/75557863725914323419136)), (53/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((-51046623/2417851639229258349412352), (-1026264827/9671406556917033397649408)), (33/4835703278458516698824704), by norm_num⟩
  | 16 => ⟨((58434595/77371252455336267181195264), (1174796019/309485009821345068724781056)), (39/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (1790309682591/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890603509537723/316912650057057350374175801344), (531066637797/158456325028528675187087900672)), (23103/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236560559106713/4951760157141521099596496896), (2389690005881/39614081257132168796771975168)), (12997/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892430470357623/2475880078570760549798248448), (1269458636689/1237940039285380274899124224)), (27623/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887048084484273/77371252455336267181195264), (2538772850249/154742504910672534362390528)), (27627/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((194034591138069/1208925819614629174706176), (1189973039661/4835703278458516698824704)), (25905/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630585494610545/302231454903657293676544), (1041149665569/302231454903657293676544)), (1417/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((472915548644077/18889465931478580854784), (211465536193/4722366482869645213696)), (36849/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325110276363925/1180591620717411303424), (317166817009/590295810358705651712)), (27645/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812718163053413/295147905179352825856), (3488425570965/590295810358705651712)), (4753/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828457542240273/73786976294838206464), (1089979424247/18446744073709551616)), (47547/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828259452006573/9223372036854775808), (1226015640239/2305843009213693952)), (53517/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799751957763433/576460752303423488), (4903006153929/1152921504606846976)), (53549/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599702257527699/72057594037927936), (4288941450367/144115188075855872)), (46891/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498863944272221/36028797018963968), (6431033117311/36028797018963968)), (8801/4503599627370496), by norm_num⟩
  | 3 => ⟨((749137486472873/4503599627370496), (4017312686041/4503599627370496)), (44067/4503599627370496), by norm_num⟩
  | 2 => ⟨((140370941308815/281474976710656), (8028370999867/2251799813685248)), (88323/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121482690473241/1125899906842624), (6013450969977/562949953421312)), (33239/281474976710656), by norm_num⟩
  | 0 => ⟨((1116991058971929/1125899906842624), (5997768555185/281474976710656)), (133899/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116991058971929/1125899906842624), (5997768555185/281474976710656)), (510784151317405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1107641493352821/1125899906842624), (185947197915/4398046511104)), (135693/281474976710656), by norm_num⟩
  | 2 => ⟨((543833281270557/562949953421312), (93661052225499/1125899906842624)), (1113837/1125899906842624), by norm_num⟩
  | 3 => ⟨((521470048727053/562949953421312), (180961014560829/1125899906842624)), (2337343/1125899906842624), by norm_num⟩
  | 4 => ⟨((468503972544585/562949953421312), (167627243784687/562949953421312)), (317599/70368744177664), by norm_num⟩
  | 5 => ⟨((679979022177713/1125899906842624), (558017842563355/1125899906842624)), (2871085/281474976710656), by norm_num⟩
  | 6 => ⟨((268207781286907/2251799813685248), (1348043195093663/2251799813685248)), (50510981/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-375540211/33554432)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-1422376769/562949953421312), (148687457/140737488355328)), (1059/281474976710656), by norm_num⟩
  | 1 => ⟨((-624585789/281474976710656), (-355355821/281474976710656)), (5721/562949953421312), by norm_num⟩
  | 2 => ⟨((-10974211/70368744177664), (-644554427/562949953421312)), (1947/140737488355328), by norm_num⟩
  | 3 => ⟨((269038279/1125899906842624), (-66969039/281474976710656)), (28451/2251799813685248), by norm_num⟩
  | 4 => ⟨((1265535089/18014398509481984), (183845293/18014398509481984)), (157501/18014398509481984), by norm_num⟩
  | 5 => ⟨((390837495/72057594037927936), (723832747/72057594037927936)), (353081/72057594037927936), by norm_num⟩
  | 6 => ⟨((-44255499/72057594037927936), (377156249/288230376151711744)), (1340971/576460752303423488), by norm_num⟩
  | 7 => ⟨((-164823567/1152921504606846976), (265793171/9223372036854775808)), (4492331/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-321618479/36893488147419103232), (-284691063/36893488147419103232)), (14067419/36893488147419103232), by norm_num⟩
  | 9 => ⟨((67771759/2361183241434822606848), (-834859677/1180591620717411303424)), (92527871/590295810358705651712), by norm_num⟩
  | 10 => ⟨((192274017/9444732965739290427392), (-49892919/2361183241434822606848)), (770792123/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((10923977/18889465931478580854784), (-252493/295147905179352825856)), (1115284861/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((2971105/37778931862957161709568), (-3558465/37778931862957161709568)), (124867489/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((90621/9444732965739290427392), (-701/2361183241434822606848)), (969806651/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((4647/18889465931478580854784), (111/295147905179352825856)), (963059991/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-213/37778931862957161709568), (233/37778931862957161709568)), (480802711/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((25/37778931862957161709568), (-9/37778931862957161709568)), (1922623605/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-565446303/8796093022208), (-272756753/8796093022208)), (15627/17592186044416), by norm_num⟩
  | 1 => ⟨((435257799/17592186044416), (-741156481/8796093022208)), (34445/17592186044416), by norm_num⟩
  | 2 => ⟨((1206587979/35184372088832), (188079205/35184372088832)), (90475/35184372088832), by norm_num⟩
  | 3 => ⟨((63108853/140737488355328), (359133275/70368744177664)), (392721/140737488355328), by norm_num⟩
  | 4 => ⟨((300255443/1125899906842624), (109193383/281474976710656)), (188889/70368744177664), by norm_num⟩
  | 5 => ⟨((-158741545/2251799813685248), (473492865/2251799813685248)), (5492799/2251799813685248), by norm_num⟩
  | 6 => ⟨((-292572225/9007199254740992), (-93798513/18014398509481984)), (78953461/36028797018963968), by norm_num⟩
  | 7 => ⟨((-23525175/288230376151711744), (-603929389/288230376151711744)), (144643153/72057594037927936), by norm_num⟩
  | 8 => ⟨((-14483311/576460752303423488), (-25916521/576460752303423488)), (1092521799/576460752303423488), by norm_num⟩
  | 9 => ⟨((1609047/576460752303423488), (-15953619/1152921504606846976)), (2117328079/1152921504606846976), by norm_num⟩
  | 10 => ⟨((909671/1152921504606846976), (-31011/576460752303423488)), (2085983157/1152921504606846976), by norm_num⟩
  | 11 => ⟨((8713/576460752303423488), (-7161/576460752303423488)), (1036468959/576460752303423488), by norm_num⟩
  | 12 => ⟨((3975/1152921504606846976), (265/576460752303423488)), (516998611/288230376151711744), by norm_num⟩
  | 13 => ⟨((31/1152921504606846976), (1/9007199254740992)), (516568315/288230376151711744), by norm_num⟩
  | 14 => ⟨((-1/1152921504606846976), (-3/576460752303423488)), (2065718551/1152921504606846976), by norm_num⟩
  | 15 => ⟨((1/576460752303423488), (-3/1152921504606846976)), (258194015/144115188075855872), by norm_num⟩
  | 16 => ⟨((1/1152921504606846976), (1/1152921504606846976)), (516376351/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-72377127203/1125899906842624), (-17456433559/562949953421312)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((13928251063/562949953421312), (-23717007529/281474976710656)), (1/268435456), by norm_num⟩
  | 2 => ⟨((38610815289/1125899906842624), (1504633797/281474976710656)), (1/134217728), by norm_num⟩
  | 3 => ⟨((504871267/1125899906842624), (718266583/140737488355328)), (1/134217728), by norm_num⟩
  | 4 => ⟨((300255049/1125899906842624), (436773647/1125899906842624)), (1/134217728), by norm_num⟩
  | 5 => ⟨((-9921327/140737488355328), (118373171/562949953421312)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-36571615/1125899906842624), (-5862339/1125899906842624)), (1/134217728), by norm_num⟩
  | 7 => ⟨((-45939/562949953421312), (-2359151/1125899906842624)), (1/134217728), by norm_num⟩
  | 8 => ⟨((-28283/1125899906842624), (-50601/1125899906842624)), (1/134217728), by norm_num⟩
  | 9 => ⟨((1571/562949953421312), (-15581/1125899906842624)), (1/134217728), by norm_num⟩
  | 10 => ⟨((889/1125899906842624), (-59/1125899906842624)), (1/134217728), by norm_num⟩
  | 11 => ⟨((17/1125899906842624), (-7/562949953421312)), (1/134217728), by norm_num⟩
  | 12 => ⟨((1/281474976710656), (1/1125899906842624)), (1/134217728), by norm_num⟩
  | 13 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | 14 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | 15 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | 16 => ⟨(0, 0), (1/134217728), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨11,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨11,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(33641/268435456)) (L:=(84261135300307501/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile011
