/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile031Gamma
import XiBand97.Tile031Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile031
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((280886623/18014398509481984), (403832709/4503599627370496)), (469/2251799813685248), by norm_num⟩
  | 1 => ⟨((-106769719/2251799813685248), (561380657/4503599627370496)), (903/2251799813685248), by norm_num⟩
  | 2 => ⟨((-340361997/4503599627370496), (136720219/2251799813685248)), (245/562949953421312), by norm_num⟩
  | 3 => ⟨((-207481871/4503599627370496), (254129625/36028797018963968)), (6007/18014398509481984), by norm_num⟩
  | 4 => ⟨((-70088477/4503599627370496), (-430779395/72057594037927936)), (14833/72057594037927936), by norm_num⟩
  | 5 => ⟨((-27206019/9007199254740992), (-1050236575/288230376151711744)), (33403/288230376151711744), by norm_num⟩
  | 6 => ⟨((-29870593/144115188075855872), (-1258256341/1152921504606846976)), (39923/576460752303423488), by norm_num⟩
  | 7 => ⟨((9709213/144115188075855872), (-487184697/2305843009213693952)), (7171/144115188075855872), by norm_num⟩
  | 8 => ⟨((63362483/2305843009213693952), (-992084157/36893488147419103232)), (790819/18446744073709551616), by norm_num⟩
  | 9 => ⟨((830244965/147573952589676412928), (-253690685/147573952589676412928)), (6014447/147573952589676412928), by norm_num⟩
  | 10 => ⟨((936110905/1180591620717411303424), (161878287/1180591620717411303424)), (47436189/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((760047551/9444732965739290427392), (551953849/9444732965739290427392)), (378159701/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((25250203/4722366482869645213696), (186046563/18889465931478580854784)), (1511454781/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((350871/4722366482869645213696), (21874321/18889465931478580854784)), (1511212735/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-1466723/37778931862957161709568), (3935123/37778931862957161709568)), (1511166931/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-129667/18889465931478580854784), (16885/2361183241434822606848)), (755579427/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-7165/9444732965739290427392), (6235/18889465931478580854784)), (1511157519/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile031Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((75117435/67108864), (729220955/67108864)), (29045/134217728), by norm_num⟩
  | 1 => ⟨((-628217111/67108864), (557333025/33554432)), (3995/16777216), by norm_num⟩
  | 2 => ⟨((684894557/67108864), (-326435763/33554432)), (16711/67108864), by norm_num⟩
  | 3 => ⟨((-368140537/67108864), (499753419/134217728)), (16423/67108864), by norm_num⟩
  | 4 => ⟨((139072751/67108864), (-276246477/268435456)), (124447/536870912), by norm_num⟩
  | 5 => ⟨((-81984187/134217728), (56444519/268435456)), (469329/2147483648), by norm_num⟩
  | 6 => ⟨((39802739/268435456), (-3983901/134217728)), (1796707/8589934592), by norm_num⟩
  | 7 => ⟨((-32828205/1073741824), (891079/536870912)), (1751787/8589934592), by norm_num⟩
  | 8 => ⟨((5856875/1073741824), (1180173/2147483648)), (27693167/137438953472), by norm_num⟩
  | 9 => ⟨((-7310763/8589934592), (-1998601/8589934592)), (110230651/549755813888), by norm_num⟩
  | 10 => ⟨((2004489/17179869184), (955603/17179869184)), (1760595885/8796093022208), by norm_num⟩
  | 11 => ⟨((-482017/34359738368), (-708567/68719476736)), (1759606573/8796093022208), by norm_num⟩
  | 12 => ⟨((401923/274877906944), (442157/274877906944)), (1759319597/8796093022208), by norm_num⟩
  | 13 => ⟨((-35147/274877906944), (-240429/1099511627776)), (1759242981/8796093022208), by norm_num⟩
  | 14 => ⟨((37385/4398046511104), (115973/4398046511104)), (1759224069/8796093022208), by norm_num⟩
  | 15 => ⟨((-2177/8796093022208), (-6261/2199023255552)), (219902469/1099511627776), by norm_num⟩
  | 16 => ⟨((-89/2199023255552), (1215/4398046511104)), (109951177/549755813888), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile031Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63483/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63483/2560))
  have he : value ((69/80), (63483/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-952511855/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-19357942638943/562949953421312), (-343070709793329/562949953421312)), (54792729/2251799813685248), by norm_num⟩
  | 1 => ⟨((84532225/4294967296), (749060239/2147483648)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((-24191641/4294967296), (-428735821/4294967296)), (37/8589934592), by norm_num⟩
  | 3 => ⟨((73847719/68719476736), (654382277/34359738368)), (59/68719476736), by norm_num⟩
  | 4 => ⟨((-84535691/549755813888), (-1498181899/549755813888)), (69/549755813888), by norm_num⟩
  | 5 => ⟨((38708213/2199023255552), (343002719/1099511627776)), (33/2199023255552), by norm_num⟩
  | 6 => ⟨((-29540299/17592186044416), (-1047054569/35184372088832)), (13/8796093022208), by norm_num⟩
  | 7 => ⟨((4830809/35184372088832), (684911233/281474976710656)), (35/281474976710656), by norm_num⟩
  | 8 => ⟨((-88479543/9007199254740992), (-392019179/2251799813685248)), (41/4503599627370496), by norm_num⟩
  | 9 => ⟨((90031269/144115188075855872), (797788569/72057594037927936)), (43/72057594037927936), by norm_num⟩
  | 10 => ⟨((-82449187/2305843009213693952), (-365300967/576460752303423488)), (81/2305843009213693952), by norm_num⟩
  | 11 => ⟨((34320745/18446744073709551616), (76031079/2305843009213693952)), (35/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-104767953/1180591620717411303424), (-1856747699/1180591620717411303424)), (55/590295810358705651712), by norm_num⟩
  | 13 => ⟨((73803697/18889465931478580854784), (653992179/9444732965739290427392)), (5/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-48277313/302231454903657293676544), (-1711187183/604462909807314587353088)), (107/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((29474391/4835703278458516698824704), (522359229/4835703278458516698824704)), (67/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-67480433/309485009821345068724781056), (-597960221/154742504910672534362390528)), (79/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-264945034705/1267650600228229401496703205376)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((27831344593309/9903520314283042199192993792), (-2514934173011/633825300114114700748351602688)), (2889/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((946241664094455/19807040628566084398385987584), (-1414584671027/19807040628566084398385987584)), (13003/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((946214591349899/1237940039285380274899124224), (-3005840273403/2475880078570760549798248448)), (27635/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774094800936047/154742504910672534362390528), (-1502834531379/77371252455336267181195264)), (3455/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((194034420148627/1208925819614629174706176), (-2817632799303/9671406556917033397649408)), (25919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630584853462287/302231454903657293676544), (-2465246712185/604462909807314587353088)), (5671/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((118228746925379/4722366482869645213696), (-2002842297979/37778931862957161709568)), (4609/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1300439282625555/4722366482869645213696), (-1501982357123/2361183241434822606848)), (27663/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406358398067449/147573952589676412928), (-4129965881559/590295810358705651712)), (38051/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914226891938947/36893488147419103232), (-2580864335783/36893488147419103232)), (47585/73786976294838206464), by norm_num⟩
  | 7 => ⟨((57132961095291/288230376151711744), (-2902971182973/4611686018427387904)), (53563/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799749316409857/576460752303423488), (-725586087305/144115188075855872)), (53601/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599699617030723/72057594037927936), (-1269422825067/36028797018963968)), (46943/144115188075855872), by norm_num⟩
  | 4 => ⟨((374713676597557/9007199254740992), (-7613711993857/36028797018963968)), (17625/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498261123844397/9007199254740992), (-9512191071909/9007199254740992)), (88273/9007199254740992), by norm_num⟩
  | 2 => ⟨((561475116310985/1125899906842624), (-1188094651941/281474976710656)), (88497/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121448135421485/1125899906842624), (-14238514594405/1125899906842624)), (66651/562949953421312), by norm_num⟩
  | 0 => ⟨((1116887597468715/1125899906842624), (-7100581340883/281474976710656)), (268841/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116887597468715/1125899906842624), (-7100581340883/281474976710656)), (1025547031882857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((553615470485883/562949953421312), (-56349955702117/1125899906842624)), (546943/1125899906842624), by norm_num⟩
  | 2 => ⟨((543025641847091/562949953421312), (-110831192180733/1125899906842624)), (1130497/1125899906842624), by norm_num⟩
  | 3 => ⟨((518351511781735/562949953421312), (-53454289235529/281474976710656)), (600885/281474976710656), by norm_num⟩
  | 4 => ⟨((913967019811351/1125899906842624), (-196877974449127/562949953421312)), (5339153/1125899906842624), by norm_num⟩
  | 5 => ⟨((302110321652761/562949953421312), (-639275212583939/1125899906842624)), (12402761/1125899906842624), by norm_num⟩
  | 6 => ⟨((-19357942638943/562949953421312), (-343070709793329/562949953421312)), (54792729/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-952511855/67108864)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((121843715/2251799813685248), (-885635/70368744177664)), (2463/18014398509481984), by norm_num⟩
  | 1 => ⟨((839916447/18014398509481984), (71636191/2251799813685248)), (6137/18014398509481984), by norm_num⟩
  | 2 => ⟨((72967973/18014398509481984), (1002396823/36028797018963968)), (4109/9007199254740992), by norm_num⟩
  | 3 => ⟨((-830654075/144115188075855872), (1021969597/144115188075855872)), (61339/144115188075855872), by norm_num⟩
  | 4 => ⟨((-625926925/288230376151711744), (78250793/576460752303423488)), (179859/576460752303423488), by norm_num⟩
  | 5 => ⟨((-337103371/1152921504606846976), (-321128103/1152921504606846976)), (452983/2305843009213693952), by norm_num⟩
  | 6 => ⟨((2787597/4611686018427387904), (-1119138741/18446744073709551616)), (270673/2305843009213693952), by norm_num⟩
  | 7 => ⟨((51155617/9223372036854775808), (-379374625/73786976294838206464)), (2771287/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1874161395/2361183241434822606848), (26149155/590295810358705651712)), (132954381/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((55918043/1180591620717411303424), (1004648967/18889465931478580854784)), (927363571/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-3570913/18889465931478580854784), (206706697/37778931862957161709568)), (1762535483/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-9404783/37778931862957161709568), (624423/2361183241434822606848)), (867294535/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-196009/9444732965739290427392), (64331/18889465931478580854784)), (1726904381/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((-38459/37778931862957161709568), (-1969/4722366482869645213696)), (1724968885/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-89/2361183241434822606848), (-783/18889465931478580854784)), (431129707/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-35/37778931862957161709568), (-105/37778931862957161709568)), (862210783/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/37778931862957161709568), (-5/37778931862957161709568)), (1724401919/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((222168435/1125899906842624), (646130279/1125899906842624)), (1131/70368744177664), by norm_num⟩
  | 1 => ⟨((-332692189/562949953421312), (438765879/281474976710656)), (22795/562949953421312), by norm_num⟩
  | 2 => ⟨((-14651981/17592186044416), (-58024735/562949953421312)), (133361/2251799813685248), by norm_num⟩
  | 3 => ⟨((-108494469/2251799813685248), (-239285529/2251799813685248)), (1253/17592186044416), by norm_num⟩
  | 4 => ⟨((-1108630349/36028797018963968), (-426994831/18014398509481984)), (1325887/18014398509481984), by norm_num⟩
  | 5 => ⟨((73488355/18014398509481984), (-465318383/36028797018963968)), (4953571/72057594037927936), by norm_num⟩
  | 6 => ⟨((274074215/144115188075855872), (130939061/576460752303423488)), (35001549/576460752303423488), by norm_num⟩
  | 7 => ⟨((35344931/1152921504606846976), (110630157/1152921504606846976)), (490457745/9223372036854775808), by norm_num⟩
  | 8 => ⟨((371473537/36893488147419103232), (122914511/18446744073709551616)), (110193803/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-8559317/18446744073709551616), (37710223/18446744073709551616)), (1645770931/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-4845865/36893488147419103232), (49369/36893488147419103232)), (1586113961/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-5747/2305843009213693952), (4439/36893488147419103232)), (1559337281/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-10613/18446744073709551616), (-5629/36893488147419103232)), (1548546723/36893488147419103232), by norm_num⟩
  | 13 => ⟨(0, (-1213/36893488147419103232)), (1544593071/36893488147419103232), by norm_num⟩
  | 14 => ⟨((1/9223372036854775808), (-1/4611686018427387904)), (1543262871/36893488147419103232), by norm_num⟩
  | 15 => ⟨((1/36893488147419103232), (1/36893488147419103232)), (1542848671/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-1/36893488147419103232), (1/36893488147419103232)), (1542728613/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((111084205/562949953421312), (646130309/1125899906842624)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-665384455/1125899906842624), (1755063523/1125899906842624)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-937726827/1125899906842624), (-116049493/1125899906842624)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((-13561805/281474976710656), (-14955349/140737488355328)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-34644701/1125899906842624), (-13343583/562949953421312)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((2296511/562949953421312), (-1817651/140737488355328)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((1070603/562949953421312), (255743/1125899906842624)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((8629/281474976710656), (27009/281474976710656)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((11337/1125899906842624), (3751/562949953421312)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((-523/1125899906842624), (1151/562949953421312)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-37/281474976710656), (1/562949953421312)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((-3/1125899906842624), 0), (1/4294967296), by norm_num⟩
  | 12 => ⟨((-1/1125899906842624), 0), (1/4294967296), by norm_num⟩
  | 13 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 14 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 15 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | 16 => ⟨(0, 0), (1/4294967296), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨31,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨31,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(161751/1048576)) (K:=(1317/536870912)) (L:=(716449232835099/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile031
