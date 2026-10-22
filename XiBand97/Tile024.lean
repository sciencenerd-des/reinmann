/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile024Gamma
import XiBand97.Tile024Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile024
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((246113795/1125899906842624), (-339536237/1125899906842624)), (905/2251799813685248), by norm_num⟩
  | 1 => ⟨((553324273/1125899906842624), (-231165465/1125899906842624)), (971/1125899906842624), by norm_num⟩
  | 2 => ⟨((840690923/2251799813685248), (123999297/2251799813685248)), (4407/4503599627370496), by norm_num⟩
  | 3 => ⟨((308695977/2251799813685248), (15675431/140737488355328)), (213/281474976710656), by norm_num⟩
  | 4 => ⟨((194758331/9007199254740992), (16185657/281474976710656)), (1019/2251799813685248), by norm_num⟩
  | 5 => ⟨((-3063447/1125899906842624), (1204564947/72057594037927936)), (16647/72057594037927936), by norm_num⟩
  | 6 => ⟨((-693347319/288230376151711744), (868512139/288230376151711744)), (32859/288230376151711744), by norm_num⟩
  | 7 => ⟨((-793754169/1152921504606846976), (330248719/1152921504606846976)), (18639/288230376151711744), by norm_num⟩
  | 8 => ⟨((-1148405791/9223372036854775808), (-112955247/9223372036854775808)), (217793/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-571603375/36893488147419103232), (-747220143/73786976294838206464)), (3091037/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-721791907/590295810358705651712), (-1250804895/590295810358705651712)), (11938157/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-23465665/1180591620717411303424), (-688028533/2361183241434822606848)), (189353123/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((109483489/9444732965739290427392), (-559182331/18889465931478580854784)), (755945303/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((21554939/9444732965739290427392), (-41860393/18889465931478580854784)), (377823389/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((10426841/37778931862957161709568), (-244229/2361183241434822606848)), (755590479/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((480397/18889465931478580854784), (18647/18889465931478580854784)), (188895143/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((71009/37778931862957161709568), (31851/37778931862957161709568)), (94447367/2361183241434822606848), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile024Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-3862369/1048576), (451514035/16777216)), (7167/33554432), by norm_num⟩
  | 1 => ⟨((369396791/67108864), (-761835319/67108864)), (3887/16777216), by norm_num⟩
  | 2 => ⟨((-30557007/8388608), (620421059/67108864)), (32489/134217728), by norm_num⟩
  | 3 => ⟨((69273227/33554432), (-578188479/134217728)), (1003/4194304), by norm_num⟩
  | 4 => ⟨((-57976737/67108864), (188041851/134217728)), (122463/536870912), by norm_num⟩
  | 5 => ⟨((75563057/268435456), (-23299473/67108864)), (464985/2147483648), by norm_num⟩
  | 6 => ⟨((-19996631/268435456), (36670657/536870912)), (1788627/8589934592), by norm_num⟩
  | 7 => ⟨((2215719/134217728), (-5784591/536870912)), (1748443/8589934592), by norm_num⟩
  | 8 => ⟨((-1680663/536870912), (2839335/2147483648)), (27673199/137438953472), by norm_num⟩
  | 9 => ⟨((4428745/8589934592), (-233123/2147483648)), (110204603/549755813888), by norm_num⟩
  | 10 => ⟨((-639539/8589934592), (997/4294967296)), (1760471981/8796093022208), by norm_num⟩
  | 11 => ⟨((650789/68719476736), (70213/34359738368)), (1759573421/8796093022208), by norm_num⟩
  | 12 => ⟨((-291325/274877906944), (-34149/68719476736)), (1759310989/8796093022208), by norm_num⟩
  | 13 => ⟨((113599/1099511627776), (45353/549755813888)), (1759240909/8796093022208), by norm_num⟩
  | 14 => ⟨((-9379/1099511627776), (-49053/4398046511104)), (1759223629/8796093022208), by norm_num⟩
  | 15 => ⟨((1209/2199023255552), (5707/4398046511104)), (1759219665/8796093022208), by norm_num⟩
  | 16 => ⟨((-83/4398046511104), (-585/4398046511104)), (1759218815/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile024Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5865/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5865/256))
  have he : value ((69/80), (5865/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-879996539/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((587100881050853/1125899906842624), (-357213553654649/1125899906842624)), (32676203/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1281875467/4294967296), (389969855/2147483648)), (19/2147483648), by norm_num⟩
  | 2 => ⟨((733700579/8589934592), (-111602537/2147483648)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((-559925987/34359738368), (681358717/68719476736)), (39/68719476736), by norm_num⟩
  | 4 => ⟨((1281928023/549755813888), (-779971687/549755813888)), (47/549755813888), by norm_num⟩
  | 5 => ⟨((-36686533/137438953472), (44642845/274877906944)), (23/2199023255552), by norm_num⟩
  | 6 => ⟨((895918309/35184372088832), (-545109321/35184372088832)), (37/35184372088832), by norm_num⟩
  | 7 => ⟨((-586048265/281474976710656), (713146207/562949953421312)), (51/562949953421312), by norm_num⟩
  | 8 => ⟨((167716741/1125899906842624), (-25511243/281474976710656)), (31/4503599627370496), by norm_num⟩
  | 9 => ⟨((-170658103/18014398509481984), (415338415/72057594037927936)), (33/72057594037927936), by norm_num⟩
  | 10 => ⟨((1250287557/2305843009213693952), (-380360237/1152921504606846976)), (63/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-1040902933/36893488147419103232), (633323245/36893488147419103232)), (55/36893488147419103232), by norm_num⟩
  | 12 => ⟨((49648029/36893488147419103232), (-483322697/590295810358705651712)), (11/147573952589676412928), by norm_num⟩
  | 13 => ⟨((-279796099/4722366482869645213696), (680952537/18889465931478580854784)), (65/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((732093615/302231454903657293676544), (-111358103/75557863725914323419136)), (11/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((-893919403/9671406556917033397649408), (271946557/4835703278458516698824704)), (7/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((3997251/1208925819614629174706176), (-311305351/154742504910672534362390528)), (67/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-178001772407/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781209041945669/633825300114114700748351602688), (-844821909535/633825300114114700748351602688)), (721/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((946243436043225/19807040628566084398385987584), (-950382034961/39614081257132168796771975168)), (6489/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946216584655105/1237940039285380274899124224), (-1009729997045/2475880078570760549798248448)), (27581/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774099036388365/154742504910672534362390528), (-504836359891/77371252455336267181195264)), (13791/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552279596279885/9671406556917033397649408), (-473253660215/4835703278458516698824704)), (6465/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261173676938185/604462909807314587353088), (-207033263519/151115727451828646838272)), (11315/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891666897561637/75557863725914323419136), (-21025033175/1180591620717411303424)), (4597/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1300444926144137/4722366482869645213696), (-1009101770453/4722366482869645213696)), (13793/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812721028143459/295147905179352825856), (-1387352735925/590295810358705651712)), (18967/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828465419852371/73786976294838206464), (-1733947643617/73786976294838206464)), (47425/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828269296943203/9223372036854775808), (-1950356628921/9223372036854775808)), (53363/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399878747055581/288230376151711744), (-1949938593361/1152921504606846976)), (417/9007199254740992), by norm_num⟩
  | 5 => ⟨((1199415584177557/144115188075855872), (-1705726050865/144115188075855872)), (23359/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498883307194745/36028797018963968), (-2557648818865/36028797018963968)), (70105/36028797018963968), by norm_num⟩
  | 3 => ⟨((374576000310925/2251799813685248), (-199713498523/562949953421312)), (87681/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123003787685307/2251799813685248), (-3192949212263/2251799813685248)), (21939/562949953421312), by norm_num⟩
  | 1 => ⟨((1121555120400165/1125899906842624), (-2391629866107/562949953421312)), (131821/1125899906842624), by norm_num⟩
  | 0 => ⟨((558603963016341/562949953421312), (-1192735008605/140737488355328)), (132195/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558603963016341/562949953421312), (-1192735008605/140737488355328)), (504283907176780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1108502181170755/1125899906842624), (-9468216470553/562949953421312)), (132295/281474976710656), by norm_num⟩
  | 2 => ⟨((1091054799544889/1125899906842624), (-37287643584011/1125899906842624)), (1059807/1125899906842624), by norm_num⟩
  | 3 => ⟨((1056053206878973/1125899906842624), (-36133640520623/562949953421312)), (2124213/1125899906842624), by norm_num⟩
  | 4 => ⟨((1971801949896467/2251799813685248), (-271136336124413/2251799813685248)), (8515121/2251799813685248), by norm_num⟩
  | 5 => ⟨((52936655293275/70368744177664), (-474844302773915/2251799813685248)), (2120403/281474976710656), by norm_num⟩
  | 6 => ⟨((587100881050853/1125899906842624), (-357213553654649/1125899906842624)), (32676203/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-879996539/67108864)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((41223345/2251799813685248), (-1020542609/4503599627370496)), (1553/4503599627370496), by norm_num⟩
  | 1 => ⟨((813568025/4503599627370496), (-600253795/4503599627370496)), (4193/4503599627370496), by norm_num⟩
  | 2 => ⟨((952553659/9007199254740992), (213195861/9007199254740992)), (367/281474976710656), by norm_num⟩
  | 3 => ⟨((145284203/9007199254740992), (269779057/9007199254740992)), (11197/9007199254740992), by norm_num⟩
  | 4 => ⟨((-398215753/144115188075855872), (1049610071/144115188075855872)), (130619/144115188075855872), by norm_num⟩
  | 5 => ⟨((-374065463/288230376151711744), (550869549/1152921504606846976)), (157375/288230376151711744), by norm_num⟩
  | 6 => ⟨((-399560097/2305843009213693952), (-27257915/288230376151711744)), (1352323/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-23837727/4611686018427387904), (-833240279/36893488147419103232)), (11514277/73786976294838206464), by norm_num⟩
  | 8 => ⟨((765860309/590295810358705651712), (-1096049295/590295810358705651712)), (27886323/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1733591723/9444732965739290427392), (-128250781/4722366482869645213696)), (334267903/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((194761565/18889465931478580854784), (141299275/18889465931478580854784)), (592825417/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((3385999/18889465931478580854784), (13439391/18889465931478580854784)), (1139856045/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-203253/18889465931478580854784), (331531/9444732965739290427392)), (563654357/9444732965739290427392), by norm_num⟩
  | 13 => ⟨((-21209/18889465931478580854784), (14067/9444732965739290427392)), (562080811/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-109/1180591620717411303424), (1113/18889465931478580854784)), (561716445/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-29/4722366482869645213696), (5/18889465931478580854784)), (280819001/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((-5/18889465931478580854784), (-3/18889465931478580854784)), (1123244417/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1697593475/281474976710656), (93405351/70368744177664)), (17695/281474976710656), by norm_num⟩
  | 1 => ⟨((126617957/281474976710656), (1097033981/281474976710656)), (44501/281474976710656), by norm_num⟩
  | 2 => ⟨((543866023/1125899906842624), (272808019/281474976710656)), (30919/140737488355328), by norm_num⟩
  | 3 => ⟨((-426587489/1125899906842624), (485493921/562949953421312)), (279895/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1173774397/4503599627370496), (-269774751/4503599627370496)), (556853/2251799813685248), by norm_num⟩
  | 5 => ⟨((42319569/36028797018963968), (-152345349/4503599627370496)), (8217809/36028797018963968), by norm_num⟩
  | 6 => ⟨((397332999/576460752303423488), (-153905393/144115188075855872)), (117471237/576460752303423488), by norm_num⟩
  | 7 => ⟨((50900811/288230376151711744), (-236686935/576460752303423488)), (26367709/144115188075855872), by norm_num⟩
  | 8 => ⟨((564105895/9223372036854775808), (12340195/1152921504606846976)), (1556498147/9223372036854775808), by norm_num⟩
  | 9 => ⟨((2215471/9223372036854775808), (7783143/2305843009213693952)), (185112249/1152921504606846976), by norm_num⟩
  | 10 => ⟨((281323/4611686018427387904), (183261/2305843009213693952)), (721436195/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1185/288230376151711744), (92299/4611686018427387904)), (1425867973/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-2213/2305843009213693952), (101/1152921504606846976)), (177376755/1152921504606846976), by norm_num⟩
  | 13 => ⟨((-161/9223372036854775808), (155/9223372036854775808)), (1416497399/9223372036854775808), by norm_num⟩
  | 14 => ⟨((-27/9223372036854775808), (1/4611686018427387904)), (1415648589/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-1/4611686018427387904), 0), (707691903/4611686018427387904), by norm_num⟩
  | 16 => ⟨(0, 0), (1415306999/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((6790373909/1125899906842624), (1494485837/1125899906842624)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((506471621/1125899906842624), (4388135851/1125899906842624)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((271933083/562949953421312), (545616067/562949953421312)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((-213293815/562949953421312), (970987853/1125899906842624)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((-36680441/140737488355328), (-65863/1099511627776)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((330613/281474976710656), (-38086313/1125899906842624)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((194013/281474976710656), (-1202399/1125899906842624)), (1/1073741824), by norm_num⟩
  | 7 => ⟨((198829/1125899906842624), (-7223/17592186044416)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((68861/1125899906842624), (12049/1125899906842624)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((135/562949953421312), (3801/1125899906842624)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((69/1125899906842624), (89/1125899906842624)), (1/1073741824), by norm_num⟩
  | 11 => ⟨((-5/1125899906842624), (23/1125899906842624)), (1/1073741824), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨24,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨24,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(1389/268435456)) (L:=(3645316279143061/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile024
