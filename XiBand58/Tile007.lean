/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile007Gamma
import XiBand58.Tile007Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile007
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((987709401/70368744177664), (-893341/274877906944)), (1339/70368744177664), by norm_num⟩
  | 1 => ⟨((628653749/35184372088832), (470615489/70368744177664)), (1413/35184372088832), by norm_num⟩
  | 2 => ⟨((16243285/2199023255552), (705960933/70368744177664)), (3073/70368744177664), by norm_num⟩
  | 3 => ⟨((12361183/35184372088832), (750960665/140737488355328)), (4549/140737488355328), by norm_num⟩
  | 4 => ⟨((-451721631/562949953421312), (841715073/562949953421312)), (5129/281474976710656), by norm_num⟩
  | 5 => ⟨((-823853173/2251799813685248), (485329005/2251799813685248)), (9369/1125899906842624), by norm_num⟩
  | 6 => ⟨((-393215757/4503599627370496), (180649/2251799813685248)), (57859/18014398509481984), by norm_num⟩
  | 7 => ⟨((-952840539/72057594037927936), (-537852405/72057594037927936)), (19639/18014398509481984), by norm_num⟩
  | 8 => ⟨((-700239417/576460752303423488), (-1114407949/576460752303423488)), (199963/576460752303423488), by norm_num⟩
  | 9 => ⟨((-59918425/2305843009213693952), (-86758855/288230376151711744)), (555277/4611686018427387904), by norm_num⟩
  | 10 => ⟨((235891849/18446744073709551616), (-615287053/18446744073709551616)), (2181335/36893488147419103232), by norm_num⟩
  | 11 => ⟨((805621763/295147905179352825856), (-395317201/147573952589676412928)), (13036935/295147905179352825856), by norm_num⟩
  | 12 => ⟨((412779417/1180591620717411303424), (-320835203/2361183241434822606848)), (96432605/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((1286110131/37778931862957161709568), (4038667/9444732965739290427392)), (1517117431/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((395771/147573952589676412928), (39945701/37778931862957161709568)), (1512204409/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((6507705/37778931862957161709568), (5711331/37778931862957161709568)), (1511330419/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((324061/37778931862957161709568), (281545/18889465931478580854784)), (1511184341/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile007Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((112233287/33554432), (142762363/4194304)), (6949/33554432), by norm_num⟩
  | 1 => ⟨((-183565613/134217728), (-485795239/33554432)), (28895/134217728), by norm_num⟩
  | 2 => ⟨((79031459/134217728), (236350323/33554432)), (7361/33554432), by norm_num⟩
  | 3 => ⟨((10565409/134217728), (-323353089/134217728)), (116823/536870912), by norm_num⟩
  | 4 => ⟨((-32195427/268435456), (85392201/134217728)), (456137/2147483648), by norm_num⟩
  | 5 => ⟨((14187227/268435456), (-36179705/268435456)), (1779939/8589934592), by norm_num⟩
  | 6 => ⟨((-8325291/536870912), (12446769/536870912)), (1748643/8589934592), by norm_num⟩
  | 7 => ⟨((1876129/536870912), (-1720173/536870912)), (27699375/137438953472), by norm_num⟩
  | 8 => ⟨((-2751281/4294967296), (361351/1073741824)), (110274235/549755813888), by norm_num⟩
  | 9 => ⟨((105559/1073741824), (-179697/8589934592)), (1760998317/8796093022208), by norm_num⟩
  | 10 => ⟨((-27497/2147483648), (-34159/34359738368)), (1759771565/8796093022208), by norm_num⟩
  | 11 => ⟨((97341/68719476736), (38391/68719476736)), (1759376301/8796093022208), by norm_num⟩
  | 12 => ⟨((-35969/274877906944), (-14639/137438953472)), (1759260301/8796093022208), by norm_num⟩
  | 13 => ⟨((5231/549755813888), (8125/549755813888)), (1759228813/8796093022208), by norm_num⟩
  | 14 => ⟨((-1881/4398046511104), (-7377/4398046511104)), (1759220921/8796093022208), by norm_num⟩
  | 15 => ⟨((-111/8796093022208), (355/2199023255552)), (879609549/4398046511104), by norm_num⟩
  | 16 => ⟨((51/8796093022208), (-29/2199023255552)), (1759218705/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile007Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2893/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2893/160))
  have he : value ((15/16), (2893/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-1389029149/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-99147905910803/281474976710656), (1050995094855665/2251799813685248)), (58137367/2251799813685248), by norm_num⟩
  | 1 => ⟨((216479437/1073741824), (-1147370811/4294967296)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((-495620963/8589934592), (656714829/8589934592)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((756469505/68719476736), (-501174061/34359738368)), (63/68719476736), by norm_num⟩
  | 4 => ⟨((-432976625/274877906944), (286854463/137438953472)), (75/549755813888), by norm_num⟩
  | 5 => ⟨((198256513/1099511627776), (-525393403/2199023255552)), (71/4398046511104), by norm_num⟩
  | 6 => ⟨((-605200415/35184372088832), (400955687/17592186044416)), (7/4398046511104), by norm_num⟩
  | 7 => ⟨((791761145/562949953421312), (-1049110761/562949953421312)), (19/140737488355328), by norm_num⟩
  | 8 => ⟨((-906352645/9007199254740992), (600474221/4503599627370496)), (45/4503599627370496), by norm_num⟩
  | 9 => ⟨((922247965/144115188075855872), (-1222010287/144115188075855872)), (95/144115188075855872), by norm_num⟩
  | 10 => ⟨((-422289923/1152921504606846976), (1119097357/2305843009213693952)), (45/1152921504606846976), by norm_num⟩
  | 11 => ⟨((703138757/36893488147419103232), (-931683047/36893488147419103232)), (77/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-536602633/590295810358705651712), (88877119/73786976294838206464)), (61/590295810358705651712), by norm_num⟩
  | 13 => ⟨((756018549/18889465931478580854784), (-500875295/9444732965739290427392)), (11/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-123633861/75557863725914323419136), (655276479/302231454903657293676544)), (15/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((75481267/1208925819614629174706176), (-800122207/9671406556917033397649408)), (75/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-691245297/309485009821345068724781056), (915923803/309485009821345068724781056)), (11/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (2888276889701/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781136821937641/633825300114114700748351602688), (3426801801329/633825300114114700748351602688)), (23135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892405270207631/39614081257132168796771975168), (3854951675849/39614081257132168796771975168)), (1627/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892346036702301/2475880078570760549798248448), (2047830063209/1237940039285380274899124224)), (27665/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443502854849049/38685626227668133590597632), (4095405731365/154742504910672534362390528)), (3459/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((97012308798605/604462909807314587353088), (1919586237727/4835703278458516698824704)), (12975/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630550419449341/302231454903657293676544), (52484459415/9444732965739290427392)), (11357/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945773785656407/37778931862957161709568), (2728938160259/37778931862957161709568)), (9231/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((5079510108529/18446744073709551616), (2046481484141/2361183241434822606848)), (27705/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406329117614333/147573952589676412928), (1406775419643/147573952589676412928)), (19057/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914153191183599/36893488147419103232), (7032792688315/73786976294838206464)), (47673/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828087554975945/9223372036854775808), (494399962647/576460752303423488)), (53673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599329716912179/1152921504606846976), (7908531976229/1152921504606846976)), (53725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199249503544535/144115188075855872), (6917861930657/144115188075855872)), (47067/144115188075855872), by norm_num⟩
  | 4 => ⟨((374656563865567/9007199254740992), (162071547979/562949953421312)), (17679/9007199254740992), by norm_num⟩
  | 3 => ⟨((1497968820525179/9007199254740992), (6479167262557/4503599627370496)), (88597/9007199254740992), by norm_num⟩
  | 2 => ⟨((280661958389169/562949953421312), (12947220366749/2251799813685248)), (44451/1125899906842624), by norm_num⟩
  | 1 => ⟨((140121168210087/140737488355328), (19392939715799/1125899906842624)), (67057/562949953421312), by norm_num⟩
  | 0 => ⟨((1115829543726429/1125899906842624), (38673685237713/1125899906842624)), (271283/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1115829543726429/1125899906842624), (38673685237713/1125899906842624)), (1034862522605514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((34516276412679/35184372088832), (19163888499659/281474976710656)), (556351/1125899906842624), by norm_num⟩
  | 2 => ⟨((1078328736112811/1125899906842624), (75199986053575/562949953421312)), (1167331/1125899906842624), by norm_num⟩
  | 3 => ⟨((1012676797100217/1125899906842624), (288090639048919/1125899906842624)), (159243/70368744177664), by norm_num⟩
  | 4 => ⟨((837124218013887/1125899906842624), (259119575242485/562949953421312)), (1471805/281474976710656), by norm_num⟩
  | 5 => ⟨((191937638800423/562949953421312), (770637853253773/1125899906842624)), (14174125/1125899906842624), by norm_num⟩
  | 6 => ⟨((-99147905910803/281474976710656), (1050995094855665/2251799813685248)), (58137367/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-1389029149/134217728)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-482349197/140737488355328), (541555695/70368744177664)), (2257/140737488355328), by norm_num⟩
  | 1 => ⟨((-1048984567/140737488355328), (222182223/140737488355328)), (1503/35184372088832), by norm_num⟩
  | 2 => ⟨((-691530991/281474976710656), (-633441201/281474976710656)), (4085/70368744177664), by norm_num⟩
  | 3 => ⟨((135087407/1125899906842624), (-1043250747/1125899906842624)), (3755/70368744177664), by norm_num⟩
  | 4 => ⟨((751209911/4503599627370496), (-387159825/4503599627370496)), (83955/2251799813685248), by norm_num⟩
  | 5 => ⟨((901327063/36028797018963968), (15346003/1125899906842624)), (758833/36028797018963968), by norm_num⟩
  | 6 => ⟨((170601411/576460752303423488), (1923771515/576460752303423488)), (1442629/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1104705169/4611686018427387904), (435782215/2305843009213693952)), (19033417/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-723906837/36893488147419103232), (-122217533/18446744073709551616)), (112370331/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-18510663/73786976294838206464), (-1014833721/1180591620717411303424)), (78152953/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-27875989/4722366482869645213696), (-37915093/4722366482869645213696)), (1846086435/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-29907675/9444732965739290427392), (-21063909/9444732965739290427392)), (894145969/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((830477/18889465931478580854784), (-3484595/9444732965739290427392)), (316662603/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((372151/18889465931478580854784), (-577/147573952589676412928)), (283882495/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((-421/18889465931478580854784), (12299/18889465931478580854784)), (1105047267/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-511/18889465931478580854784), (-201/4722366482869645213696)), (1098448831/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((39/9444732965739290427392), (-39/18889465931478580854784)), (137138913/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-300620675/1099511627776), (-49980513/549755813888)), (12769/4398046511104), by norm_num⟩
  | 1 => ⟨((164677369/4398046511104), (-920603463/4398046511104)), (6725/1099511627776), by norm_num⟩
  | 2 => ⟨((1590478237/35184372088832), (-88114117/17592186044416)), (36631/4398046511104), by norm_num⟩
  | 3 => ⟨((192840939/35184372088832), (-108252401/35184372088832)), (627169/70368744177664), by norm_num⟩
  | 4 => ⟨((856003493/281474976710656), (178337229/140737488355328)), (1187707/140737488355328), by norm_num⟩
  | 5 => ⟨((-70380313/562949953421312), (162760259/281474976710656)), (8449715/1125899906842624), by norm_num⟩
  | 6 => ⟨((-875373141/18014398509481984), (-44720739/36028797018963968)), (238001955/36028797018963968), by norm_num⟩
  | 7 => ⟨((-272721993/288230376151711744), (-72231811/144115188075855872)), (859209761/144115188075855872), by norm_num⟩
  | 8 => ⟨((-77906521/288230376151711744), (-23848157/288230376151711744)), (1608778285/288230376151711744), by norm_num⟩
  | 9 => ⟨((5523/72057594037927936), (-6218805/288230376151711744)), (388222773/72057594037927936), by norm_num⟩
  | 10 => ⟨((13409/288230376151711744), (-56709/144115188075855872)), (190956813/36028797018963968), by norm_num⟩
  | 11 => ⟨((2779/144115188075855872), (-23735/288230376151711744)), (758692791/144115188075855872), by norm_num⟩
  | 12 => ⟨((1055/288230376151711744), (-107/144115188075855872)), (1513574199/288230376151711744), by norm_num⟩
  | 13 => ⟨((5/36028797018963968), (-23/144115188075855872)), (756136191/144115188075855872), by norm_num⟩
  | 14 => ⟨((5/144115188075855872), (1/72057594037927936)), (1511860203/288230376151711744), by norm_num⟩
  | 15 => ⟨(0, (1/144115188075855872)), (377934635/72057594037927936), by norm_num⟩
  | 16 => ⟨((-1/288230376151711744), 0), (1511704909/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-153917785251/562949953421312), (-102360099077/1125899906842624)), (1/268435456), by norm_num⟩
  | 1 => ⟨((21078707389/562949953421312), (-235674487089/1125899906842624)), (1/67108864), by norm_num⟩
  | 2 => ⟨((397619545/8796093022208), (-5639301157/1125899906842624)), (1/33554432), by norm_num⟩
  | 3 => ⟨((1542727883/281474976710656), (-866019581/281474976710656)), (1/33554432), by norm_num⟩
  | 4 => ⟨((3424013553/1125899906842624), (356674759/281474976710656)), (1/33554432), by norm_num⟩
  | 5 => ⟨((-70380303/562949953421312), (325520195/562949953421312)), (1/33554432), by norm_num⟩
  | 6 => ⟨((-54710639/1125899906842624), (-1397329/1125899906842624)), (1/33554432), by norm_num⟩
  | 7 => ⟨((-1065319/1125899906842624), (-564333/1125899906842624)), (1/33554432), by norm_num⟩
  | 8 => ⟨((-304307/1125899906842624), (-93131/1125899906842624)), (1/33554432), by norm_num⟩
  | 9 => ⟨((21/281474976710656), (-3037/140737488355328)), (1/33554432), by norm_num⟩
  | 10 => ⟨((27/562949953421312), (-221/562949953421312)), (1/33554432), by norm_num⟩
  | 11 => ⟨((11/562949953421312), (-93/1125899906842624)), (1/33554432), by norm_num⟩
  | 12 => ⟨((1/281474976710656), (-1/1125899906842624)), (1/33554432), by norm_num⟩
  | 13 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | 14 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | 15 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | 16 => ⟨(0, 0), (1/33554432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨7,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨7,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(163873/524288)) (K:=(528257/1073741824)) (L:=(340166084039942341/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile007
