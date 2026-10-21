/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand58.Tile005Gamma
import XiBand58.Tile005Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile005
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3878713/8796093022208), (-1239706811/35184372088832)), (1553/35184372088832), by norm_num⟩
  | 1 => ⟨((459613745/17592186044416), (-656842323/17592186044416)), (1789/17592186044416), by norm_num⟩
  | 2 => ⟨((951342981/35184372088832), (-92423475/8796093022208)), (4103/35184372088832), by norm_num⟩
  | 3 => ⟨((1667762625/140737488355328), (353513671/140737488355328)), (12501/140737488355328), by norm_num⟩
  | 4 => ⟨((374728665/140737488355328), (45998675/17592186044416)), (14273/281474976710656), by norm_num⟩
  | 5 => ⟨((121764205/562949953421312), (989036729/1125899906842624)), (26143/1125899906842624), by norm_num⟩
  | 6 => ⟨((-29394137/562949953421312), (775112189/4503599627370496)), (80347/9007199254740992), by norm_num⟩
  | 7 => ⟨((-197089037/9007199254740992), (374829877/18014398509481984)), (107237/36028797018963968), by norm_num⟩
  | 8 => ⟨((-38042605/9007199254740992), (333205469/288230376151711744)), (258463/288230376151711744), by norm_num⟩
  | 9 => ⟨((-631595553/1152921504606846976), (-256619623/2305843009213693952)), (152335/576460752303423488), by norm_num⟩
  | 10 => ⟨((-944317713/18446744073709551616), (-352216617/9223372036854775808)), (430501/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-482996195/147573952589676412928), (-425131707/73786976294838206464)), (952809/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-96000265/1180591620717411303424), (-1480370517/2361183241434822606848)), (100008989/2361183241434822606848), by norm_num⟩
  | 13 => ⟨((30889557/2361183241434822606848), (-1028953981/18889465931478580854784)), (763960555/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((96204993/37778931862957161709568), (-73371643/18889465931478580854784)), (757058657/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((10781671/37778931862957161709568), (-8432281/37778931862957161709568)), (1511649601/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((947029/37778931862957161709568), (-87293/9444732965739290427392)), (188904343/4722366482869645213696), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand58.Tile005Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-95839423/8388608), (889573351/33554432)), (6945/33554432), by norm_num⟩
  | 1 => ⟨((197071311/16777216), (-480708155/67108864)), (7201/33554432), by norm_num⟩
  | 2 => ⟨((-718832899/134217728), (171832065/67108864)), (14667/67108864), by norm_num⟩
  | 3 => ⟨((248539391/134217728), (-2191271/4194304)), (116447/536870912), by norm_num⟩
  | 4 => ⟨((-65826735/134217728), (4927049/134217728)), (455289/2147483648), by norm_num⟩
  | 5 => ⟨((6970435/67108864), (4291365/268435456)), (1778147/8589934592), by norm_num⟩
  | 6 => ⟨((-4798957/268435456), (-2051277/268435456)), (1747795/8589934592), by norm_num⟩
  | 7 => ⟨((667957/268435456), (1070113/536870912)), (27693871/137438953472), by norm_num⟩
  | 8 => ⟨((-4511/16777216), (-415655/1073741824)), (110267323/549755813888), by norm_num⟩
  | 9 => ⟨((163923/8589934592), (16293/268435456)), (1760952237/8796093022208), by norm_num⟩
  | 10 => ⟨((655/8589934592), (-68051/8589934592)), (1759760301/8796093022208), by norm_num⟩
  | 11 => ⟨((-5163/17179869184), (7445/8589934592)), (1759372717/8796093022208), by norm_num⟩
  | 12 => ⟨((4223/68719476736), (-5371/68719476736)), (1759259181/8796093022208), by norm_num⟩
  | 13 => ⟨((-9419/1099511627776), (2983/549755813888)), (1759228501/8796093022208), by norm_num⟩
  | 14 => ⟨((4197/4398046511104), (-233/1099511627776)), (1759220857/8796093022208), by norm_num⟩
  | 15 => ⟨((-389/4398046511104), (-53/4398046511104)), (879609543/4398046511104), by norm_num⟩
  | 16 => ⟨((15/2199023255552), (33/8796093022208)), (879609351/4398046511104), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand58.Tile005Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2697/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2697/160))
  have he : value ((15/16), (2697/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-72020177/134217728), (-40466337/4194304)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1284064724732801/2251799813685248), (291390006491909/2251799813685248)), (13783199/562949953421312), by norm_num⟩
  | 1 => ⟨((1401812807/4294967296), (-159055161/2147483648)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((-1604697015/17179869184), (364150393/17179869184)), (73/17179869184), by norm_num⟩
  | 3 => ⟨((612314877/34359738368), (-277902559/68719476736)), (29/34359738368), by norm_num⟩
  | 4 => ⟨((-1401870279/549755813888), (318123365/549755813888)), (69/549755813888), by norm_num⟩
  | 5 => ⟨((320952561/1099511627776), (-291332259/4398046511104)), (65/4398046511104), by norm_num⟩
  | 6 => ⟨((-489871985/17592186044416), (111165581/17592186044416)), (13/8796093022208), by norm_num⟩
  | 7 => ⟨((640881259/281474976710656), (-72716893/140737488355328)), (35/281474976710656), by norm_num⟩
  | 8 => ⟨((-1467271861/9007199254740992), (332964803/9007199254740992)), (83/9007199254740992), by norm_num⟩
  | 9 => ⟨((93312775/9007199254740992), (-42350529/18014398509481984)), (87/144115188075855872), by norm_num⟩
  | 10 => ⟨((-683634703/1152921504606846976), (38783933/288230376151711744)), (41/1152921504606846976), by norm_num⟩
  | 11 => ⟨((142286741/4611686018427387904), (-129155279/18446744073709551616)), (71/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-868692719/590295810358705651712), (12320659/36893488147419103232)), (111/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((611949857/9444732965739290427392), (-277736893/18889465931478580854784)), (81/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-800591189/302231454903657293676544), (363352825/604462909807314587353088)), (109/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((488779019/4835703278458516698824704), (-110917557/4835703278458516698824704)), (17/2417851639229258349412352), by norm_num⟩
  | 16 => ⟨((-559519951/154742504910672534362390528), (253941285/309485009821345068724781056)), (5/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583276795940879/10141204801825835211973625643008), (1900799607535/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781132241286329/633825300114114700748351602688), (4510414872129/633825300114114700748351602688)), (23161/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892399837885199/39614081257132168796771975168), (634242496395/4951760157141521099596496896)), (1629/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((473084981460191/618970019642690137449562112), (1347690527849/618970019642690137449562112)), (27701/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443501231786627/38685626227668133590597632), (5390425339699/154742504910672534362390528)), (13855/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776095224568405/4835703278458516698824704), (631645709993/1208925819614629174706176)), (6497/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261094753632707/604462909807314587353088), (552645200759/75557863725914323419136)), (11375/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945768461696549/37778931862957161709568), (7183715066121/75557863725914323419136)), (18493/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300345937564537/4722366482869645213696), (5387197212587/4722366482869645213696)), (6939/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812651748629521/295147905179352825856), (1851609438851/147573952589676412928)), (19095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228536068460635/9223372036854775808), (9256607572785/73786976294838206464)), (47777/73786976294838206464), by norm_num⟩
  | 7 => ⟨((457016316707241/2305843009213693952), (5205850392981/4611686018427387904)), (53803/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599304649916581/1152921504606846976), (10409217491789/1152921504606846976)), (53871/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199224445529065/144115188075855872), (4552632449285/72057594037927936)), (47213/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498582424189741/36028797018963968), (6826139899619/18014398509481984)), (17743/9007199254740992), by norm_num⟩
  | 3 => ⟨((374475778562119/2251799813685248), (17055481431393/9007199254740992)), (88983/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122565772093247/2251799813685248), (4260150964023/562949953421312)), (11173/281474976710656), by norm_num⟩
  | 1 => ⟨((560402719002097/562949953421312), (6380862381113/281474976710656)), (67541/562949953421312), by norm_num⟩
  | 0 => ⟨((1115338904650071/1125899906842624), (1590484508953/35184372088832)), (274193/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1115338904650071/1125899906842624), (1590484508953/35184372088832)), (1045963291648482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102576270168359/1125899906842624), (50418101695827/562949953421312)), (17751/35184372088832), by norm_num⟩
  | 2 => ⟨((535352425334391/562949953421312), (98747325901545/562949953421312)), (1214277/1125899906842624), by norm_num⟩
  | 3 => ⟨((491786495861939/562949953421312), (187812860078927/562949953421312)), (1367747/562949953421312), by norm_num⟩
  | 4 => ⟨((733920611754749/1125899906842624), (656284472711549/1125899906842624)), (3302319/562949953421312), by norm_num⟩
  | 5 => ⟨((191722469431335/2251799813685248), (855601281730861/1125899906842624)), (4077539/281474976710656), by norm_num⟩
  | 6 => ⟨((-1284064724732801/2251799813685248), (291390006491909/2251799813685248)), (13783199/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-72020177/134217728), (-40466337/4194304)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((75787399/17592186044416), (1417874403/70368744177664)), (559/17592186044416), by norm_num⟩
  | 1 => ⟨((-881881579/70368744177664), (924589475/70368744177664)), (6397/70368744177664), by norm_num⟩
  | 2 => ⟨((-534205225/70368744177664), (-187220077/140737488355328)), (9103/70368744177664), by norm_num⟩
  | 3 => ⟨((-461162633/562949953421312), (-1080532905/562949953421312)), (69051/562949953421312), by norm_num⟩
  | 4 => ⟨((64198907/281474976710656), (-744630725/2251799813685248)), (196645/2251799813685248), by norm_num⟩
  | 5 => ⟨((1039533975/18014398509481984), (456415/140737488355328)), (448729/9007199254740992), by norm_num⟩
  | 6 => ⟨((103329665/36028797018963968), (405863969/72057594037927936)), (1711875/72057594037927936), by norm_num⟩
  | 7 => ⟨((-674305645/2305843009213693952), (244813865/576460752303423488)), (22512915/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-516266731/18446744073709551616), (-87926921/18446744073709551616)), (65441193/18446744073709551616), by norm_num⟩
  | 9 => ⟨((114795793/1180591620717411303424), (-348678031/590295810358705651712)), (1387218425/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-22898377/590295810358705651712), (98340957/1180591620717411303424)), (1781909923/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-108084757/9444732965739290427392), (-24813445/9444732965739290427392)), (646455935/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((804367/18889465931478580854784), (-15193667/18889465931478580854784)), (1342081271/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((714079/18889465931478580854784), (86609/9444732965739290427392)), (8042515/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-9381/4722366482869645213696), (62337/37778931862957161709568)), (956703089/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-3315/37778931862957161709568), (-3869/18889465931478580854784)), (1881864889/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((553/37778931862957161709568), (-69/18889465931478580854784)), (937727919/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1282913623/2199023255552), (-127534967/1099511627776)), (1723/274877906944), by norm_num⟩
  | 1 => ⟨((-44960529/4398046511104), (-1216242733/4398046511104)), (8033/549755813888), by norm_num⟩
  | 2 => ⟨((-50627473/8796093022208), (-1366480169/35184372088832)), (688883/35184372088832), by norm_num⟩
  | 3 => ⟨((475851917/35184372088832), (-1000421915/35184372088832)), (93641/4398046511104), by norm_num⟩
  | 4 => ⟨((269472915/35184372088832), (69918765/35184372088832)), (357045/17592186044416), by norm_num⟩
  | 5 => ⟨((-6761673/70368744177664), (258212317/281474976710656)), (20314381/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1379769641/36028797018963968), (365746771/36028797018963968)), (8905149/562949953421312), by norm_num⟩
  | 7 => ⟨((-239446511/144115188075855872), (234529119/72057594037927936)), (2049248419/144115188075855872), by norm_num⟩
  | 8 => ⟨((-34774605/72057594037927936), (-3754931/72057594037927936)), (1914476717/144115188075855872), by norm_num⟩
  | 9 => ⟨((-855813/144115188075855872), (-1012475/72057594037927936)), (923551243/72057594037927936), by norm_num⟩
  | 10 => ⟨((-48765/36028797018963968), (-78683/144115188075855872)), (1817461563/144115188075855872), by norm_num⟩
  | 11 => ⟨((53/18014398509481984), (-16697/144115188075855872)), (1805761585/144115188075855872), by norm_num⟩
  | 12 => ⟨((3/144115188075855872), (-69/144115188075855872)), (450389643/36028797018963968), by norm_num⟩
  | 13 => ⟨((-17/72057594037927936), (-25/72057594037927936)), (900084989/72057594037927936), by norm_num⟩
  | 14 => ⟨((3/144115188075855872), (-1/36028797018963968)), (1799744467/144115188075855872), by norm_num⟩
  | 15 => ⟨(0, (1/144115188075855872)), (899811363/72057594037927936), by norm_num⟩
  | 16 => ⟨(0, (1/144115188075855872)), (899795015/72057594037927936), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-164212945957/281474976710656), (-32648948841/281474976710656)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11509898517/1125899906842624), (-311358135055/1125899906842624)), (1/33554432), by norm_num⟩
  | 2 => ⟨((-3240161227/562949953421312), (-43727365753/1125899906842624)), (1/16777216), by norm_num⟩
  | 3 => ⟨((15227261503/1125899906842624), (-4001687877/140737488355328)), (1/16777216), by norm_num⟩
  | 4 => ⟨((8623133361/1125899906842624), (1118700539/562949953421312)), (1/16777216), by norm_num⟩
  | 5 => ⟨((-27046821/281474976710656), (516424449/562949953421312)), (1/16777216), by norm_num⟩
  | 6 => ⟨((-43117659/1125899906842624), (5714813/562949953421312)), (1/16777216), by norm_num⟩
  | 7 => ⟨((-1870769/1125899906842624), (916125/281474976710656)), (1/16777216), by norm_num⟩
  | 8 => ⟨((-543305/1125899906842624), (-29333/562949953421312)), (1/16777216), by norm_num⟩
  | 9 => ⟨((-419/70368744177664), (-15795/1125899906842624)), (1/16777216), by norm_num⟩
  | 10 => ⟨((-383/281474976710656), (-309/562949953421312)), (1/16777216), by norm_num⟩
  | 11 => ⟨(0, (-33/281474976710656)), (1/16777216), by norm_num⟩
  | 12 => ⟨(0, (-1/562949953421312)), (1/16777216), by norm_num⟩
  | 13 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 14 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 15 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | 16 => ⟨(0, 0), (1/16777216), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (FiniteBandModel.xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨5,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨5,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(163873/524288)) (K:=(289357/536870912)) (L:=(351120150681265707/590295810358705651712)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand58.Tile005
