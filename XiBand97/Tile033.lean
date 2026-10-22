/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import XiBand97.Tile033Gamma
import XiBand97.Tile033Zeta
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile033
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_gammaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-168087575/9007199254740992), (38019639/562949953421312)), (3235/18014398509481984), by norm_num⟩
  | 1 => ⟨((-668246285/9007199254740992), (644963183/9007199254740992)), (765/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1317610799/18014398509481984), (160645303/9007199254740992)), (6619/18014398509481984), by norm_num⟩
  | 3 => ⟨((-628858237/18014398509481984), (-366827763/36028797018963968)), (159/562949953421312), by norm_num⟩
  | 4 => ⟨((-655706223/72057594037927936), (-338041565/36028797018963968)), (6373/36028797018963968), by norm_num⟩
  | 5 => ⟨((-69038145/72057594037927936), (-259710517/72057594037927936)), (29591/288230376151711744), by norm_num⟩
  | 6 => ⟨((122164261/576460752303423488), (-984647951/1152921504606846976)), (73971/1152921504606846976), by norm_num⟩
  | 7 => ⟨((274129007/2305843009213693952), (-602388073/4611686018427387904)), (110801/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1068840499/36893488147419103232), (-385067345/36893488147419103232)), (781501/18446744073709551616), by norm_num⟩
  | 9 => ⟨((693298069/147573952589676412928), (91763001/147573952589676412928)), (2997345/73786976294838206464), by norm_num⟩
  | 10 => ⟨((1271519755/2361183241434822606848), (868152215/2361183241434822606848)), (47398295/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((754035835/18889465931478580854784), (666465157/9444732965739290427392)), (756186699/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((11979027/18889465931478580854784), (173193005/18889465931478580854784)), (755700663/18889465931478580854784), by norm_num⟩
  | 13 => ⟨((-6455495/18889465931478580854784), (33783529/37778931862957161709568)), (1511202753/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-2468459/37778931862957161709568), (2460169/37778931862957161709568)), (1511165191/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-290957/37778931862957161709568), (114187/37778931862957161709568)), (1511158569/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-26225/37778931862957161709568), (-153/9444732965739290427392)), (1511157475/37778931862957161709568), by norm_num⟩
  | _ => zero
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiBand97.Tile033Gamma.gammaJet_sound

private def J_zetaActual : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-192814549/33554432), (75484881/8388608)), (14531/67108864), by norm_num⟩
  | 1 => ⟨((-51505009/67108864), (739761849/33554432)), (16009/67108864), by norm_num⟩
  | 2 => ⟨((82263745/16777216), (-971495989/67108864)), (4189/16777216), by norm_num⟩
  | 3 => ⟨((-224235887/67108864), (837553145/134217728)), (16455/67108864), by norm_num⟩
  | 4 => ⟨((193437571/134217728), (-535989091/268435456)), (124575/536870912), by norm_num⟩
  | 5 => ⟨((-63141229/134217728), (135215283/268435456)), (469489/2147483648), by norm_num⟩
  | 6 => ⟨((67162725/536870912), (-27700355/268435456)), (1796979/8589934592), by norm_num⟩
  | 7 => ⟨((-30232217/1073741824), (2321567/134217728)), (1751795/8589934592), by norm_num⟩
  | 8 => ⟨((11777907/2147483648), (-623973/268435456)), (27692655/137438953472), by norm_num⟩
  | 9 => ⟨((-2013829/2147483648), (981767/4294967296)), (110230075/549755813888), by norm_num⟩
  | 10 => ⟨((610035/4294967296), (-40161/4294967296)), (1760595373/8796093022208), by norm_num⟩
  | 11 => ⟨((-1316639/68719476736), (-39229/17179869184)), (1759607341/8796093022208), by norm_num⟩
  | 12 => ⟨((316921/137438953472), (401/536870912)), (1759319917/8796093022208), by norm_num⟩
  | 13 => ⟨((-271479/1099511627776), (-154503/1099511627776)), (1759243085/8796093022208), by norm_num⟩
  | 14 => ⟨((102379/4398046511104), (22919/1099511627776)), (1759224123/8796093022208), by norm_num⟩
  | 15 => ⟨((-16559/8796093022208), (-11605/4398046511104)), (879609885/4398046511104), by norm_num⟩
  | 16 => ⟨((535/4398046511104), (2589/8796093022208)), (1759218837/8796093022208), by norm_num⟩
  | _ => zero
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiBand97.Tile033Zeta.zetaJet_sound

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32189/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32189/1280))
  have he : value ((69/80), (32189/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-66258563/134217728), (-965940617/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-348657270221747/2251799813685248), (-1329508923513719/2251799813685248)), (28753347/1125899906842624), by norm_num⟩
  | 1 => ⟨((380628965/4294967296), (181428027/536870912)), (65/4294967296), by norm_num⟩
  | 2 => ⟨((-54464669/2147483648), (-830744339/8589934592)), (77/17179869184), by norm_num⟩
  | 3 => ⟨((332519117/68719476736), (1267970497/68719476736)), (61/68719476736), by norm_num⟩
  | 4 => ⟨((-380644571/549755813888), (-1451483723/549755813888)), (9/68719476736), by norm_num⟩
  | 5 => ⟨((348588173/4398046511104), (664622719/2199023255552)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((-33253275/4398046511104), (-507208993/17592186044416)), (27/17592186044416), by norm_num⟩
  | 7 => ⟨((174016081/281474976710656), (1327125241/562949953421312)), (73/562949953421312), by norm_num⟩
  | 8 => ⟨((-398402817/9007199254740992), (-759599963/4503599627370496)), (43/4503599627370496), by norm_num⟩
  | 9 => ⟨((405389877/144115188075855872), (1545843163/144115188075855872)), (45/72057594037927936), by norm_num⟩
  | 10 => ⟨((-185624763/1152921504606846976), (-707829147/1152921504606846976)), (85/2305843009213693952), by norm_num⟩
  | 11 => ⟨((309076675/36893488147419103232), (1178579169/36893488147419103232)), (73/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-235872871/590295810358705651712), (-224859133/147573952589676412928)), (57/590295810358705651712), by norm_num⟩
  | 13 => ⟨((83080223/4722366482869645213696), (316803655/4722366482869645213696)), (41/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-108690759/151115727451828646838272), (-1657849655/604462909807314587353088)), (55/302231454903657293676544), by norm_num⟩
  | 15 => ⟨((132716331/4835703278458516698824704), (253038673/2417851639229258349412352)), (69/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-303848701/309485009821345068724781056), (-1158643725/309485009821345068724781056)), (81/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583332713632487/10141204801825835211973625643008), (-2380218271107/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781205174651123/633825300114114700748351602688), (-706053554171/158456325028528675187087900672)), (1445/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1892482285267381/39614081257132168796771975168), (-1588545818975/19807040628566084398385987584)), (26015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473107002374089/618970019642690137449562112), (-421936101045/309485009821345068724781056)), (27645/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774093554502241/154742504910672534362390528), (-3375296310337/154742504910672534362390528)), (27651/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388068528715489/2417851639229258349412352), (-1582067853593/4835703278458516698824704)), (25929/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630584269303205/302231454903657293676544), (-2768414098627/604462909807314587353088)), (11347/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891657906476261/75557863725914323419136), (-4498289070155/75557863725914323419136)), (36889/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650218810910237/2361183241434822606848), (-3373380812131/4722366482869645213696)), (27677/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625431101434885/590295810358705651712), (-2318926193891/295147905179352825856)), (4759/73786976294838206464), by norm_num⟩
  | 8 => ⟨((457112589896465/18446744073709551616), (-724561964247/9223372036854775808)), (47615/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828250475593769/9223372036854775808), (-3259964899667/4611686018427387904)), (1675/288230376151711744), by norm_num⟩
  | 6 => ⟨((1599493819683679/1152921504606846976), (-3259259455151/576460752303423488)), (53643/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199394422491053/144115188075855872), (-5702115366981/144115188075855872)), (46985/144115188075855872), by norm_num⟩
  | 4 => ⟨((749423144834195/18014398509481984), (-4274996060795/18014398509481984)), (70573/36028797018963968), by norm_num⟩
  | 3 => ⟨((749124252911731/4503599627370496), (-10681915504303/9007199254740992)), (88383/9007199254740992), by norm_num⟩
  | 2 => ⟨((561467236237243/1125899906842624), (-5336768756679/1125899906842624)), (88633/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121416652344391/1125899906842624), (-15989305336649/1125899906842624)), (133577/1125899906842624), by norm_num⟩
  | 0 => ⟨((69799583431129/70368744177664), (-31894272099487/1125899906842624)), (67417/281474976710656), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((69799583431129/70368744177664), (-31894272099487/1125899906842624)), (257175446630382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1106856924586437/1125899906842624), (-1977268932037/35184372088832)), (550253/1125899906842624), by norm_num⟩
  | 2 => ⟨((1084580273464507/1125899906842624), (-31101220218869/281474976710656)), (1143739/1125899906842624), by norm_num⟩
  | 3 => ⟨((1031031078471315/1125899906842624), (-239678640881357/1125899906842624)), (1228141/562949953421312), by norm_num⟩
  | 4 => ⟨((893133774829903/1125899906842624), (-6858850365289/17592186044416)), (1386101/281474976710656), by norm_num⟩
  | 5 => ⟨((537344763252359/1125899906842624), (-174107723232283/281474976710656)), (6559821/562949953421312), by norm_num⟩
  | 6 => ⟨((-348657270221747/2251799813685248), (-1329508923513719/2251799813685248)), (28753347/1125899906842624), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-66258563/134217728), (-965940617/67108864)), (1/67108864), by norm_num⟩, -2, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((770374115/18014398509481984), (2527035/4503599627370496)), (2451/18014398509481984), by norm_num⟩
  | 1 => ⟨((65949957/2251799813685248), (72947687/2251799813685248)), (377/1125899906842624), by norm_num⟩
  | 2 => ⟨((-68917389/36028797018963968), (785040391/36028797018963968)), (8027/18014398509481984), by norm_num⟩
  | 3 => ⟨((-203391177/36028797018963968), (316471589/72057594037927936)), (14993/36028797018963968), by norm_num⟩
  | 4 => ⟨((-975793587/576460752303423488), (-19625511/72057594037927936)), (177187/576460752303423488), by norm_num⟩
  | 5 => ⟨((-826305697/4611686018427387904), (-613052303/2305843009213693952)), (908041/4611686018427387904), by norm_num⟩
  | 6 => ⟨((98323973/9223372036854775808), (-1748766535/36893488147419103232)), (279867/2305843009213693952), by norm_num⟩
  | 7 => ⟨((386703787/73786976294838206464), (-116337521/36893488147419103232)), (11952397/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1485524289/2361183241434822606848), (97404367/590295810358705651712)), (148806115/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((141343921/4722366482869645213696), (240544269/4722366482869645213696)), (1060260899/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-39450961/37778931862957161709568), (169947183/37778931862957161709568)), (508125165/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-9602845/37778931862957161709568), (6871625/37778931862957161709568)), (1002921557/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-174657/9444732965739290427392), (-1761/2361183241434822606848)), (1998520435/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((-3809/4722366482869645213696), (-10697/18889465931478580854784)), (1996677977/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-889/37778931862957161709568), (-1673/37778931862957161709568)), (499062483/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((-3/18889465931478580854784), (-97/37778931862957161709568)), (998078747/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((1/18889465931478580854784), (-5/37778931862957161709568)), (124758677/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-282360957/1125899906842624), (214816441/562949953421312)), (25643/2251799813685248), by norm_num⟩
  | 1 => ⟨((-568575949/1125899906842624), (1148159161/1125899906842624)), (35729/1125899906842624), by norm_num⟩
  | 2 => ⟨((-792581279/1125899906842624), (-155276151/1125899906842624)), (106985/2251799813685248), by norm_num⟩
  | 3 => ⟨((-11153145/562949953421312), (-76044229/562949953421312)), (130485/2251799813685248), by norm_num⟩
  | 4 => ⟨((-830700755/72057594037927936), (-1226966885/72057594037927936)), (4341725/72057594037927936), by norm_num⟩
  | 5 => ⟨((255035969/72057594037927936), (-662398835/72057594037927936)), (2024879/36028797018963968), by norm_num⟩
  | 6 => ⟨((472527957/288230376151711744), (162001271/576460752303423488)), (28381751/576460752303423488), by norm_num⟩
  | 7 => ⟨((64826175/4611686018427387904), (1068018285/9223372036854775808)), (392278559/9223372036854775808), by norm_num⟩
  | 8 => ⟨((160705191/36893488147419103232), (192291971/36893488147419103232)), (347167083/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-1045399/2305843009213693952), (29317793/18446744073709551616)), (79992663/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-2352991/18446744073709551616), (-8117/1152921504606846976)), (611699733/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-34199/18446744073709551616), (-36651/18446744073709551616)), (598755307/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-981/2305843009213693952), (-5687/36893488147419103232)), (37089325/1152921504606846976), by norm_num⟩
  | 13 => ⟨((7/2305843009213693952), (-1247/36893488147419103232)), (1182875059/36893488147419103232), by norm_num⟩
  | 14 => ⟨((23/36893488147419103232), (-5/18446744073709551616)), (1181508509/36893488147419103232), by norm_num⟩
  | 15 => ⟨((3/36893488147419103232), (-1/36893488147419103232)), (1181075235/36893488147419103232), by norm_num⟩
  | 16 => ⟨(0, 0), (590473807/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-282360971/1125899906842624), (429632897/1125899906842624)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-568575971/1125899906842624), (574079579/562949953421312)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-396290649/562949953421312), (-155276143/1125899906842624)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((-22306287/1125899906842624), (-152088481/1125899906842624)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-3244925/281474976710656), (-19171347/1125899906842624)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((3984937/1125899906842624), (-2587497/281474976710656)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((1845813/1125899906842624), (316411/1125899906842624)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((15827/1125899906842624), (130373/1125899906842624)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((4905/1125899906842624), (5869/1125899906842624)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((-255/562949953421312), (1789/1125899906842624)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-9/70368744177664), (-1/140737488355328)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((-1/562949953421312), (-1/562949953421312)), (1/4294967296), by norm_num⟩
  | 12 => ⟨(0, 0), (1/4294967296), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨33,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨33,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply FiniteBandTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(102823/524288)) (K:=(2123/1073741824)) (L:=(539086519801677/1180591620717411303424)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiBand97.Tile033
