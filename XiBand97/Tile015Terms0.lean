/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile015Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26461/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26461/1280))
  have he : value ((69/80), (26461/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-961615891/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-236363355800561/2251799813685248), (-1215722868283175/2251799813685248)), (51179355/2251799813685248), by norm_num⟩
  | 1 => ⟨((39061211/536870912), (1607274777/4294967296)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((-108300673/4294967296), (-278519495/2147483648)), (25/4294967296), by norm_num⟩
  | 3 => ⟨((100091075/17179869184), (1029626681/34359738368)), (3/2147483648), by norm_num⟩
  | 4 => ⟨((-138755693/137438953472), (-713682831/137438953472)), (17/68719476736), by norm_num⟩
  | 5 => ⟨((38471247/274877906944), (1582999175/2199023255552)), (39/1099511627776), by norm_num⟩
  | 6 => ⟨((-284439855/17592186044416), (-1463001887/17592186044416)), (37/8796093022208), by norm_num⟩
  | 7 => ⟨((112662105/70368744177664), (1158943581/140737488355328)), (15/35184372088832), by norm_num⟩
  | 8 => ⟨((-156182841/1125899906842624), (-1606636951/2251799813685248)), (85/2251799813685248), by norm_num⟩
  | 9 => ⟨((96229063/9007199254740992), (494949277/9007199254740992)), (27/9007199254740992), by norm_num⟩
  | 10 => ⟨((-53360723/72057594037927936), (-1097832627/288230376151711744)), (31/144115188075855872), by norm_num⟩
  | 11 => ⟨((215196129/4611686018427387904), (1106850313/4611686018427387904)), (1/72057594037927936), by norm_num⟩
  | 12 => ⟨((-198883453/73786976294838206464), (-511473449/36893488147419103232)), (61/73786976294838206464), by norm_num⟩
  | 13 => ⟨((339336627/2361183241434822606848), (436340159/590295810358705651712)), (53/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-268811687/37778931862957161709568), (-1382619205/37778931862957161709568)), (43/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((24843475/75557863725914323419136), (1022249177/604462909807314587353088)), (33/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-137761477/9671406556917033397649408), (-708569135/9671406556917033397649408)), (47/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-2296273496343/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781044470857321/633825300114114700748351602688), (-2724143521297/633825300114114700748351602688)), (11559/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892301521598599/39614081257132168796771975168), (-766122356467/9903520314283042199192993792)), (6503/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118264748797241/154742504910672534362390528), (-1627910236235/1237940039285380274899124224)), (13821/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773901562510359/154742504910672534362390528), (-3255595939133/154742504910672534362390528)), (27/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((776047080710525/4835703278458516698824704), (-3051882585247/9671406556917033397649408)), (12963/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630505559201965/302231454903657293676544), (-2670158608273/604462909807314587353088)), (22691/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236425271487009/9444732965739290427392), (-4338560164563/75557863725914323419136)), (9221/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300245884992553/4722366482869645213696), (-3253528398359/4722366482869645213696)), (27673/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812583783748929/295147905179352825856), (-4472964811039/590295810358705651712)), (38065/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457030274628509/18446744073709551616), (-5590250587889/73786976294838206464)), (47605/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827880271945399/9223372036854775808), (-3143858839901/4611686018427387904)), (53589/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599123884972275/1152921504606846976), (-3143037054841/576460752303423488)), (53629/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299767758082671/36028797018963968), (-1374616189359/36028797018963968)), (11743/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498361810246077/36028797018963968), (-8243994282443/36028797018963968)), (70549/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497643967611209/9007199254740992), (-10298506846905/9007199254740992)), (22087/2251799813685248), by norm_num⟩
  | 2 => ⟨((561165763810513/1125899906842624), (-10288765839081/2251799813685248)), (88589/2251799813685248), by norm_num⟩
  | 1 => ⟨((560258112295219/562949953421312), (-7704377179809/562949953421312)), (133489/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115008474015413/1125899906842624), (-15359840385891/562949953421312)), (269403/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115008474015413/1125899906842624), (-15359840385891/562949953421312)), (1027690891746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1103384226954293/1125899906842624), (-60845025692631/1125899906842624)), (68537/140737488355328), by norm_num⟩
  | 2 => ⟨((1078030673742335/1125899906842624), (-7453531307475/70368744177664)), (1133925/1125899906842624), by norm_num⟩
  | 3 => ⟨((509782447596481/562949953421312), (-28546535365439/140737488355328)), (2411643/1125899906842624), by norm_num⟩
  | 4 => ⟨((438475334219985/562949953421312), (-206803785388743/562949953421312)), (5346087/1125899906842624), by norm_num⟩
  | 5 => ⟨((531105161869811/1125899906842624), (-644308492186149/1125899906842624)), (6127931/562949953421312), by norm_num⟩
  | 6 => ⟨((-236363355800561/2251799813685248), (-1215722868283175/2251799813685248)), (51179355/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-961615891/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-1524125127/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-164068693559389/562949953421312), (143924240532785/562949953421312)), (78010747/2251799813685248), by norm_num⟩
  | 1 => ⟨((343795553/1073741824), (-1178063/4194304)), (21/536870912), by norm_num⟩
  | 2 => ⟨((-755396039/4294967296), (331324029/2147483648)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((1106516495/17179869184), (-970657733/17179869184)), (71/8589934592), by norm_num⟩
  | 4 => ⟨((-303908155/17179869184), (533188257/34359738368)), (5/2147483648), by norm_num⟩
  | 5 => ⟨((267101787/68719476736), (-468613737/137438953472)), (143/274877906944), by norm_num⟩
  | 6 => ⟨((-195627537/274877906944), (85804135/137438953472)), (107/1099511627776), by norm_num⟩
  | 7 => ⟨((982486017/8796093022208), (-861855791/8796093022208)), (137/8796093022208), by norm_num⟩
  | 8 => ⟨((-269842803/17592186044416), (946845363/70368744177664)), (153/70368744177664), by norm_num⟩
  | 9 => ⟨((527026879/281474976710656), (-924636401/562949953421312)), (19/70368744177664), by norm_num⟩
  | 10 => ⟨((-926397129/4503599627370496), (406326765/2251799813685248)), (17/562949953421312), by norm_num⟩
  | 11 => ⟨((370091371/18014398509481984), (-324651329/18014398509481984)), (55/18014398509481984), by norm_num⟩
  | 12 => ⟨((-1084231809/576460752303423488), (237777293/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 13 => ⟨((91626953/576460752303423488), (-643015523/4611686018427387904)), (113/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-460171413/36893488147419103232), (403671289/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 15 => ⟨((1078506601/1180591620717411303424), (-946086909/1180591620717411303424)), (43/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-592430303/9444732965739290427392), (64961419/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (3154283271451/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890250348632571/316912650057057350374175801344), (3739873785461/633825300114114700748351602688)), (11571/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472922403284735/9903520314283042199192993792), (525872952805/4951760157141521099596496896)), (26041/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891585620451951/2475880078570760549798248448), (2234742851387/1237940039285380274899124224)), (27675/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773250968796089/154742504910672534362390528), (2234498440409/77371252455336267181195264)), (55365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551483981936039/9671406556917033397649408), (4189165115297/9671406556917033397649408)), (51921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260476963612267/604462909807314587353088), (3664999917423/604462909807314587353088)), (5681/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((945266853065503/37778931862957161709568), (5954650485651/75557863725914323419136)), (73883/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649797064878439/2361183241434822606848), (4465135073771/4722366482869645213696)), (55439/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624270744982311/590295810358705651712), (1534543638177/147573952589676412928)), (4767/36893488147419103232), by norm_num⟩
  | 8 => ⟨((456749770678849/18446744073709551616), (239707445315/2305843009213693952)), (95405/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826616647683889/9223372036854775808), (8626607009105/9223372036854775808)), (26855/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597858567405463/1152921504606846976), (2155757269719/288230376151711744)), (107533/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299490494415073/36028797018963968), (471320187831/9007199254740992)), (47109/72057594037927936), by norm_num⟩
  | 4 => ⟨((374173608141053/9007199254740992), (11303623977123/36028797018963968)), (35395/9007199254740992), by norm_num⟩
  | 3 => ⟨((747776560450587/4503599627370496), (3528852840661/2251799813685248)), (88709/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120230779650807/2251799813685248), (14094208190511/2251799813685248)), (44521/562949953421312), by norm_num⟩
  | 1 => ⟨((1117340474262947/1125899906842624), (21088216401649/1125899906842624)), (134397/562949953421312), by norm_num⟩
  | 0 => ⟨((554279604261651/562949953421312), (20981762581573/562949953421312)), (544273/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554279604261651/562949953421312), (20981762581573/562949953421312)), (2076236729148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089921558657007/1125899906842624), (41317218305985/562949953421312)), (1112353/1125899906842624), by norm_num⟩
  | 2 => ⟨((1049028023479741/1125899906842624), (79993837288283/562949953421312)), (2316897/1125899906842624), by norm_num⟩
  | 3 => ⟨((954670776235917/1125899906842624), (149064364444995/562949953421312)), (2487935/562949953421312), by norm_num⟩
  | 4 => ⟨((182635140790605/281474976710656), (252788709989135/562949953421312)), (11073397/1125899906842624), by norm_num⟩
  | 5 => ⟨((493971062869359/2251799813685248), (1312176369741027/2251799813685248)), (48629635/2251799813685248), by norm_num⟩
  | 6 => ⟨((-164068693559389/562949953421312), (143924240532785/562949953421312)), (78010747/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1524125127/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-961615891/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1263091370608019/4503599627370496), (1993907378587/17592186044416)), (118890665/4503599627370496), by norm_num⟩
  | 1 => ⟨((834949705/2147483648), (-168709873/1073741824)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((-289371517/1073741824), (467763091/4294967296)), (57/2147483648), by norm_num⟩
  | 3 => ⟨((1069744273/8589934592), (-216152445/4294967296)), (107/8589934592), by norm_num⟩
  | 4 => ⟨((-741490227/17179869184), (599301831/34359738368)), (151/34359738368), by norm_num⟩
  | 5 => ⟨((25698093/2147483648), (-83080875/17179869184)), (43/34359738368), by norm_num⟩
  | 6 => ⟨((-1520005181/549755813888), (614264259/549755813888)), (161/549755813888), by norm_num⟩
  | 7 => ⟨((602049889/1099511627776), (-60825077/274877906944)), (65/1099511627776), by norm_num⟩
  | 8 => ⟨((-417309183/4398046511104), (337285845/8796093022208)), (23/2199023255552), by norm_num⟩
  | 9 => ⟨((64279263/4398046511104), (-415624413/70368744177664)), (29/17592186044416), by norm_num⟩
  | 10 => ⟨((-570303871/281474976710656), (28808889/35184372088832)), (65/281474976710656), by norm_num⟩
  | 11 => ⟨((574988393/2251799813685248), (-464728441/4503599627370496)), (133/4503599627370496), by norm_num⟩
  | 12 => ⟨((-1062804223/36028797018963968), (214750139/18014398509481984)), (125/36028797018963968), by norm_num⟩
  | 13 => ⟨((453341385/144115188075855872), (-366408501/288230376151711744)), (27/72057594037927936), by norm_num⟩
  | 14 => ⟨((-1436490527/4611686018427387904), (290257165/2305843009213693952)), (173/4611686018427387904), by norm_num⟩
  | 15 => ⟨((265519829/9223372036854775808), (-429207329/36893488147419103232)), (65/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-1472354567/590295810358705651712), (148751925/147573952589676412928)), (91/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (112250105975/316912650057057350374175801344)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890057673097095/316912650057057350374175801344), (1064278896105/158456325028528675187087900672)), (23155/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891256009209787/39614081257132168796771975168), (1197179849665/9903520314283042199192993792)), (3257/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1891124803679315/2475880078570760549798248448), (1271847615155/618970019642690137449562112)), (55385/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772790025455485/154742504910672534362390528), (5086688391139/154742504910672534362390528)), (27701/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775525856593979/4835703278458516698824704), (2384012157469/4835703278458516698824704)), (25979/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260098594217521/604462909807314587353088), (4171275108035/604462909807314587353088)), (22741/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889918604432117/75557863725914323419136), (3388461370367/37778931862957161709568)), (73943/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299132583747197/4722366482869645213696), (5081467414149/4722366482869645213696)), (867/73786976294838206464), by norm_num⟩
  | 9 => ⟨((101477235165683/36893488147419103232), (6985027193041/590295810358705651712)), (76345/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826204820827615/73786976294838206464), (4364148718665/36893488147419103232)), (95505/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228215296284225/1152921504606846976), (2453806701335/2305843009213693952)), (107545/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596963376152775/1152921504606846976), (9810090096211/1152921504606846976)), (53837/576460752303423488), by norm_num⟩
  | 5 => ⟨((149647207522899/18014398509481984), (8578047371347/144115188075855872)), (94359/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495515913438313/36028797018963968), (1606937686847/4503599627370496)), (141827/36028797018963968), by norm_num⟩
  | 3 => ⟨((373519103358455/2251799813685248), (8024557636983/4503599627370496)), (177789/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118748767388073/2251799813685248), (8009346670099/1125899906842624)), (44637/562949953421312), by norm_num⟩
  | 1 => ⟨((1115104309439837/1125899906842624), (11975941292065/562949953421312)), (67431/281474976710656), by norm_num⟩
  | 0 => ⟨((1104034985737591/1125899906842624), (47598526347519/1125899906842624)), (136769/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104034985737591/1125899906842624), (47598526347519/1125899906842624)), (521732331396007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1080582405796579/1125899906842624), (93348330589317/1125899906842624)), (1119161/1125899906842624), by norm_num⟩
  | 2 => ⟨((1029349427822011/1125899906842624), (44795528906371/281474976710656)), (1166905/562949953421312), by norm_num⟩
  | 3 => ⟨((456281241233415/562949953421312), (163816523186559/562949953421312)), (5010185/1125899906842624), by norm_num⟩
  | 4 => ⟨((322154246093073/562949953421312), (531105161869801/1125899906842624)), (2759397/281474976710656), by norm_num⟩
  | 5 => ⟨((236363355800573/2251799813685248), (607861434141573/1125899906842624)), (46091955/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1263091370608019/4503599627370496), (1993907378587/17592186044416)), (118890665/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-961615891/33554432)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-1116401477/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-157788243440925/2251799813685248), (-1078606020344401/4503599627370496)), (47955959/2251799813685248), by norm_num⟩
  | 1 => ⟨((60546489/536870912), (827765189/2147483648)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-97445815/1073741824), (-666118339/2147483648)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((52277663/1073741824), (357358703/2147483648)), (67/4294967296), by norm_num⟩
  | 4 => ⟨((-336550611/17179869184), (-575146645/8589934592)), (55/8589934592), by norm_num⟩
  | 5 => ⟨((216662925/34359738368), (1481060505/68719476736)), (9/4294967296), by norm_num⟩
  | 6 => ⟨((-464940701/274877906944), (-1589116619/274877906944)), (157/274877906944), by norm_num⟩
  | 7 => ⟨((427596109/1099511627776), (1461476877/1099511627776)), (147/1099511627776), by norm_num⟩
  | 8 => ⟨((-344094695/4398046511104), (-1176078147/4398046511104)), (15/549755813888), by norm_num⟩
  | 9 => ⟨((123066455/8796093022208), (105156931/2199023255552)), (87/17592186044416), by norm_num⟩
  | 10 => ⟨((-158454255/70368744177664), (-541579365/70368744177664)), (57/70368744177664), by norm_num⟩
  | 11 => ⟨((185470753/562949953421312), (1267837619/1125899906842624)), (135/1125899906842624), by norm_num⟩
  | 12 => ⟨((-199002441/4503599627370496), (-1360337287/9007199254740992)), (147/9007199254740992), by norm_num⟩
  | 13 => ⟨((394193321/72057594037927936), (1347309787/72057594037927936)), (147/72057594037927936), by norm_num⟩
  | 14 => ⟨((-362531243/576460752303423488), (-619546129/288230376151711744)), (137/576460752303423488), by norm_num⟩
  | 15 => ⟨((155592407/2305843009213693952), (265898941/1152921504606846976)), (119/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-250416319/36893488147419103232), (-855895673/36893488147419103232)), (97/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-2416904989829/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55619486355955/19807040628566084398385987584), (-2863521935227/633825300114114700748351602688)), (46241/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890928106671759/39614081257132168796771975168), (-1610529010115/19807040628566084398385987584)), (26015/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945388422444105/1237940039285380274899124224), (-1710944251461/1237940039285380274899124224)), (55293/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772442558913659/154742504910672534362390528), (-427667772271/19342813113834066795298816)), (55305/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550726486158849/9671406556917033397649408), (-1603463936245/4835703278458516698824704)), (51861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629907271619997/302231454903657293676544), (-2805481525657/604462909807314587353088)), (45391/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889458001220899/75557863725914323419136), (-569727427463/9444732965739290427392)), (73783/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298787988128043/4722366482869645213696), (-3417412633505/4722366482869645213696)), (27679/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623163335235843/590295810358705651712), (-4697395709365/590295810358705651712)), (38075/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825616372638001/73786976294838206464), (-366839065065/4611686018427387904)), (95237/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912531616183493/4611686018427387904), (-6599914372653/9223372036854775808)), (107211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596307818049217/1152921504606846976), (-3297964671903/576460752303423488)), (107297/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196608069884503/144115188075855872), (-1441739088203/36028797018963968)), (46991/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494669563476561/36028797018963968), (-2160368556049/9007199254740992)), (70583/18014398509481984), by norm_num⟩
  | 3 => ⟨((746516257111227/4503599627370496), (-10786169777263/9007199254740992)), (88399/4503599627370496), by norm_num⟩
  | 2 => ⟨((558862938889393/1125899906842624), (-10762675368141/2251799813685248)), (177309/2251799813685248), by norm_num⟩
  | 1 => ⟨((556811165850439/562949953421312), (-4021332503619/281474976710656)), (267241/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101279451607997/1125899906842624), (-31936246994635/1125899906842624)), (269803/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101279451607997/1125899906842624), (-31936246994635/1125899906842624)), (1029216768504905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((538145753142553/562949953421312), (-62475771359283/1125899906842624)), (1086225/1125899906842624), by norm_num⟩
  | 2 => ⟨((512701074703925/562949953421312), (-59723019474417/562949953421312)), (2197279/1125899906842624), by norm_num⟩
  | 3 => ⟨((57575178613027/70368744177664), (-54392146376431/281474976710656)), (4468517/1125899906842624), by norm_num⟩
  | 4 => ⟨((711678374752243/1125899906842624), (-356025969127691/1125899906842624)), (18078409/2251799813685248), by norm_num⟩
  | 5 => ⟨((674538857475473/2251799813685248), (-900172320962111/2251799813685248)), (4285993/281474976710656), by norm_num⟩
  | 6 => ⟨((-157788243440925/2251799813685248), (-1078606020344401/4503599627370496)), (47955959/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1116401477/33554432)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-1242870509/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((379699502963673/2251799813685248), (73471738140593/562949953421312)), (50059697/4503599627370496), by norm_num⟩
  | 1 => ⟨((-648813419/2147483648), (-125545199/536870912)), (11/536870912), by norm_num⟩
  | 2 => ⟨((1162517587/4294967296), (899787197/4294967296)), (81/4294967296), by norm_num⟩
  | 3 => ⟨((-347158649/2147483648), (-67175093/536870912)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((622024797/8589934592), (120361609/2147483648)), (23/4294967296), by norm_num⟩
  | 5 => ⟨((-55725941/2147483648), (-690108969/34359738368)), (17/8589934592), by norm_num⟩
  | 6 => ⟨((1065039813/137438953472), (12880305/2147483648)), (83/137438953472), by norm_num⟩
  | 7 => ⟨((-1090454383/549755813888), (-422005183/274877906944)), (87/549755813888), by norm_num⟩
  | 8 => ⟨((976915983/2199023255552), (756131783/2199023255552)), (5/137438953472), by norm_num⟩
  | 9 => ⟨((-777954873/8796093022208), (-301068063/4398046511104)), (33/4398046511104), by norm_num⟩
  | 10 => ⟨((139390801/8796093022208), (863106485/70368744177664)), (97/70368744177664), by norm_num⟩
  | 11 => ⟨((-363279691/140737488355328), (-562356079/281474976710656)), (65/281474976710656), by norm_num⟩
  | 12 => ⟨((867879769/2251799813685248), (671737887/2251799813685248)), (5/140737488355328), by norm_num⟩
  | 13 => ⟨((-956942643/18014398509481984), (-740672443/18014398509481984)), (45/9007199254740992), by norm_num⟩
  | 14 => ⟨((979777739/144115188075855872), (758346779/144115188075855872)), (47/72057594037927936), by norm_num⟩
  | 15 => ⟨((-234070139/288230376151711744), (-181170003/288230376151711744)), (23/288230376151711744), by norm_num⟩
  | 16 => ⟨((104849347/1152921504606846976), (649226137/9223372036854775808)), (21/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (214502443777/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444896182899357/158456325028528675187087900672), (1016296838589/633825300114114700748351602688)), (46151/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890659680219027/39614081257132168796771975168), (571588795213/19807040628566084398385987584)), (51923/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890491967356063/2475880078570760549798248448), (1214434659179/2475880078570760549798248448)), (55171/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772158047495455/154742504910672534362390528), (303554809823/38685626227668133590597632)), (6897/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550460145547273/9671406556917033397649408), (1138101704065/9671406556917033397649408)), (12933/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629790941937845/302231454903657293676544), (995610215501/604462909807314587353088)), (22635/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944540329072975/37778931862957161709568), (101089860473/4722366482869645213696)), (18393/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298505617799233/4722366482869645213696), (303175804661/1180591620717411303424)), (27593/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622776110436679/590295810358705651712), (1666857604461/590295810358705651712)), (18973/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825133892044629/73786976294838206464), (2082658422221/73786976294838206464)), (94883/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824522571559903/9223372036854775808), (2341735194997/9223372036854775808)), (6673/576460752303423488), by norm_num⟩
  | 6 => ⟨((797884908324237/576460752303423488), (2340166752641/1152921504606846976)), (53399/576460752303423488), by norm_num⟩
  | 5 => ⟨((598070153239803/72057594037927936), (1022941372005/72057594037927936)), (93483/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493973883989993/36028797018963968), (1532650558557/18014398509481984)), (140293/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492173332175201/9007199254740992), (478183579283/1125899906842624)), (175487/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116882276700233/2251799813685248), (7632493890949/4503599627370496)), (351337/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224791450503119/2251799813685248), (2850684229009/562949953421312)), (527917/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197960955549353/2251799813685248), (2827760504423/281474976710656)), (1059491/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197960955549353/2251799813685248), (2827760504423/281474976710656)), (4041637429244231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2145182077943151/2251799813685248), (44162413675269/2251799813685248)), (261201/281474976710656), by norm_num⟩
  | 2 => ⟨((1021373170206201/1125899906842624), (21035710581185/562949953421312)), (4063303/2251799813685248), by norm_num⟩
  | 3 => ⟨((924978447914565/1125899906842624), (76331156165015/1125899906842624)), (1918953/562949953421312), by norm_num⟩
  | 4 => ⟨((754737324819521/1125899906842624), (125419096187755/1125899906842624)), (13652839/2251799813685248), by norm_num⟩
  | 5 => ⟨((245980338225837/562949953421312), (336294452331843/2251799813685248)), (21345831/2251799813685248), by norm_num⟩
  | 6 => ⟨((379699502963673/2251799813685248), (73471738140593/562949953421312)), (50059697/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1242870509/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-168724819/4194304)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-687387252533969/4503599627370496), (-484092749833039/4503599627370496)), (37860475/2251799813685248), by norm_num⟩
  | 1 => ⟨((637814441/2147483648), (224590539/1073741824)), (9/268435456), by norm_num⟩
  | 2 => ⟨((-620564797/2147483648), (-874066019/4294967296)), (71/2147483648), by norm_num⟩
  | 3 => ⟨((805042225/4294967296), (35434457/268435456)), (47/2147483648), by norm_num⟩
  | 4 => ⟨((-391634959/4294967296), (-137904539/2147483648)), (93/8589934592), by norm_num⟩
  | 5 => ⟨((609669153/17179869184), (858719495/34359738368)), (147/34359738368), by norm_num⟩
  | 6 => ⟨((-790907595/68719476736), (-278498497/34359738368)), (97/68719476736), by norm_num⟩
  | 7 => ⟨((439724319/137438953472), (619352059/274877906944)), (55/137438953472), by norm_num⟩
  | 8 => ⟨((-855664015/1099511627776), (-602601729/1099511627776)), (109/1099511627776), by norm_num⟩
  | 9 => ⟨((740020129/4398046511104), (130289869/1099511627776)), (3/137438953472), by norm_num⟩
  | 10 => ⟨((-36000317/1099511627776), (-811303611/35184372088832)), (151/35184372088832), by norm_num⟩
  | 11 => ⟨((407583315/70368744177664), (574081429/140737488355328)), (109/140737488355328), by norm_num⟩
  | 12 => ⟨((-264373503/281474976710656), (-372370293/562949953421312)), (143/1125899906842624), by norm_num⟩
  | 13 => ⟨((79145705/562949953421312), (222953579/2251799813685248)), (87/4503599627370496), by norm_num⟩
  | 14 => ⟨((-704047683/36028797018963968), (-495825865/36028797018963968)), (49/18014398509481984), by norm_num⟩
  | 15 => ⟨((182668471/72057594037927936), (257288689/144115188075855872)), (13/36028797018963968), by norm_num⟩
  | 16 => ⟨((-710912863/2305843009213693952), (-500660671/2305843009213693952)), (103/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-1646513997485/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779372037462603/633825300114114700748351602688), (-3899676124307/633825300114114700748351602688)), (11573/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945209997984021/19807040628566084398385987584), (-137077107639/1237940039285380274899124224)), (52091/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890236785341663/2475880078570760549798248448), (-291238836167/154742504910672534362390528)), (55361/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221487785455719/19342813113834066795298816), (-2329460521867/77371252455336267181195264)), (27689/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550219749072271/9671406556917033397649408), (-2183390967303/4835703278458516698824704)), (51933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314842729867463/151115727451828646838272), (-1909988859215/302231454903657293676544)), (45459/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472184170997605/18889465931478580854784), (-6205670551075/75557863725914323419136)), (36951/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298246625608869/4722366482869645213696), (-2326341987711/2361183241434822606848)), (55455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622418353862953/590295810358705651712), (-3197445610421/295147905179352825856)), (76295/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824684235475123/73786976294838206464), (-3994895323467/36893488147419103232)), (95437/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824013328495361/9223372036854775808), (-8983258128275/9223372036854775808)), (107461/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595256355672399/1152921504606846976), (-8976688890453/1152921504606846976)), (107579/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195686291725083/144115188075855872), (-3923607020867/72057594037927936)), (94263/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493283410913221/36028797018963968), (-11756047744779/36028797018963968)), (35415/9007199254740992), by norm_num⟩
  | 3 => ⟨((745646875399379/4503599627370496), (-7334607890313/4503599627370496)), (88769/4503599627370496), by norm_num⟩
  | 2 => ⟨((557989029196527/1125899906842624), (-14630468872915/2251799813685248)), (178235/2251799813685248), by norm_num⟩
  | 1 => ⟨((555489074137073/562949953421312), (-341389108255/17592186044416)), (269099/1125899906842624), by norm_num⟩
  | 0 => ⟨((136987797234099/140737488355328), (-21655505175767/562949953421312)), (545201/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((136987797234099/140737488355328), (-21655505175767/562949953421312)), (2079776768210982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((532518996991613/562949953421312), (-21078534132499/281474976710656)), (1103297/1125899906842624), by norm_num⟩
  | 2 => ⟨((500576049504271/562949953421312), (-159512863068185/1125899906842624)), (1126279/562949953421312), by norm_num⟩
  | 3 => ⟨((216906752973367/281474976710656), (-141839107285669/562949953421312)), (36283/8796093022208), by norm_num⟩
  | 4 => ⟨((1194250569271571/2251799813685248), (-874418339150665/2251799813685248)), (18996075/2251799813685248), by norm_num⟩
  | 5 => ⟨((146910703682771/1125899906842624), (-231875540837519/562949953421312)), (2181399/140737488355328), by norm_num⟩
  | 6 => ⟨((-687387252533969/4503599627370496), (-484092749833039/4503599627370496)), (37860475/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-168724819/4194304)), (1/33554432), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-360605959/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((816326940344261/9007199254740992), (314175285354259/2251799813685248)), (190436867/9007199254740992), by norm_num⟩
  | 1 => ⟨((-25294783/134217728), (-1246088295/4294967296)), (3/67108864), by norm_num⟩
  | 2 => ⟨((841584361/4294967296), (1295583883/4294967296)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-583341827/4294967296), (-224507579/1073741824)), (71/2147483648), by norm_num⟩
  | 4 => ⟨((303256307/4294967296), (233425193/2147483648)), (75/4294967296), by norm_num⟩
  | 5 => ⟨((-252241505/8589934592), (-776630469/17179869184)), (127/17179869184), by norm_num⟩
  | 6 => ⟨((21855061/2147483648), (134579805/8589934592)), (89/34359738368), by norm_num⟩
  | 7 => ⟨((-831018455/274877906944), (-1279318113/274877906944)), (107/137438953472), by norm_num⟩
  | 8 => ⟨((216006787/274877906944), (665066807/549755813888)), (113/549755813888), by norm_num⟩
  | 9 => ⟨((-399265321/2199023255552), (-614652243/2199023255552)), (211/4398046511104), by norm_num⟩
  | 10 => ⟨((166049779/4398046511104), (511253363/8796093022208)), (89/8796093022208), by norm_num⟩
  | 11 => ⟨((-62780147/8796093022208), (-773179259/70368744177664)), (137/70368744177664), by norm_num⟩
  | 12 => ⟨((348127055/281474976710656), (1071854047/562949953421312)), (3/8796093022208), by norm_num⟩
  | 13 => ⟨((-445482991/2251799813685248), (-342901205/1125899906842624)), (125/2251799813685248), by norm_num⟩
  | 14 => ⟨((529346193/18014398509481984), (407453149/9007199254740992)), (151/18014398509481984), by norm_num⟩
  | 15 => ⟨((-293531857/72057594037927936), (-903760005/144115188075855872)), (85/72057594037927936), by norm_num⟩
  | 16 => ⟨((610382337/1152921504606846976), (939658049/1152921504606846976)), (179/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (323932478567/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889600632501121/316912650057057350374175801344), (1534140376009/633825300114114700748351602688)), (92351/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890228303527097/39614081257132168796771975168), (862817471977/19807040628566084398385987584)), (103905/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890033655566033/2475880078570760549798248448), (916575787573/1237940039285380274899124224)), (55205/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771699764914185/154742504910672534362390528), (114548386247/9671406556917033397649408)), (110423/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550030536675625/9671406556917033397649408), (1717824910125/9671406556917033397649408)), (103535/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78700375448565/37778931862957161709568), (1502696023941/604462909807314587353088)), (45303/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888469916789157/75557863725914323419136), (2441129826771/75557863725914323419136)), (36815/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298047612808737/4722366482869645213696), (915095147769/2361183241434822606848)), (110467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811073218278165/295147905179352825856), (2515444352721/590295810358705651712)), (18991/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912173462137941/36893488147419103232), (392838157433/9223372036854775808)), (47491/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823637404297241/9223372036854775808), (441668053077/1152921504606846976)), (26723/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594884863997831/1152921504606846976), (1765298784507/576460752303423488)), (53469/288230376151711744), by norm_num⟩
  | 5 => ⟨((298841553678289/36028797018963968), (3086185250165/144115188075855872)), (187245/144115188075855872), by norm_num⟩
  | 4 => ⟨((11662603366051/281474976710656), (4623109099281/36028797018963968)), (281077/36028797018963968), by norm_num⟩
  | 3 => ⟨((372680841423335/2251799813685248), (5768105558483/9007199254740992)), (10991/281474976710656), by norm_num⟩
  | 2 => ⟨((1115433589183591/2251799813685248), (5751963384719/2251799813685248)), (704521/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220451811046969/2251799813685248), (17175382318399/2251799813685248)), (1059533/2251799813685248), by norm_num⟩
  | 0 => ⟨((2189307537458237/2251799813685248), (34029948978451/2251799813685248)), (1065057/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189307537458237/2251799813685248), (34029948978451/2251799813685248)), (4062870029929732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2128035284052021/2251799813685248), (16542772440307/562949953421312)), (4206381/2251799813685248), by norm_num⟩
  | 2 => ⟨((2009128666569183/2251799813685248), (62534161758195/1125899906842624)), (8197593/2251799813685248), by norm_num⟩
  | 3 => ⟨((1785663134371723/2251799813685248), (223180011410775/2251799813685248)), (7769465/1125899906842624), by norm_num⟩
  | 4 => ⟨((1393899889717135/2251799813685248), (353960699599371/2251799813685248)), (27724733/2251799813685248), by norm_num⟩
  | 5 => ⟨((807207068161981/2251799813685248), (54776825312937/281474976710656)), (43040211/2251799813685248), by norm_num⟩
  | 6 => ⟨((816326940344261/9007199254740992), (314175285354259/2251799813685248)), (190436867/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-360605959/8388608)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile015Terms0
