/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile059Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨59,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (15847/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (15847/512))
  have he : value ((69/80), (15847/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2567700857/1073741824), (-92143015127/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-450945760968707/9007199254740992), (86237776048659/1125899906842624)), (4659339/9007199254740992), by norm_num⟩
  | 1 => ⟨((38155735205/274877906944), (-58374483717/274877906944)), (99/68719476736), by norm_num⟩
  | 2 => ⟨((-52895080559/274877906944), (40462108805/137438953472)), (551/274877906944), by norm_num⟩
  | 3 => ⟨((24442717303/137438953472), (-18697464425/68719476736)), (1/536870912), by norm_num⟩
  | 4 => ⟨((-2117800073/17179869184), (51840378999/274877906944)), (357/274877906944), by norm_num⟩
  | 5 => ⟨((37579447029/549755813888), (-14373205017/137438953472)), (199/274877906944), by norm_num⟩
  | 6 => ⟨((-34730783673/1099511627776), (53134648177/1099511627776)), (185/549755813888), by norm_num⟩
  | 7 => ⟨((27512622607/2199023255552), (-21045789471/1099511627776)), (295/2199023255552), by norm_num⟩
  | 8 => ⟨((-9535148395/2199023255552), (29175659269/4398046511104)), (411/8796093022208), by norm_num⟩
  | 9 => ⟨((23499595471/17592186044416), (-35952046157/17592186044416)), (509/35184372088832), by norm_num⟩
  | 10 => ⟨((-3257735669/8796093022208), (79744190173/140737488355328)), (567/140737488355328), by norm_num⟩
  | 11 => ⟨((52551919569/562949953421312), (-80399215395/562949953421312)), (287/281474976710656), by norm_num⟩
  | 12 => ⟨((-24284143255/1125899906842624), (74304652627/2251799813685248)), (533/2251799813685248), by norm_num⟩
  | 13 => ⟨((2589613143/562949953421312), (-63389612887/9007199254740992)), (57/1125899906842624), by norm_num⟩
  | 14 => ⟨((-16411273589/18014398509481984), (25107617971/18014398509481984)), (363/36028797018963968), by norm_num⟩
  | 15 => ⟨((24267579771/144115188075855872), (-74253971657/288230376151711744)), (539/288230376151711744), by norm_num⟩
  | 16 => ⟨((-16821004497/576460752303423488), (51468931099/1152921504606846976)), (47/144115188075855872), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (1400127906995/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889137529428385/316912650057057350374175801344), (1656112423241/316912650057057350374175801344)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889186256525893/39614081257132168796771975168), (931367248171/9903520314283042199192993792)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236115797115101/309485009821345068724781056), (3957344259533/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27665505779733/2417851639229258349412352), (3956257183163/154742504910672534362390528)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548992230440243/9671406556917033397649408), (3707836400643/9671406556917033397649408)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258297366063839/604462909807314587353088), (405400311323/75557863725914323419136)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886993144602001/75557863725914323419136), (2634020181451/37778931862957161709568)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296939832628609/4722366482869645213696), (3949137788971/4722366482869645213696)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810311456566385/295147905179352825856), (2713495281467/295147905179352825856)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455610508313673/18446744073709551616), (3389564893691/36893488147419103232)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821493735504537/9223372036854775808), (3810094192383/4611686018427387904)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592740366520509/1152921504606846976), (7612278520205/1152921504606846976)), (6715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596744426531569/72057594037927936), (3325926621133/72057594037927936)), (5883/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489995350416095/36028797018963968), (9960019266801/36028797018963968)), (8837/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487197831815273/9007199254740992), (6209494379675/4503599627370496)), (173/140737488355328), by norm_num⟩
  | 2 => ⟨((2223806692622789/4503599627370496), (24745054321039/4503599627370496)), (2777/562949953421312), by norm_num⟩
  | 1 => ⟨((552459499392785/562949953421312), (2305369545339/140737488355328)), (16755/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167990316615337/2251799813685248), (36424491020855/1125899906842624)), (67767/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2167990316615337/2251799813685248), (36424491020855/1125899906842624)), (258510598189543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((260617918288095/281474976710656), (4383601471861/70368744177664)), (134875/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921712394704245/2251799813685248), (129880969575543/1125899906842624)), (266567/2251799813685248), by norm_num⟩
  | 3 => ⟨((1610046435253483/2251799813685248), (443367776394023/2251799813685248)), (516485/2251799813685248), by norm_num⟩
  | 4 => ⟨((531946606436377/1125899906842624), (634019688207719/2251799813685248)), (941965/2251799813685248), by norm_num⟩
  | 5 => ⟨((648270595748189/4503599627370496), (1198204634377283/4503599627370496)), (2841061/4503599627370496), by norm_num⟩
  | 6 => ⟨((-450945760968707/9007199254740992), (86237776048659/1125899906842624)), (4659339/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-92143015127/1073741824)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-655961365/268435456), (-47078893801/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1506362920041229/18014398509481984), (52786148638235/2251799813685248)), (1944433/9007199254740992), by norm_num⟩
  | 1 => ⟨((-65122185151/274877906944), (-18256154871/274877906944)), (85/137438953472), by norm_num⟩
  | 2 => ⟨((92252521981/274877906944), (6465447699/68719476736)), (243/274877906944), by norm_num⟩
  | 3 => ⟨((-87123692099/274877906944), (-24423990261/274877906944)), (29/34359738368), by norm_num⟩
  | 4 => ⟨((61710001759/274877906944), (17299593781/274877906944)), (83/137438953472), by norm_num⟩
  | 5 => ⟨((-34967520089/274877906944), (-19605375979/549755813888)), (95/274877906944), by norm_num⟩
  | 6 => ⟨((8255870377/137438953472), (2314425535/137438953472)), (181/1099511627776), by norm_num⟩
  | 7 => ⟨((-53464324843/2199023255552), (-29976051701/4398046511104)), (295/4398046511104), by norm_num⟩
  | 8 => ⟨((9467239911/1099511627776), (5308034355/2199023255552)), (211/8796093022208), by norm_num⟩
  | 9 => ⟨((-95369637145/35184372088832), (-1670977085/2199023255552)), (67/8796093022208), by norm_num⟩
  | 10 => ⟨((54040505715/70368744177664), (15149550639/70368744177664)), (77/35184372088832), by norm_num⟩
  | 11 => ⟨((-55675738877/281474976710656), (-15607966919/281474976710656)), (161/281474976710656), by norm_num⟩
  | 12 => ⟨((26290207721/562949953421312), (14740233383/1125899906842624)), (307/2251799813685248), by norm_num⟩
  | 13 => ⟨((-91674790563/9007199254740992), (-6424957833/2251799813685248)), (135/4503599627370496), by norm_num⟩
  | 14 => ⟨((74209782839/36028797018963968), (10401872153/18014398509481984)), (221/36028797018963968), by norm_num⟩
  | 15 => ⟨((-56067239199/144115188075855872), (-7858859463/72057594037927936)), (169/144115188075855872), by norm_num⟩
  | 16 => ⟨((79425225131/1152921504606846976), (5566456375/288230376151711744)), (121/576460752303423488), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (356031289489/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778200281217337/633825300114114700748351602688), (52635988621/79228162514264337593543950336)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889102471616121/39614081257132168796771975168), (236811875913/19807040628566084398385987584)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888837803540353/2475880078570760549798248448), (251549929171/1237940039285380274899124224)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770504300137243/154742504910672534362390528), (251479436709/77371252455336267181195264)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548910199743559/9671406556917033397649408), (58921775381/1208925819614629174706176)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((314556530870713/151115727451828646838272), (412302749575/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886878376267073/75557863725914323419136), (167427863697/18889465931478580854784)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296854631216623/4722366482869645213696), (251019137527/2361183241434822606848)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620507181095305/590295810358705651712), (689904238999/590295810358705651712)), (4739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455574873768665/18446744073709551616), (430891575507/36893488147419103232)), (1481/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455334074910375/2305843009213693952), (484342837387/4611686018427387904)), (6665/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24884165201169/18014398509481984), (967661273125/1152921504606846976)), (3333/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193358371136667/144115188075855872), (845552619331/144115188075855872)), (2917/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489807777644653/36028797018963968), (1266030577687/36028797018963968)), (547/2251799813685248), by norm_num⟩
  | 3 => ⟨((1486977572633407/9007199254740992), (789262139533/4503599627370496)), (10943/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111704285754085/2251799813685248), (1572519673687/2251799813685248)), (10947/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209346030872723/2251799813685248), (4687649850345/2251799813685248)), (32867/2251799813685248), by norm_num⟩
  | 0 => ⟨((541855648930233/562949953421312), (578521481019/140737488355328)), (65833/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541855648930233/562949953421312), (578521481019/140737488355328)), (251132973677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1043084513994827/1125899906842624), (17818998260147/2251799813685248)), (63637/1125899906842624), by norm_num⟩
  | 2 => ⟨((1932580183281153/2251799813685248), (33016649219171/2251799813685248)), (14865/140737488355328), by norm_num⟩
  | 3 => ⟨((414532415691821/562949953421312), (56672286418649/2251799813685248)), (207611/1125899906842624), by norm_num⟩
  | 4 => ⟨((304887474211849/562949953421312), (41731062679953/1125899906842624)), (632405/2251799813685248), by norm_num⟩
  | 5 => ⟨((657401255446511/2251799813685248), (180808659375021/4503599627370496)), (731887/2251799813685248), by norm_num⟩
  | 6 => ⟨((1506362920041229/18014398509481984), (52786148638235/2251799813685248)), (1944433/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-47078893801/536870912)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83649375/33554432), (-48028682811/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((111580215236217/18014398509481984), (-1484994036316503/18014398509481984)), (920253/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1230271541/68719476736), (65493542835/274877906944)), (163/137438953472), by norm_num⟩
  | 2 => ⟨((7111884233/274877906944), (-23662585817/68719476736)), (473/274877906944), by norm_num⟩
  | 3 => ⟨((-1712999111/68719476736), (45595779843/137438953472)), (457/274877906944), by norm_num⟩
  | 4 => ⟨((1237801063/68719476736), (-65894377169/274877906944)), (83/68719476736), by norm_num⟩
  | 5 => ⟨((-5724328375/549755813888), (38091849355/274877906944)), (193/274877906944), by norm_num⟩
  | 6 => ⟨((5515145689/1099511627776), (-73399737055/1099511627776)), (187/549755813888), by norm_num⟩
  | 7 => ⟨((-4554520383/2199023255552), (121230015441/4398046511104)), (155/1099511627776), by norm_num⟩
  | 8 => ⟨((6582128543/8796093022208), (-43799976605/4398046511104)), (225/4398046511104), by norm_num⟩
  | 9 => ⟨((-8455465977/35184372088832), (112531747001/35184372088832)), (145/8796093022208), by norm_num⟩
  | 10 => ⟨((1221972003/17592186044416), (-8131464585/8796093022208)), (337/70368744177664), by norm_num⟩
  | 11 => ⟨((-5137386715/281474976710656), (68372234435/281474976710656)), (89/70368744177664), by norm_num⟩
  | 12 => ⟨((2474826245/562949953421312), (-65873725145/1125899906842624)), (345/1125899906842624), by norm_num⟩
  | 13 => ⟨((-4401949467/4503599627370496), (3661529899/281474976710656)), (77/1125899906842624), by norm_num⟩
  | 14 => ⟨((454402515/2251799813685248), (-96760526727/36028797018963968)), (511/36028797018963968), by norm_num⟩
  | 15 => ⟨((-5603806703/144115188075855872), (74579704995/144115188075855872)), (99/36028797018963968), by norm_num⟩
  | 16 => ⟨((2024635579/288230376151711744), (-107781536515/1152921504606846976)), (575/1152921504606846976), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-974222446727/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778121581232065/633825300114114700748351602688), (-288036408207/79228162514264337593543950336)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944506900261411/19807040628566084398385987584), (-2591765220571/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944371705789771/1237940039285380274899124224), (-2753050169121/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770409707118165/154742504910672534362390528), (-1376131274963/77371252455336267181195264)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774410652668797/4835703278458516698824704), (-2579409576227/9671406556917033397649408)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258148127622781/604462909807314587353088), (-1128073565533/302231454903657293676544)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943375616778617/37778931862957161709568), (-114520993575/2361183241434822606848)), (4609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81047432818247/295147905179352825856), (-2747133135301/4722366482869645213696)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810187509338417/295147905179352825856), (-943770478683/147573952589676412928)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911066721832959/36893488147419103232), (-4715515374707/73786976294838206464)), (2973/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910574163741775/4611686018427387904), (-2650184984907/4611686018427387904)), (6693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796198574309483/576460752303423488), (-330915268343/72057594037927936)), (3349/576460752303423488), by norm_num⟩
  | 5 => ⟨((18643609310011/2251799813685248), (-4626379730593/144115188075855872)), (2933/72057594037927936), by norm_num⟩
  | 4 => ⟨((744776733939291/18014398509481984), (-6926719923613/36028797018963968)), (1101/4503599627370496), by norm_num⟩
  | 3 => ⟨((743327014449219/4503599627370496), (-4317977140569/4503599627370496)), (5513/4503599627370496), by norm_num⟩
  | 2 => ⟨((555686153946411/1125899906842624), (-4301184160927/1125899906842624)), (2763/562949953421312), by norm_num⟩
  | 1 => ⟨((276038534986671/281474976710656), (-3204968915877/281474976710656)), (33285/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165181932290917/2251799813685248), (-50613535678485/2251799813685248)), (16773/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165181932290917/2251799813685248), (-50613535678485/2251799813685248)), (63983919383811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2080758263434191/2251799813685248), (-48666632048907/1125899906842624)), (132039/2251799813685248), by norm_num⟩
  | 2 => ⟨((1918501440622993/2251799813685248), (-179880105103213/2251799813685248)), (127717/1125899906842624), by norm_num⟩
  | 3 => ⟨((405041658597733/562949953421312), (-306510586494051/2251799813685248)), (476063/2251799813685248), by norm_num⟩
  | 4 => ⟨((140498234355619/281474976710656), (-220533913497637/1125899906842624)), (12729/35184372088832), by norm_num⟩
  | 5 => ⟨((474644065757985/2251799813685248), (-55039751355595/281474976710656)), (2264821/4503599627370496), by norm_num⟩
  | 6 => ⟨((111580215236217/18014398509481984), (-1484994036316503/18014398509481984)), (920253/2251799813685248), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-48028682811/536870912)), (1/536870912), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2726851779/1073741824), (-48927106141/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-355196566528489/4503599627370496), (9823676347813/4503599627370496)), (7266365/18014398509481984), by norm_num⟩
  | 1 => ⟨((127667799775/549755813888), (-1765455051/274877906944)), (655/549755813888), by norm_num⟩
  | 2 => ⟨((-93977511511/274877906944), (1299568667/137438953472)), (121/68719476736), by norm_num⟩
  | 3 => ⟨((23059254005/68719476736), (-1275500213/137438953472)), (477/274877906944), by norm_num⟩
  | 4 => ⟨((-67896566323/274877906944), (1877816273/274877906944)), (353/274877906944), by norm_num⟩
  | 5 => ⟨((79966918573/549755813888), (-552911543/137438953472)), (209/274877906944), by norm_num⟩
  | 6 => ⟨((-39242952015/549755813888), (542671433/274877906944)), (103/274877906944), by norm_num⟩
  | 7 => ⟨((66027701469/2199023255552), (-3652258103/4398046511104)), (87/549755813888), by norm_num⟩
  | 8 => ⟨((-97207268955/8796093022208), (672115695/2199023255552)), (257/4398046511104), by norm_num⟩
  | 9 => ⟨((63604638171/17592186044416), (-3518228713/35184372088832)), (675/35184372088832), by norm_num⟩
  | 10 => ⟨((-74911990355/70368744177664), (64745061/2199023255552)), (399/70368744177664), by norm_num⟩
  | 11 => ⟨((20052162219/70368744177664), (-1109165855/140737488355328)), (429/281474976710656), by norm_num⟩
  | 12 => ⟨((-39361578703/562949953421312), (544311863/281474976710656)), (423/1125899906842624), by norm_num⟩
  | 13 => ⟨((17830425633/1125899906842624), (-61642041/140737488355328)), (385/4503599627370496), by norm_num⟩
  | 14 => ⟨((-60000685999/18014398509481984), (3318879603/36028797018963968)), (325/18014398509481984), by norm_num⟩
  | 15 => ⟨((23555781151/36028797018963968), (-2605930259/144115188075855872)), (1/281474976710656), by norm_num⟩
  | 16 => ⟨((-34679280103/288230376151711744), (959125329/288230376151711744)), (189/288230376151711744), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (1014064506239/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444510064184507/158456325028528675187087900672), (2398343450213/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472230451491313/9903520314283042199192993792), (674381578783/4951760157141521099596496896)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888644993769653/2475880078570760549798248448), (2865377483425/1237940039285380274899124224)), (3465/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770310532290097/154742504910672534362390528), (5729080631119/154742504910672534362390528)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548727525247051/9671406556917033397649408), (5369234460235/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314516316769247/151115727451828646838272), (4696301914355/604462909807314587353088)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235826885142853/9444732965739290427392), (1907039312415/18889465931478580854784)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296655496290957/4722366482869645213696), (5718202082435/4722366482869645213696)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620230670902907/590295810358705651712), (3928895584089/295147905179352825856)), (4777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227743726776893/9223372036854775808), (4907568332513/36893488147419103232)), (5977/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910468679875951/4611686018427387904), (5516133780387/4611686018427387904)), (6731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796090356181491/576460752303423488), (11020072785827/1152921504606846976)), (1685/288230376151711744), by norm_num⟩
  | 5 => ⟨((596497739407439/72057594037927936), (9628853801577/144115188075855872)), (1477/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489247963641937/36028797018963968), (7207942025643/18014398509481984)), (4441/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486250842492487/9007199254740992), (2246495379131/1125899906842624)), (5569/4503599627370496), by norm_num⟩
  | 2 => ⟨((69433584381385/140737488355328), (8950114708633/1125899906842624)), (1399/281474976710656), by norm_num⟩
  | 1 => ⟨((551711465021551/562949953421312), (6667844137785/281474976710656)), (8461/562949953421312), by norm_num⟩
  | 0 => ⟨((1080817369040989/1125899906842624), (26314544589201/562949953421312)), (17193/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080817369040989/1125899906842624), (26314544589201/562949953421312)), (65586092235374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1035079901073155/1125899906842624), (50521750073095/562949953421312)), (34617/562949953421312), by norm_num⟩
  | 2 => ⟨((942517719589925/1125899906842624), (185785779889975/1125899906842624)), (69863/562949953421312), by norm_num⟩
  | 3 => ⟨((94793428188263/140737488355328), (622102865556453/2251799813685248)), (280049/1125899906842624), by norm_num⟩
  | 4 => ⟨((424849332548359/1125899906842624), (104754006912057/281474976710656)), (531991/1125899906842624), by norm_num⟩
  | 5 => ⟨((17488318138297/4503599627370496), (39528087397359/140737488355328)), (398729/562949953421312), by norm_num⟩
  | 6 => ⟨((-355196566528489/4503599627370496), (9823676347813/4503599627370496)), (7266365/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-48927106141/536870912)), (1/536870912), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1387177309/536870912), (-3111214733/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((7551518831461/2251799813685248), (1358477291418195/18014398509481984)), (3399007/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2761514731/274877906944), (-7762211351/34359738368)), (39/34359738368), by norm_num⟩
  | 2 => ⟨((2068189701/137438953472), (93014028233/274877906944)), (469/274877906944), by norm_num⟩
  | 3 => ⟨((-2065247545/137438953472), (-92881708757/274877906944)), (235/137438953472), by norm_num⟩
  | 4 => ⟨((1546732181/137438953472), (69562183137/274877906944)), (177/137438953472), by norm_num⟩
  | 5 => ⟨((-3706876411/549755813888), (-83355870817/549755813888)), (213/274877906944), by norm_num⟩
  | 6 => ⟨((925400775/274877906944), (83237290799/1099511627776)), (427/1099511627776), by norm_num⟩
  | 7 => ⟨((-1584144553/1099511627776), (-71244753831/2199023255552)), (367/2199023255552), by norm_num⟩
  | 8 => ⟨((4745672963/8796093022208), (106715104187/8796093022208)), (69/1099511627776), by norm_num⟩
  | 9 => ⟨((-3159281257/17592186044416), (-71042195931/17592186044416)), (369/17592186044416), by norm_num⟩
  | 10 => ⟨((3785744329/70368744177664), (42564679827/35184372088832)), (111/17592186044416), by norm_num⟩
  | 11 => ⟨((-2062013903/140737488355328), (-23184070013/70368744177664)), (485/281474976710656), by norm_num⟩
  | 12 => ⟨((4118161065/1125899906842624), (46302177847/562949953421312)), (243/562949953421312), by norm_num⟩
  | 13 => ⟨((-3795971695/4503599627370496), (-85359340623/4503599627370496)), (225/2251799813685248), by norm_num⟩
  | 14 => ⟨((3249061405/18014398509481984), (36530533079/9007199254740992)), (387/18014398509481984), by norm_num⟩
  | 15 => ⟨((-324443937/9007199254740992), (-116731410043/144115188075855872)), (155/36028797018963968), by norm_num⟩
  | 16 => ⟨((971947173/144115188075855872), (87424013101/576460752303423488)), (233/288230376151711744), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (1988247958953/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777981482917629/633825300114114700748351602688), (1175505357441/316912650057057350374175801344)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888856218720811/39614081257132168796771975168), (1322146752383/19807040628566084398385987584)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472144003920393/618970019642690137449562112), (351102658643/309485009821345068724781056)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221280293791569/19342813113834066795298816), (2807988457307/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548664449902867/9671406556917033397649408), (328950578179/1208925819614629174706176)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629005460331737/302231454903657293676544), (1150884920953/302231454903657293676544)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886528350135121/75557863725914323419136), (3738718847173/75557863725914323419136)), (4609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296591830664127/4722366482869645213696), (175161866967/295147905179352825856)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620145374541233/590295810358705651712), (1925603701971/295147905179352825856)), (1189/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227730819313799/9223372036854775808), (4810481172461/73786976294838206464)), (1487/18446744073709551616), by norm_num⟩
  | 7 => ⟨((14225201604591/72057594037927936), (5406944138039/9223372036854775808)), (3347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592074911680195/1152921504606846976), (5400891055927/1152921504606846976)), (3349/576460752303423488), by norm_num⟩
  | 5 => ⟨((596454679593003/72057594037927936), (4718978053643/144115188075855872)), (2933/72057594037927936), by norm_num⟩
  | 4 => ⟨((93070728368205/2251799813685248), (7064884060639/36028797018963968)), (8809/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486127882390039/9007199254740992), (4403690113759/4503599627370496)), (11029/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110847841310437/2251799813685248), (17543767354603/4503599627370496)), (22109/4503599627370496), by norm_num⟩
  | 1 => ⟨((551685817236691/562949953421312), (26138801982235/2251799813685248)), (33297/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162085400094843/2251799813685248), (25786999578769/1125899906842624)), (67125/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162085400094843/2251799813685248), (25786999578769/1125899906842624)), (256061562545012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((259345511728025/281474976710656), (6189903623167/140737488355328)), (131977/2251799813685248), by norm_num⟩
  | 2 => ⟨((476822740054777/562949953421312), (2851627774265/35184372088832)), (63703/562949953421312), by norm_num⟩
  | 3 => ⟨((1600697810792637/2251799813685248), (154582377142713/1125899906842624)), (3695/17592186044416), by norm_num⟩
  | 4 => ⟨((1095412931999095/2251799813685248), (219770577451561/1125899906842624)), (802283/2251799813685248), by norm_num⟩
  | 5 => ⟨((55884911406139/281474976710656), (855278630543483/4503599627370496)), (2187527/4503599627370496), by norm_num⟩
  | 6 => ⟨((7551518831461/2251799813685248), (1358477291418195/18014398509481984)), (3399007/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-3111214733/33554432)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2819539303/1073741824), (-101180342683/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1303611956049983/18014398509481984), (21175596455033/18014398509481984)), (1286109/9007199254740992), by norm_num⟩
  | 1 => ⟨((-60560239415/274877906944), (-245931925/68719476736)), (241/549755813888), by norm_num⟩
  | 2 => ⟨((92188503867/274877906944), (46796579/8589934592)), (185/274877906944), by norm_num⟩
  | 3 => ⟨((-93556656175/274877906944), (-189964313/34359738368)), (95/137438953472), by norm_num⟩
  | 4 => ⟨((71208834731/274877906944), (1156701227/274877906944)), (73/137438953472), by norm_num⟩
  | 5 => ⟨((-86718758041/549755813888), (-88040071/34359738368)), (45/137438953472), by norm_num⟩
  | 6 => ⟨((22001433719/274877906944), (1429546515/1099511627776)), (23/137438953472), by norm_num⟩
  | 7 => ⟨((-2392280665/68719476736), (-310877603/549755813888)), (81/1099511627776), by norm_num⟩
  | 8 => ⟨((116533634591/8796093022208), (1892947675/8796093022208)), (249/8796093022208), by norm_num⟩
  | 9 => ⟨((-78842058947/17592186044416), (-160086713/2199023255552)), (85/8796093022208), by norm_num⟩
  | 10 => ⟨((12001820875/8796093022208), (1559640287/70368744177664)), (209/70368744177664), by norm_num⟩
  | 11 => ⟨((-53148818833/140737488355328), (-1726676309/281474976710656)), (117/140737488355328), by norm_num⟩
  | 12 => ⟨((13484397623/140737488355328), (438075397/281474976710656)), (15/70368744177664), by norm_num⟩
  | 13 => ⟨((-101054895071/4503599627370496), (-410378577/1125899906842624)), (227/4503599627370496), by norm_num⟩
  | 14 => ⟨((87903970139/18014398509481984), (1427893469/18014398509481984)), (199/18014398509481984), by norm_num⟩
  | 15 => ⟨((-17841707297/18014398509481984), (-1159267655/72057594037927936)), (163/72057594037927936), by norm_num⟩
  | 16 => ⟨((54319478193/288230376151711744), (1764708193/576460752303423488)), (251/576460752303423488), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (1322342935/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777919631258161/633825300114114700748351602688), (25016005105/633825300114114700748351602688)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888786814745157/39614081257132168796771975168), (28136641211/39614081257132168796771975168)), (1621/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236062813970263/309485009821345068724781056), (7471794627/618970019642690137449562112)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770169113656029/154742504910672534362390528), (1867386249/9671406556917033397649408)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548596074249191/9671406556917033397649408), (28001236639/9671406556917033397649408)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78621960965931/37778931862957161709568), (24491529279/604462909807314587353088)), (1413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886432120197663/75557863725914323419136), (39780832785/75557863725914323419136)), (287/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296520122345385/4722366482869645213696), (29819969245/4722366482869645213696)), (861/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202505941107347/73786976294838206464), (40977034945/590295810358705651712)), (4735/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910862687804229/36893488147419103232), (51183189553/73786976294838206464)), (5919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455172756917181/2305843009213693952), (57528743811/9223372036854775808)), (6659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591942065553159/1152921504606846976), (57463386299/1152921504606846976)), (6659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192795286251159/144115188075855872), (50207036107/144115188075855872)), (5827/144115188075855872), by norm_num⟩
  | 4 => ⟨((372241216333495/9007199254740992), (75163950721/36028797018963968)), (8741/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485926926733851/9007199254740992), (93698944683/9007199254740992)), (10925/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110658118035331/2251799813685248), (186632152309/4503599627370496)), (21851/4503599627370496), by norm_num⟩
  | 1 => ⟨((551557456009447/562949953421312), (278041717195/2251799813685248)), (32779/2251799813685248), by norm_num⟩
  | 0 => ⟨((135079925131569/140737488355328), (548504194357/2251799813685248)), (16393/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((135079925131569/140737488355328), (548504194357/2251799813685248)), (62534334422874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2074396547678613/2251799813685248), (263227326187/562949953421312)), (125905/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910969128894521/2251799813685248), (969958081315/1125899906842624)), (232091/2251799813685248), by norm_num⟩
  | 3 => ⟨((1621724642714447/2251799813685248), (1646291946957/1125899906842624)), (394325/2251799813685248), by norm_num⟩
  | 4 => ⟨((1167945729320597/2251799813685248), (4742574723129/2251799813685248)), (142283/562949953421312), by norm_num⟩
  | 5 => ⟨((302885435537629/1125899906842624), (4919682344939/2251799813685248)), (1185567/4503599627370496), by norm_num⟩
  | 6 => ⟨((1303611956049983/18014398509481984), (21175596455033/18014398509481984)), (1286109/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-101180342683/1073741824)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨59,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile059Terms2
