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
namespace Reinmann.XiBand97.Tile065Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨65,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (81383/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (81383/2560))
  have he : value ((69/80), (81383/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/1073741824), (-1478764711/16777216)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((811380453979229/9007199254740992), (-144840931288307/9007199254740992)), (1883329/9007199254740992), by norm_num⟩
  | 1 => ⟨((-68653085209/274877906944), (3063845311/68719476736)), (161/274877906944), by norm_num⟩
  | 2 => ⟨((47586692449/137438953472), (-2123695739/34359738368)), (225/274877906944), by norm_num⟩
  | 3 => ⟨((-43979442271/137438953472), (3925423237/68719476736)), (105/137438953472), by norm_num⟩
  | 4 => ⟨((60968452825/274877906944), (-10883584197/274877906944)), (147/274877906944), by norm_num⟩
  | 5 => ⟨((-33808088943/274877906944), (12070281121/549755813888)), (165/549755813888), by norm_num⟩
  | 6 => ⟨((7811327177/137438953472), (-11155308437/1099511627776)), (77/549755813888), by norm_num⟩
  | 7 => ⟨((-99006160625/4398046511104), (2209220169/549755813888)), (123/2199023255552), by norm_num⟩
  | 8 => ⟨((68625841095/8796093022208), (-12250517851/8796093022208)), (43/2199023255552), by norm_num⟩
  | 9 => ⟨((-84564992477/35184372088832), (15095843393/35184372088832)), (107/17592186044416), by norm_num⟩
  | 10 => ⟨((93785577775/140737488355328), (-8370913029/70368744177664)), (239/140737488355328), by norm_num⟩
  | 11 => ⟨((-47277970045/281474976710656), (8439672385/281474976710656)), (243/562949953421312), by norm_num⟩
  | 12 => ⟨((87388244371/2251799813685248), (-15599826983/2251799813685248)), (227/2251799813685248), by norm_num⟩
  | 13 => ⟨((-37275640123/4503599627370496), (13308278265/9007199254740992)), (195/9007199254740992), by norm_num⟩
  | 14 => ⟨((29528576977/18014398509481984), (-10542394923/36028797018963968)), (39/9007199254740992), by norm_num⟩
  | 15 => ⟨((-87328639477/288230376151711744), (7794593405/144115188075855872)), (233/288230376151711744), by norm_num⟩
  | 16 => ⟨((60531600235/1152921504606846976), (-10805600885/1152921504606846976)), (41/288230376151711744), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (-230107657231/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889140448924965/316912650057057350374175801344), (-136089048693/316912650057057350374175801344)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889193149422687/39614081257132168796771975168), (-306136945909/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944467064519067/1237940039285380274899124224), (-325191196841/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770600603511665/154742504910672534362390528), (-81275503863/38685626227668133590597632)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549000460657805/9671406556917033397649408), (-304688418823/9671406556917033397649408)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258305078291185/604462909807314587353088), (-133253842353/302231454903657293676544)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887006633800043/75557863725914323419136), (-54112192745/9444732965739290427392)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648475392927915/2361183241434822606848), (-81129493517/1180591620717411303424)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405159832793759/147573952589676412928), (-55745024709/73786976294838206464)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822464588903759/73786976294838206464), (-4352128849/576460752303423488)), (2961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821521901351117/9223372036854775808), (-626187581279/9223372036854775808)), (6663/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398193003413451/288230376151711744), (-625539523451/1152921504606846976)), (6663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596760225474633/72057594037927936), (-546618922235/144115188075855872)), (5831/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490050536069953/36028797018963968), (-818474319407/36028797018963968)), (2187/9007199254740992), by norm_num⟩
  | 3 => ⟨((185910048675001/1125899906842624), (-1020553358623/9007199254740992)), (1367/1125899906842624), by norm_num⟩
  | 2 => ⟨((2224012315235449/4503599627370496), (-508377084635/1125899906842624)), (10939/2251799813685248), by norm_num⟩
  | 1 => ⟨((138140433492759/140737488355328), (-3031337224221/2251799813685248)), (32833/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169205646824201/2251799813685248), (-2993697896417/1125899906842624)), (32867/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169205646824201/2251799813685248), (-2993697896417/1125899906842624)), (125377659324264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((522406261505639/562949953421312), (-11535566069997/2251799813685248)), (126997/2251799813685248), by norm_num⟩
  | 2 => ⟨((969535510471123/1125899906842624), (-21409547716823/2251799813685248)), (237003/2251799813685248), by norm_num⟩
  | 3 => ⟨((1669570284479145/2251799813685248), (-36872401620133/2251799813685248)), (103171/562949953421312), by norm_num⟩
  | 4 => ⟨((1237279328243151/2251799813685248), (-54677210370317/2251799813685248)), (625475/2251799813685248), by norm_num⟩
  | 5 => ⟨((678510820312869/2251799813685248), (-15021535597003/562949953421312)), (1435451/4503599627370496), by norm_num⟩
  | 6 => ⟨((811380453979229/9007199254740992), (-144840931288307/9007199254740992)), (1883329/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-1478764711/16777216)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-655961365/268435456), (-48355166457/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-198772310275457/4503599627370496), (-1347327170658659/18014398509481984)), (2202827/4503599627370496), by norm_num⟩
  | 1 => ⟨((34372824823/274877906944), (29123423147/137438953472)), (383/274877906944), by norm_num⟩
  | 2 => ⟨((-12173193245/68719476736), (-20628217771/68719476736)), (545/274877906944), by norm_num⟩
  | 3 => ⟨((11496417847/68719476736), (38962761235/137438953472)), (517/274877906944), by norm_num⟩
  | 4 => ⟨((-32571804453/274877906944), (-27597453763/137438953472)), (23/17179869184), by norm_num⟩
  | 5 => ⟨((18456574203/274877906944), (31275789705/274877906944)), (419/549755813888), by norm_num⟩
  | 6 => ⟨((-34860941545/1099511627776), (-59073989825/1099511627776)), (397/1099511627776), by norm_num⟩
  | 7 => ⟨((28219567077/2199023255552), (23909888037/1099511627776)), (323/2199023255552), by norm_num⟩
  | 8 => ⟨((-39976027003/8796093022208), (-67741813841/8796093022208)), (459/8796093022208), by norm_num⟩
  | 9 => ⟨((50338050287/35184372088832), (5331305859/2199023255552)), (145/8796093022208), by norm_num⟩
  | 10 => ⟨((-28523687157/70368744177664), (-48335126083/70368744177664)), (165/35184372088832), by norm_num⟩
  | 11 => ⟨((14693398377/140737488355328), (12449429473/70368744177664)), (171/140737488355328), by norm_num⟩
  | 12 => ⟨((-27753021567/1125899906842624), (-23514593139/562949953421312)), (325/1125899906842624), by norm_num⟩
  | 13 => ⟨((48387834487/9007199254740992), (81996134229/9007199254740992)), (569/9007199254740992), by norm_num⟩
  | 14 => ⟨((-39169445245/36028797018963968), (-33187505951/18014398509481984)), (231/18014398509481984), by norm_num⟩
  | 15 => ⟨((7398359663/36028797018963968), (25073942591/72057594037927936)), (351/144115188075855872), by norm_num⟩
  | 16 => ⟨((-20961131321/576460752303423488), (-71039828737/1152921504606846976)), (125/288230376151711744), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-2740593232091/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778194745393745/633825300114114700748351602688), (-810343576185/158456325028528675187087900672)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472273984364309/9903520314283042199192993792), (-3645763834935/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888830454923195/2475880078570760549798248448), (-3872657649571/2475880078570760549798248448)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885248247576359/77371252455336267181195264), (-120986585399/4835703278458516698824704)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774451199021829/4835703278458516698824704), (-453555379893/1208925819614629174706176)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78638675804849/37778931862957161709568), (-3173733503269/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235858198710151/9444732965739290427392), (-1288788419939/18889465931478580854784)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296844248649487/4722366482869645213696), (-966118295975/1180591620717411303424)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1582511346359/576460752303423488), (-5310577465277/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911139057648679/36893488147419103232), (-3316807321717/36893488147419103232)), (2979/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910654801364469/4611686018427387904), (-7456485741951/9223372036854775808)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398139144261735/288230376151711744), (-3724289276317/576460752303423488)), (3357/576460752303423488), by norm_num⟩
  | 5 => ⟨((596664211499611/72057594037927936), (-813577400281/18014398509481984)), (5881/144115188075855872), by norm_num⟩
  | 4 => ⟨((372438868887057/9007199254740992), (-4872588060979/18014398509481984)), (8835/36028797018963968), by norm_num⟩
  | 3 => ⟨((185862416672381/1125899906842624), (-189850797481/140737488355328)), (11069/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223213720200279/4503599627370496), (-24208036907019/4503599627370496)), (347/70368744177664), by norm_num⟩
  | 1 => ⟨((2208958561602687/2251799813685248), (-36080564377307/2251799813685248)), (16747/1125899906842624), by norm_num⟩
  | 0 => ⟨((2166271304793669/2251799813685248), (-8904898904381/281474976710656)), (8465/281474976710656), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166271304793669/2251799813685248), (-8904898904381/281474976710656)), (32291413427257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2081737601680019/2251799813685248), (-34266681880711/562949953421312)), (134581/2251799813685248), by norm_num⟩
  | 2 => ⟨((958087865588965/1125899906842624), (-253430130768647/2251799813685248)), (265219/2251799813685248), by norm_num⟩
  | 3 => ⟨((1602052979864981/2251799813685248), (-215657121550863/1125899906842624)), (511077/2251799813685248), by norm_num⟩
  | 4 => ⟨((1057172915427107/2251799813685248), (-306860434138003/1125899906842624)), (923003/2251799813685248), by norm_num⟩
  | 5 => ⟨((82263226114953/562949953421312), (-576258222982951/2251799813685248)), (2739569/4503599627370496), by norm_num⟩
  | 6 => ⟨((-198772310275457/4503599627370496), (-1347327170658659/18014398509481984)), (2202827/4503599627370496), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-48355166457/536870912)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-98661407035/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1059297438487633/18014398509481984), (1046683509539165/18014398509481984)), (8523159/18014398509481984), by norm_num⟩
  | 1 => ⟨((46718801871/274877906944), (-46162482535/274877906944)), (189/137438953472), by norm_num⟩
  | 2 => ⟨((-33758676373/137438953472), (66713367897/274877906944)), (549/274877906944), by norm_num⟩
  | 3 => ⟨((32525041591/137438953472), (-16068869537/68719476736)), (531/274877906944), by norm_num⟩
  | 4 => ⟨((-11751182705/68719476736), (46445006691/274877906944)), (193/137438953472), by norm_num⟩
  | 5 => ⟨((13586114645/137438953472), (-26848667127/274877906944)), (7/8589934592), by norm_num⟩
  | 6 => ⟨((-52358562759/1099511627776), (25867543067/549755813888)), (217/549755813888), by norm_num⟩
  | 7 => ⟨((43238774595/2199023255552), (-1335121713/68719476736)), (45/274877906944), by norm_num⟩
  | 8 => ⟨((-15622016617/2199023255552), (30871984741/4398046511104)), (261/4398046511104), by norm_num⟩
  | 9 => ⟨((10034096807/4398046511104), (-4957306267/2199023255552)), (337/17592186044416), by norm_num⟩
  | 10 => ⟨((-46403632043/70368744177664), (22925532847/35184372088832)), (49/8796093022208), by norm_num⟩
  | 11 => ⟨((24386135913/140737488355328), (-1505984379/8796093022208)), (207/140737488355328), by norm_num⟩
  | 12 => ⟨((-23494999509/562949953421312), (23215225157/562949953421312)), (401/1125899906842624), by norm_num⟩
  | 13 => ⟨((10447582005/1125899906842624), (-41292696091/4503599627370496)), (359/4503599627370496), by norm_num⟩
  | 14 => ⟨((-34511309675/18014398509481984), (68200710051/36028797018963968)), (595/36028797018963968), by norm_num⟩
  | 15 => ⟨((53200274567/144115188075855872), (-52566774987/144115188075855872)), (115/36028797018963968), by norm_num⟩
  | 16 => ⟨((-9610535695/144115188075855872), (37984380457/576460752303423488)), (167/288230376151711744), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (769252097417/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778117329299931/633825300114114700748351602688), (3638965402861/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889008782407619/39614081257132168796771975168), (1023234509137/9903520314283042199192993792)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944368884010661/1237940039285380274899124224), (1086909872017/618970019642690137449562112)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770403713127649/154742504910672534362390528), (4346394231507/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548815313922287/9671406556917033397649408), (4073421862463/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258142513405987/604462909807314587353088), (3562921799683/604462909807314587353088)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886741414145475/75557863725914323419136), (5787269404877/75557863725914323419136)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324187737985791/1180591620717411303424), (4338284198015/4722366482869645213696)), (1733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810181533957049/295147905179352825856), (2980809799297/295147905179352825856)), (4767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822117025918003/73786976294838206464), (3723372761475/36893488147419103232)), (5963/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821127827107647/9223372036854775808), (8370334647667/9223372036854775808)), (3357/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398093528913843/288230376151711744), (522579615787/72057594037927936)), (105/18014398509481984), by norm_num⟩
  | 5 => ⟨((2330406250555/281474976710656), (3652965278457/72057594037927936)), (23/562949953421312), by norm_num⟩
  | 4 => ⟨((1489513309704871/36028797018963968), (10938551027743/36028797018963968)), (8847/36028797018963968), by norm_num⟩
  | 3 => ⟨((92912122465597/562949953421312), (6818818913965/4503599627370496)), (5543/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111297514103027/2251799813685248), (13584416268883/2251799813685248)), (22253/4503599627370496), by norm_num⟩
  | 1 => ⟨((276001357209469/281474976710656), (40487874805991/2251799813685248)), (33583/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164298394102373/2251799813685248), (79918653634769/2251799813685248)), (67989/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164298394102373/2251799813685248), (79918653634769/2251799813685248)), (259357460982512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2077360748982267/2251799813685248), (38406569862327/562949953421312)), (135521/2251799813685248), by norm_num⟩
  | 2 => ⟨((1905953904779313/2251799813685248), (283450776574921/2251799813685248)), (134269/1125899906842624), by norm_num⟩
  | 3 => ⟨((1577545180887523/2251799813685248), (479833163802911/2251799813685248)), (522195/2251799813685248), by norm_num⟩
  | 4 => ⟨((250733759605419/562949953421312), (672314200034037/2251799813685248)), (477109/1125899906842624), by norm_num⟩
  | 5 => ⟨((61492178874021/562949953421312), (598887577789653/2251799813685248)), (1419801/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1059297438487633/18014398509481984), (1046683509539165/18014398509481984)), (8523159/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-98661407035/1073741824)), (1/536870912), by norm_num⟩, -15, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-2726851779/1073741824), (-25126741207/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1137171723735365/18014398509481984), (213163399559259/4503599627370496)), (1164397/4503599627370496), by norm_num⟩
  | 1 => ⟨((-25545751567/137438953472), (-2394281855/17179869184)), (211/274877906944), by norm_num⟩
  | 2 => ⟨((37608953333/137438953472), (7049816821/34359738368)), (313/274877906944), by norm_num⟩
  | 3 => ⟨((-576756605/2147483648), (-55354014517/274877906944)), (309/274877906944), by norm_num⟩
  | 4 => ⟨((6792898517/34359738368), (40746629499/274877906944)), (115/137438953472), by norm_num⟩
  | 5 => ⟨((-4000255035/34359738368), (-47990385667/549755813888)), (273/549755813888), by norm_num⟩
  | 6 => ⟨((62818703209/1099511627776), (47101587395/1099511627776)), (135/549755813888), by norm_num⟩
  | 7 => ⟨((-26423691193/1099511627776), (-19812535701/1099511627776)), (229/2199023255552), by norm_num⟩
  | 8 => ⟨((38901473161/4398046511104), (29168401197/4398046511104)), (85/2199023255552), by norm_num⟩
  | 9 => ⟨((-12727001547/4398046511104), (-38170923309/17592186044416)), (7/549755813888), by norm_num⟩
  | 10 => ⟨((59958207109/70368744177664), (44956781785/70368744177664)), (133/35184372088832), by norm_num⟩
  | 11 => ⟨((-64197557139/281474976710656), (-12033863697/70368744177664)), (287/281474976710656), by norm_num⟩
  | 12 => ⟨((7876074567/140737488355328), (23621984893/562949953421312)), (283/1125899906842624), by norm_num⟩
  | 13 => ⟨((-57084605435/4503599627370496), (-21401074795/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | 14 => ⟨((48023467815/18014398509481984), (9002022689/4503599627370496)), (219/18014398509481984), by norm_num⟩
  | 15 => ⟨((-4713405685/9007199254740992), (-14136483465/36028797018963968)), (173/72057594037927936), by norm_num⟩
  | 16 => ⟨((27756670847/288230376151711744), (41624012943/576460752303423488)), (257/576460752303423488), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (838066933495/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778052065101547/633825300114114700748351602688), (30970236737/19807040628566084398385987584)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888935740540679/39614081257132168796771975168), (1114683849009/39614081257132168796771975168)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944330332498955/1237940039285380274899124224), (296011228215/618970019642690137449562112)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885163588244695/77371252455336267181195264), (295925016197/38685626227668133590597632)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548744162158399/9671406556917033397649408), (1109352548825/9671406556917033397649408)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258080856440915/604462909807314587353088), (60644835933/37778931862957161709568)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886642347055471/75557863725914323419136), (1576079619485/75557863725914323419136)), (4599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296677635345011/4722366482869645213696), (73841231041/295147905179352825856)), (1725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620263854123265/590295810358705651712), (811766338351/295147905179352825856)), (593/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910997699979315/36893488147419103232), (2027955326013/73786976294838206464)), (5931/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455248570050289/2305843009213693952), (2279443295807/9223372036854775808)), (3337/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592244663065295/1152921504606846976), (2276937889065/1152921504606846976)), (6675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298264830906741/36028797018963968), (497376427721/36028797018963968)), (5843/144115188075855872), by norm_num⟩
  | 4 => ⟨((372339863530615/9007199254740992), (2978637771035/36028797018963968)), (137/562949953421312), by norm_num⟩
  | 3 => ⟨((743208801556271/4503599627370496), (3713481237409/9007199254740992)), (1371/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111144971205951/2251799813685248), (3698798017649/2251799813685248)), (10979/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207671380501805/2251799813685248), (11023262396037/2251799813685248)), (32993/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164086577420063/2251799813685248), (21755698657007/2251799813685248)), (66215/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164086577420063/2251799813685248), (21755698657007/2251799813685248)), (252590188033293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519894949773739/562949953421312), (41816519532411/2251799813685248)), (16069/281474976710656), by norm_num⟩
  | 2 => ⟨((1919754808231927/2251799813685248), (38618348202873/1125899906842624)), (30277/281474976710656), by norm_num⟩
  | 3 => ⟨((1634023146327625/2251799813685248), (131695116409319/2251799813685248)), (26851/140737488355328), by norm_num⟩
  | 4 => ⟨((1178030135239701/2251799813685248), (23891207731179/281474976710656)), (168439/562949953421312), by norm_num⟩
  | 5 => ⟨((600064199171775/2251799813685248), (199979145595823/2251799813685248)), (819327/2251799813685248), by norm_num⟩
  | 6 => ⟨((1137171723735365/18014398509481984), (213163399559259/4503599627370496)), (1164397/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-25126741207/268435456)), (1/536870912), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-1387177309/536870912), (-102257836003/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((93655149819227/2251799813685248), (-567394881373405/9007199254740992)), (2723699/9007199254740992), by norm_num⟩
  | 1 => ⟨((-34248749377/274877906944), (6484081871/34359738368)), (251/274877906944), by norm_num⟩
  | 2 => ⟨((51300041919/274877906944), (-77698293301/274877906944)), (189/137438953472), by norm_num⟩
  | 3 => ⟨((-51227063737/274877906944), (38793880807/137438953472)), (379/274877906944), by norm_num⟩
  | 4 => ⟨((38365642029/274877906944), (-58108040375/274877906944)), (285/274877906944), by norm_num⟩
  | 5 => ⟨((-45973276809/549755813888), (34815226381/274877906944)), (43/68719476736), by norm_num⟩
  | 6 => ⟨((45907876353/1099511627776), (-69531398187/1099511627776)), (173/549755813888), by norm_num⟩
  | 7 => ⟨((-39293630515/2199023255552), (14878389541/549755813888)), (149/1099511627776), by norm_num⟩
  | 8 => ⟨((14714149635/2199023255552), (-44571671727/4398046511104)), (225/4398046511104), by norm_num⟩
  | 9 => ⟨((-9795478431/4398046511104), (29672176773/8796093022208)), (301/17592186044416), by norm_num⟩
  | 10 => ⟨((46951409393/70368744177664), (-17777979517/17592186044416)), (363/70368744177664), by norm_num⟩
  | 11 => ⟨((-51146855421/281474976710656), (77466279269/281474976710656)), (199/140737488355328), by norm_num⟩
  | 12 => ⟨((51074095159/1125899906842624), (-9669509705/140737488355328)), (25/70368744177664), by norm_num⟩
  | 13 => ⟨((-23539125417/2251799813685248), (71304030259/4503599627370496)), (185/2251799813685248), by norm_num⟩
  | 14 => ⟨((40295381545/18014398509481984), (-61030795623/18014398509481984)), (319/18014398509481984), by norm_num⟩
  | 15 => ⟨((-32190446659/72057594037927936), (6094397471/9007199254740992)), (257/72057594037927936), by norm_num⟩
  | 16 => ⟨((24108489989/288230376151711744), (-73028732767/576460752303423488)), (387/576460752303423488), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (-1286005297131/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777983206708447/633825300114114700748351602688), (-760320718383/316912650057057350374175801344)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888858252673685/39614081257132168796771975168), (-53448105267/1237940039285380274899124224)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888578303123429/2475880078570760549798248448), (-1816756760687/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770244779778409/154742504910672534362390528), (-908109169455/77371252455336267181195264)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193583359783517/1208925819614629174706176), (-1702132834577/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258013196108345/604462909807314587353088), (-1488794614041/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1886532329869757/75557863725914323419136), (-302277497661/9444732965739290427392)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296595062049325/4722366482869645213696), (-226591017669/590295810358705651712)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620150217860595/590295810358705651712), (-2490979784279/590295810358705651712)), (1187/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910926603986013/36893488147419103232), (-3111444298295/73786976294838206464)), (5937/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820834113069649/9223372036854775808), (-874310493579/2305843009213693952)), (6681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592084245262121/1152921504606846976), (-3493329993139/1152921504606846976)), (6685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298229669272167/36028797018963968), (-95383387193/4503599627370496)), (1463/36028797018963968), by norm_num⟩
  | 4 => ⟨((744573962500329/18014398509481984), (-4569625921615/36028797018963968)), (549/2251799813685248), by norm_num⟩
  | 3 => ⟨((1486152218758487/9007199254740992), (-712088098595/1125899906842624)), (687/562949953421312), by norm_num⟩
  | 2 => ⟨((2221756278158369/4503599627370496), (-11347552676357/4503599627370496)), (22017/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103431863234519/1125899906842624), (-8453563203195/1125899906842624)), (4139/281474976710656), by norm_num⟩
  | 0 => ⟨((2162443123031319/2251799813685248), (-33360071147071/2251799813685248)), (66569/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162443123031319/2251799813685248), (-33360071147071/2251799813685248)), (253940590865325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2076138090777893/2251799813685248), (-16018132694877/562949953421312)), (32457/562949953421312), by norm_num⟩
  | 2 => ⟨((59761141629455/70368744177664), (-118148532489815/2251799813685248)), (246789/2251799813685248), by norm_num⟩
  | 3 => ⟨((1617882907777899/2251799813685248), (-50169228298359/562949953421312)), (445073/2251799813685248), by norm_num⟩
  | 4 => ⟨((1144539520843601/2251799813685248), (-144183219959477/1125899906842624)), (718885/2251799813685248), by norm_num⟩
  | 5 => ⟨((1089631061913615/4503599627370496), (-586280867360171/4503599627370496)), (1829817/4503599627370496), by norm_num⟩
  | 6 => ⟨((93655149819227/2251799813685248), (-567394881373405/9007199254740992)), (2723699/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-102257836003/1073741824)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-2819539303/1073741824), (-103923264069/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-536815593622549/9007199254740992), (-369854231967241/9007199254740992)), (930689/2251799813685248), by norm_num⟩
  | 1 => ⟨((49876315909/274877906944), (34363693479/274877906944)), (347/274877906944), by norm_num⟩
  | 2 => ⟨((-9490597681/34359738368), (-1634703685/8589934592)), (265/137438953472), by norm_num⟩
  | 3 => ⟨((77051566899/274877906944), (103685251/536870912)), (135/68719476736), by norm_num⟩
  | 4 => ⟨((-7330788259/34359738368), (-40406025361/274877906944)), (413/274877906944), by norm_num⟩
  | 5 => ⟨((71419997891/549755813888), (12301705083/137438953472)), (253/274877906944), by norm_num⟩
  | 6 => ⟨((-36239964347/549755813888), (-24968544765/549755813888)), (515/1099511627776), by norm_num⟩
  | 7 => ⟨((63047648341/2199023255552), (43438454157/2199023255552)), (225/1099511627776), by norm_num⟩
  | 8 => ⟨((-47987495005/4398046511104), (-33062337085/4398046511104)), (43/549755813888), by norm_num⟩
  | 9 => ⟨((64932891233/17592186044416), (44737345377/17592186044416)), (117/4398046511104), by norm_num⟩
  | 10 => ⟨((-39537928861/35184372088832), (-27240770361/35184372088832)), (143/17592186044416), by norm_num⟩
  | 11 => ⟨((43772404203/140737488355328), (15079115743/70368744177664)), (319/140737488355328), by norm_num⟩
  | 12 => ⟨((-22211011125/281474976710656), (-30605804147/562949953421312)), (325/562949953421312), by norm_num⟩
  | 13 => ⟨((20806745149/1125899906842624), (7167696727/562949953421312)), (153/1125899906842624), by norm_num⟩
  | 14 => ⟨((-18099029275/4503599627370496), (-49879345171/18014398509481984)), (267/9007199254740992), by norm_num⟩
  | 15 => ⟨((14694106861/18014398509481984), (40495676147/72057594037927936)), (109/18014398509481984), by norm_num⟩
  | 16 => ⟨((-44736538041/288230376151711744), (-30822498665/288230376151711744)), (333/288230376151711744), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (-826605520069/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888955717799515/316912650057057350374175801344), (-3909418533347/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236097143181213/4951760157141521099596496896), (-1099270226645/9903520314283042199192993792)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888491637472325/2475880078570760549798248448), (-4670645484279/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770157564369225/154742504910672534362390528), (-4669236247043/154742504910672534362390528)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548584530186409/9671406556917033397649408), (-2187956041883/4835703278458516698824704)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257940558444047/604462909807314587353088), (-3827426643773/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886413201519037/75557863725914323419136), (-3108381742947/37778931862957161709568)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296504761310205/4722366482869645213696), (-4660119400515/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620024505478601/590295810358705651712), (-6403679568699/590295810358705651712)), (2385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821693747968673/73786976294838206464), (-3999312907429/36893488147419103232)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820651537341559/9223372036854775808), (-8990245582735/9223372036854775808)), (3359/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591897699677199/1152921504606846976), (-4489996482263/576460752303423488)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192750996207013/144115188075855872), (-1961492646449/36028797018963968)), (5893/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488887528115085/36028797018963968), (-367060521909/1125899906842624)), (8855/36028797018963968), by norm_num⟩
  | 3 => ⟨((742905630482477/4503599627370496), (-14642198814889/9007199254740992)), (5549/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221028258903039/4503599627370496), (-29163977377811/4503599627370496)), (22283/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205657419674043/2251799813685248), (-43445775902629/2251799813685248)), (33645/2251799813685248), by norm_num⟩
  | 0 => ⟨((67486851766175/70368744177664), (-85695951506545/2251799813685248)), (68173/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((67486851766175/70368744177664), (-85695951506545/2251799813685248)), (260059365279387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((516968553418595/562949953421312), (-20546586570033/281474976710656)), (8497/140737488355328), by norm_num⟩
  | 2 => ⟨((1886972969664635/2251799813685248), (-301893667733563/2251799813685248)), (33693/281474976710656), by norm_num⟩
  | 3 => ⟨((385194898380997/562949953421312), (-252982164428661/1125899906842624)), (524023/2251799813685248), by norm_num⟩
  | 4 => ⟨((940581769690099/2251799813685248), (-173101424961613/562949953421312)), (952609/2251799813685248), by norm_num⟩
  | 5 => ⟨((359950657985223/4503599627370496), (-1156877577743897/4503599627370496)), (2763299/4503599627370496), by norm_num⟩
  | 6 => ⟨((-536815593622549/9007199254740992), (-369854231967241/9007199254740992)), (930689/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-103923264069/1073741824)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨65,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile065Terms2
