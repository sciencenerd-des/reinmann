/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile057Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨57,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78519/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78519/2560))
  have he : value ((69/80), (78519/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-320962607/134217728), (-22827593251/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1609964030758773/18014398509481984), (176977661463599/9007199254740992)), (35478523/18014398509481984), by norm_num⟩
  | 1 => ⟨((17027924023/68719476736), (-935909783/17179869184)), (377/68719476736), by norm_num⟩
  | 2 => ⟨((-23605715055/68719476736), (5189785819/68719476736)), (525/68719476736), by norm_num⟩
  | 3 => ⟨((10908156557/34359738368), (-37471723/536870912)), (487/68719476736), by norm_num⟩
  | 4 => ⟨((-15121915925/68719476736), (3324597651/68719476736)), (339/68719476736), by norm_num⟩
  | 5 => ⟨((16770741421/137438953472), (-3687096781/137438953472)), (189/68719476736), by norm_num⟩
  | 6 => ⟨((-968716011/17179869184), (425950123/34359738368)), (351/274877906944), by norm_num⟩
  | 7 => ⟨((24556352797/1099511627776), (-5398786319/1099511627776)), (279/549755813888), by norm_num⟩
  | 8 => ⟨((-8510583353/1099511627776), (935538379/549755813888)), (389/2199023255552), by norm_num⟩
  | 9 => ⟨((5243632761/2199023255552), (-2305656141/4398046511104)), (241/4398046511104), by norm_num⟩
  | 10 => ⟨((-23261499291/35184372088832), (5114108971/35184372088832)), (537/35184372088832), by norm_num⟩
  | 11 => ⟨((11726285563/70368744177664), (-5156116675/140737488355328)), (17/4398046511104), by norm_num⟩
  | 12 => ⟨((-21674778071/562949953421312), (148914489/17592186044416)), (505/562949953421312), by norm_num⟩
  | 13 => ⟨((18490844689/2251799813685248), (-2032633269/1125899906842624)), (433/2251799813685248), by norm_num⟩
  | 14 => ⟨((-1830982409/1125899906842624), (1610187451/4503599627370496)), (345/9007199254740992), by norm_num⟩
  | 15 => ⟨((21659994359/72057594037927936), (-4762013405/72057594037927936)), (1/140737488355328), by norm_num⟩
  | 16 => ⟨((-15013564021/288230376151711744), (1650388083/144115188075855872)), (357/288230376151711744), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (952594241957/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889135026367209/316912650057057350374175801344), (4507025823951/633825300114114700748351602688)), (11581/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889180346828067/39614081257132168796771975168), (1267330749553/9903520314283042199192993792)), (1629/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((29514370790653/38685626227668133590597632), (5384838829789/2475880078570760549798248448)), (13851/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770585310779183/154742504910672534362390528), (5383357519933/154742504910672534362390528)), (433/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548985174229835/9671406556917033397649408), (5045324076083/9671406556917033397649408)), (12995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629145376980529/302231454903657293676544), (1103271324123/151115727451828646838272)), (11375/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943490789804501/37778931862957161709568), (7168314424369/75557863725914323419136)), (9247/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648465220934883/2361183241434822606848), (2686827991493/2361183241434822606848)), (13879/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620608837136495/590295810358705651712), (7384586056287/590295810358705651712)), (2387/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455605673808047/18446744073709551616), (2306112121869/18446744073709551616)), (11945/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821469587670309/9223372036854775808), (10368867670929/9223372036854775808)), (26903/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398178308534317/288230376151711744), (10358077183841/1152921504606846976)), (26937/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298365440764227/36028797018963968), (9051185959479/144115188075855872)), (2951/18014398509481984), by norm_num⟩
  | 4 => ⟨((744974019077425/18014398509481984), (13552535114837/36028797018963968)), (35489/36028797018963968), by norm_num⟩
  | 3 => ⟨((46472720427373/281474976710656), (16898285756547/9007199254740992)), (2781/562949953421312), by norm_num⟩
  | 2 => ⟨((555907603011683/1125899906842624), (16834798328483/2251799813685248)), (22349/1125899906842624), by norm_num⟩
  | 1 => ⟨((552371856571385/562949953421312), (6273446284009/281474976710656)), (33777/562949953421312), by norm_num⟩
  | 0 => ⟨((135434282556825/140737488355328), (49555764015807/1125899906842624)), (137143/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((135434282556825/140737488355328), (49555764015807/1125899906842624)), (523159031394576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1040466112663243/1125899906842624), (95376852670429/1125899906842624)), (34503/140737488355328), by norm_num⟩
  | 2 => ⟨((119179442711919/140737488355328), (176279227901077/1125899906842624)), (139231/281474976710656), by norm_num⟩
  | 3 => ⟨((1559579072069733/2251799813685248), (149276929611643/562949953421312)), (2235245/2251799813685248), by norm_num⟩
  | 4 => ⟨((921817846326353/2251799813685248), (827104341870015/2251799813685248)), (66901/35184372088832), by norm_num⟩
  | 5 => ⟨((147123690533069/4503599627370496), (1354364697032283/4503599627370496)), (13301889/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1609964030758773/18014398509481984), (176977661463599/9007199254740992)), (35478523/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-22827593251/268435456)), (1/134217728), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-2915841849/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((756968676176529/18014398509481984), (684553838167325/9007199254740992)), (26006941/18014398509481984), by norm_num⟩
  | 1 => ⟨((-8181204813/68719476736), (-7398556019/34359738368)), (283/68719476736), by norm_num⟩
  | 2 => ⟨((2897387331/17179869184), (2620210955/8589934592)), (403/68719476736), by norm_num⟩
  | 3 => ⟨((-2736305483/17179869184), (-9898155523/34359738368)), (383/68719476736), by norm_num⟩
  | 4 => ⟨((969067151/8589934592), (14021793155/68719476736)), (273/68719476736), by norm_num⟩
  | 5 => ⟨((-8785836747/137438953472), (-7945346295/68719476736)), (311/137438953472), by norm_num⟩
  | 6 => ⟨((1037172913/34359738368), (3751810191/68719476736)), (37/34359738368), by norm_num⟩
  | 7 => ⟨((-6716644885/549755813888), (-6074102113/274877906944)), (241/549755813888), by norm_num⟩
  | 8 => ⟨((4757421979/1099511627776), (2151153395/274877906944)), (343/2199023255552), by norm_num⟩
  | 9 => ⟨((-5990573971/4398046511104), (-21669960903/8796093022208)), (217/4398046511104), by norm_num⟩
  | 10 => ⟨((6789029645/17592186044416), (12279124479/17592186044416)), (31/2199023255552), by norm_num⟩
  | 11 => ⟨((-3497230797/35184372088832), (-12354183/68719476736)), (257/70368744177664), by norm_num⟩
  | 12 => ⟨((6605600641/281474976710656), (5973680833/140737488355328)), (61/70368744177664), by norm_num⟩
  | 13 => ⟨((-11516969773/2251799813685248), (-5207603769/562949953421312)), (107/562949953421312), by norm_num⟩
  | 14 => ⟨((9322866413/9007199254740992), (16862002845/9007199254740992)), (349/9007199254740992), by norm_num⟩
  | 15 => ⟨((-7043645207/36028797018963968), (-1592455049/4503599627370496)), (265/36028797018963968), by norm_num⟩
  | 16 => ⟨((2494518699/72057594037927936), (18047059579/288230376151711744)), (377/288230376151711744), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (1388239459305/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778198931427123/633825300114114700748351602688), (205238580261/79228162514264337593543950336)), (5773/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889100878403553/39614081257132168796771975168), (1846755328551/39614081257132168796771975168)), (6495/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888836011735609/2475880078570760549798248448), (61302765619/77371252455336267181195264)), (3451/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770502397056495/154742504910672534362390528), (245142320551/19342813113834066795298816)), (6903/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387227074365769/2417851639229258349412352), (1837983302305/9671406556917033397649408)), (12945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258224340944771/604462909807314587353088), (1607651517837/604462909807314587353088)), (11329/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943437629262127/37778931862957161709568), (2611339445937/75557863725914323419136)), (4603/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648426049821125/2361183241434822606848), (489386896585/1180591620717411303424)), (3453/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810251693258605/295147905179352825856), (2690073724935/590295810358705651712)), (4749/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911147141024623/36893488147419103232), (1680131224063/36893488147419103232)), (23751/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821329790132529/9223372036854775808), (3777094505941/9223372036854775808)), (26731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592579258979421/1152921504606846976), (1886548733963/576460752303423488)), (26743/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193351068853441/144115188075855872), (3296968970009/144115188075855872)), (11707/72057594037927936), by norm_num⟩
  | 4 => ⟨((186224378091701/4503599627370496), (4936484193453/36028797018963968)), (35149/36028797018963968), by norm_num⟩
  | 3 => ⟨((92934905958079/562949953421312), (6154939066371/9007199254740992)), (43985/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223361059986743/4503599627370496), (6131499757631/2251799813685248)), (44059/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104625775566587/1125899906842624), (4569430355119/562949953421312)), (33137/562949953421312), by norm_num⟩
  | 0 => ⟨((2167141859666869/2251799813685248), (18045417838837/1125899906842624)), (66647/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167141859666869/2251799813685248), (18045417838837/1125899906842624)), (254238130809593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1042544115814717/1125899906842624), (34733976027577/1125899906842624)), (521677/2251799813685248), by norm_num⟩
  | 2 => ⟨((964288013286923/1125899906842624), (128649810187653/2251799813685248)), (499149/1125899906842624), by norm_num⟩
  | 3 => ⟨((1644397825290709/2251799813685248), (220366782378519/2251799813685248)), (1824075/2251799813685248), by norm_num⟩
  | 4 => ⟨((294817802287123/562949953421312), (321849798110161/2251799813685248)), (3021113/2251799813685248), by norm_num⟩
  | 5 => ⟨((285792121564431/1125899906842624), (337106520992563/2251799813685248)), (8055879/4503599627370496), by norm_num⟩
  | 6 => ⟨((756968676176529/18014398509481984), (684553838167325/9007199254740992)), (26006941/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-2915841849/33554432)), (1/134217728), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-11898668977/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1150986913265451/18014398509481984), (-944926747329911/18014398509481984)), (20066783/18014398509481984), by norm_num⟩
  | 1 => ⟨((-3172664707/17179869184), (10418661437/68719476736)), (223/68719476736), by norm_num⟩
  | 2 => ⟨((18340360933/68719476736), (-7528451193/34359738368)), (325/68719476736), by norm_num⟩
  | 3 => ⟨((-17670153757/68719476736), (7253340903/34359738368)), (315/68719476736), by norm_num⟩
  | 4 => ⟨((1596041043/8589934592), (-1310303231/8589934592)), (115/34359738368), by norm_num⟩
  | 5 => ⟨((-922630391/8589934592), (6059621525/68719476736)), (67/34359738368), by norm_num⟩
  | 6 => ⟨((14222639067/274877906944), (-11676372613/274877906944)), (65/68719476736), by norm_num⟩
  | 7 => ⟨((-5872673469/274877906944), (1205323487/68719476736)), (27/68719476736), by norm_num⟩
  | 8 => ⟨((8487104769/1099511627776), (-1741916483/274877906944)), (157/1099511627776), by norm_num⟩
  | 9 => ⟨((-5451308429/2199023255552), (8950731035/4398046511104)), (203/4398046511104), by norm_num⟩
  | 10 => ⟨((12605046341/17592186044416), (-5174188039/8796093022208)), (237/17592186044416), by norm_num⟩
  | 11 => ⟨((-1656057725/8796093022208), (10876601439/70368744177664)), (251/70368744177664), by norm_num⟩
  | 12 => ⟨((12764326607/281474976710656), (-2619785135/70368744177664)), (61/70368744177664), by norm_num⟩
  | 13 => ⟨((-11351892041/1125899906842624), (9319572881/1125899906842624)), (219/1125899906842624), by norm_num⟩
  | 14 => ⟨((9374625187/4503599627370496), (-15392588715/9007199254740992)), (91/2251799813685248), by norm_num⟩
  | 15 => ⟨((-14451281003/36028797018963968), (11864080987/36028797018963968)), (283/36028797018963968), by norm_num⟩
  | 16 => ⟨((10442393619/144115188075855872), (-8572901155/144115188075855872)), (103/72057594037927936), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-895412524511/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889061913163279/316912650057057350374175801344), (-1058942578423/633825300114114700748351602688)), (11539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889016450175369/39614081257132168796771975168), (-1191053431069/39614081257132168796771975168)), (6491/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888746391487871/2475880078570760549798248448), (-632586291977/1237940039285380274899124224)), (13795/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770412872062789/154742504910672534362390528), (-316202713177/38685626227668133590597632)), (13795/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548824468924061/9671406556917033397649408), (-592687988849/4835703278458516698824704)), (6467/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629075546021367/302231454903657293676544), (-1036819944403/604462909807314587353088)), (11319/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378209204481/37778931862957161709568), (-1684112683183/75557863725914323419136)), (18395/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296763135082617/4722366482869645213696), (-1262455092721/4722366482869645213696)), (6899/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620381328938695/590295810358705651712), (-433713396127/147573952589676412928)), (593/18446744073709551616), by norm_num⟩
  | 8 => ⟨((56941941018917/2305843009213693952), (-2167034846083/73786976294838206464)), (5931/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821159152162535/9223372036854775808), (-2435809331173/9223372036854775808)), (3337/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592409310594081/1152921504606846976), (-2433180961771/1152921504606846976)), (1669/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193203138105799/144115188075855872), (-531520040083/36028797018963968)), (23375/144115188075855872), by norm_num⟩
  | 4 => ⟨((46549208517691/1125899906842624), (-3183223201441/36028797018963968)), (4385/4503599627370496), by norm_num⟩
  | 3 => ⟨((743342873777299/4503599627370496), (-3968730126683/9007199254740992)), (21941/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111411801955485/2251799813685248), (-7906647229329/4503599627370496)), (87859/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208465333783115/2251799813685248), (-11783230117829/2251799813685248)), (132029/2251799813685248), by norm_num⟩
  | 0 => ⟨((541412126095093/562949953421312), (-11630621092251/1125899906842624)), (265033/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541412126095093/562949953421312), (-11630621092251/1125899906842624)), (1011020668990325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1041276478183523/1125899906842624), (-44742586832755/2251799813685248)), (515263/2251799813685248), by norm_num⟩
  | 2 => ⟨((962568895034685/1125899906842624), (-82759405092559/2251799813685248)), (243387/562949953421312), by norm_num⟩
  | 3 => ⟨((1642822052448657/2251799813685248), (-70753739856919/1125899906842624)), (868099/1125899906842624), by norm_num⟩
  | 4 => ⟨((297410976867935/562949953421312), (-206476265649801/2251799813685248)), (2751533/2251799813685248), by norm_num⟩
  | 5 => ⟨((1219131620818053/4503599627370496), (-436332270701815/4503599627370496)), (426489/281474976710656), by norm_num⟩
  | 6 => ⟨((1150986913265451/18014398509481984), (-944926747329911/18014398509481984)), (20066783/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-11898668977/134217728)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-681712945/268435456), (-12121245179/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-994449464107047/18014398509481984), (-253875947490125/4503599627370496)), (2034699/1125899906842624), by norm_num⟩
  | 1 => ⟨((2792449727/17179869184), (11406284113/68719476736)), (23/4294967296), by norm_num⟩
  | 2 => ⟨((-16444395647/68719476736), (-16792553775/68719476736)), (17/2147483648), by norm_num⟩
  | 3 => ⟨((4034959961/17179869184), (16481549965/68719476736)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((-2970173347/17179869184), (-6066114769/34359738368)), (397/68719476736), by norm_num⟩
  | 5 => ⟨((3498197671/34359738368), (7144521911/68719476736)), (235/68719476736), by norm_num⟩
  | 6 => ⟨((-13733639439/274877906944), (-3506101467/68719476736)), (463/274877906944), by norm_num⟩
  | 7 => ⟨((5776837613/274877906944), (11798287799/549755813888)), (391/549755813888), by norm_num⟩
  | 8 => ⟨((-4252386461/549755813888), (-8684834621/1099511627776)), (289/1099511627776), by norm_num⟩
  | 9 => ⟨((5564841089/2199023255552), (5682659019/2199023255552)), (95/1099511627776), by norm_num⟩
  | 10 => ⟨((-3277067003/4398046511104), (-13385794177/17592186044416)), (225/8796093022208), by norm_num⟩
  | 11 => ⟨((7017544597/35184372088832), (7166118935/35184372088832)), (121/17592186044416), by norm_num⟩
  | 12 => ⟨((-6887577283/140737488355328), (-3516699987/70368744177664)), (477/281474976710656), by norm_num⟩
  | 13 => ⟨((12480031399/1125899906842624), (99564505/8796093022208)), (217/562949953421312), by norm_num⟩
  | 14 => ⟨((-5249527273/2251799813685248), (-2680334715/1125899906842624)), (367/4503599627370496), by norm_num⟩
  | 15 => ⟨((16487373573/36028797018963968), (8418220813/18014398509481984)), (579/36028797018963968), by norm_num⟩
  | 16 => ⟨((-12136516353/144115188075855872), (-3098367187/36028797018963968)), (107/36028797018963968), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (-763890498373/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889022796074657/316912650057057350374175801344), (-451665491243/79228162514264337593543950336)), (5785/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888928102069857/39614081257132168796771975168), (-2032041261217/19807040628566084398385987584)), (13019/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888652074525973/2475880078570760549798248448), (-2158483920701/1237940039285380274899124224)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770318052662669/154742504910672534362390528), (-4315708363437/154742504910672534362390528)), (865/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548735042323009/9671406556917033397649408), (-1011159692331/2417851639229258349412352)), (12979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314518077708537/151115727451828646838272), (-442215190261/75557863725914323419136)), (11361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886627400717231/75557863725914323419136), (-5746290739485/75557863725914323419136)), (4617/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324166374846179/1180591620717411303424), (-4307525555431/4722366482869645213696)), (6929/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405061416017013/147573952589676412928), (-5919286501661/590295810358705651712)), (19065/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455492602794867/18446744073709551616), (-924221168839/9223372036854775808)), (23847/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820963078018077/9223372036854775808), (-4155327230571/4611686018427387904)), (26849/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592209607024295/1152921504606846976), (-8301491525191/1152921504606846976)), (26877/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193024325533531/144115188075855872), (-7253506592491/144115188075855872)), (5887/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489298337645617/36028797018963968), (-10859687424127/36028797018963968)), (35383/36028797018963968), by norm_num⟩
  | 3 => ⟨((371581547070731/2251799813685248), (-3384665653643/2251799813685248)), (2771/562949953421312), by norm_num⟩
  | 2 => ⟨((1111031156373355/2251799813685248), (-26969705714709/4503599627370496)), (88997/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103609417325759/1125899906842624), (-40186280986335/2251799813685248)), (134309/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162742446192497/2251799813685248), (-79304074893501/2251799813685248)), (271885/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2162742446192497/2251799813685248), (-79304074893501/2251799813685248)), (1037158974654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1037207154001683/1125899906842624), (-76167645048121/1125899906842624)), (67677/281474976710656), by norm_num⟩
  | 2 => ⟨((1900696791352797/2251799813685248), (-140335079285897/1125899906842624)), (1070787/2251799813685248), by norm_num⟩
  | 3 => ⟨((1569354670548019/2251799813685248), (-236907768880585/1125899906842624)), (1037295/1125899906842624), by norm_num⟩
  | 4 => ⟨((994037260569669/2251799813685248), (-330217909533787/1125899906842624)), (3764759/2251799813685248), by norm_num⟩
  | 5 => ⟨((490216404619121/4503599627370496), (-1166174379051229/4503599627370496)), (11064381/4503599627370496), by norm_num⟩
  | 6 => ⟨((-994449464107047/18014398509481984), (-253875947490125/4503599627370496)), (2034699/1125899906842624), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-12121245179/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-693588655/268435456), (-3083100519/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-969227461355177/18014398509481984), (476893148543751/9007199254740992)), (1948481/1125899906842624), by norm_num⟩
  | 1 => ⟨((11076148935/68719476736), (-10899690217/68719476736)), (179/34359738368), by norm_num⟩
  | 2 => ⟨((-32403493/134217728), (16326276877/68719476736)), (539/68719476736), by norm_num⟩
  | 3 => ⟨((4141746763/17179869184), (-4075762879/17179869184)), (135/17179869184), by norm_num⟩
  | 4 => ⟨((-12407564447/68719476736), (3052473599/17179869184)), (203/34359738368), by norm_num⟩
  | 5 => ⟨((3716974125/34359738368), (-1828878735/17179869184)), (489/137438953472), by norm_num⟩
  | 6 => ⟨((-14846745795/274877906944), (1826277017/34359738368)), (245/137438953472), by norm_num⟩
  | 7 => ⟨((3176919681/137438953472), (-12505227429/549755813888)), (421/549755813888), by norm_num⟩
  | 8 => ⟨((-9517200819/1099511627776), (9365578349/1099511627776)), (317/1099511627776), by norm_num⟩
  | 9 => ⟨((12671549177/4398046511104), (-3117418369/1099511627776)), (53/549755813888), by norm_num⟩
  | 10 => ⟨((-7592113765/8796093022208), (14942321309/17592186044416)), (255/8796093022208), by norm_num⟩
  | 11 => ⟨((1033815465/4398046511104), (-16277525159/70368744177664)), (279/35184372088832), by norm_num⟩
  | 12 => ⟨((-16517516551/281474976710656), (16254369151/281474976710656)), (35/17592186044416), by norm_num⟩
  | 13 => ⟨((7612624217/562949953421312), (-14982688693/1125899906842624)), (259/562949953421312), by norm_num⟩
  | 14 => ⟨((-6515824015/2251799813685248), (6412017723/2251799813685248)), (223/2251799813685248), by norm_num⟩
  | 15 => ⟨((5205243811/9007199254740992), (-5122316915/9007199254740992)), (179/9007199254740992), by norm_num⟩
  | 16 => ⟨((-3898379219/36028797018963968), (7672545049/72057594037927936)), (539/144115188075855872), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (3079665709767/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777977336189081/633825300114114700748351602688), (3641561430653/633825300114114700748351602688)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472212831467663/9903520314283042199192993792), (4095827666255/39614081257132168796771975168)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888570513060117/2475880078570760549798248448), (543833585741/309485009821345068724781056)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770236506111569/154742504910672534362390528), (4349377311443/154742504910672534362390528)), (13841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548658608284211/9671406556917033397649408), (2038084768513/4835703278458516698824704)), (3245/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629002723454879/302231454903657293676544), (3565277094133/604462909807314587353088)), (11361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((14738427942117/590295810358705651712), (2895502560627/37778931862957161709568)), (18469/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296584057336219/4722366482869645213696), (1085251473039/1180591620717411303424)), (13859/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620133723602939/590295810358705651712), (5965231944051/590295810358705651712)), (9533/295147905179352825856), by norm_num⟩
  | 8 => ⟨((56932204661615/2305843009213693952), (3725533135725/36893488147419103232)), (2981/9223372036854775808), by norm_num⟩
  | 7 => ⟨((227600727593489/1152921504606846976), (4187464137651/4611686018427387904)), (26851/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592052459226759/1152921504606846976), (8365534174131/1152921504606846976)), (26879/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596443472260247/72057594037927936), (456830271661/9007199254740992)), (11775/72057594037927936), by norm_num⟩
  | 4 => ⟨((23267070517597/562949953421312), (10942836169323/36028797018963968)), (17693/18014398509481984), by norm_num⟩
  | 3 => ⟨((371517335183513/2251799813685248), (13641695035579/9007199254740992)), (22171/4503599627370496), by norm_num⟩
  | 2 => ⟨((277693740040049/562949953421312), (27173071166947/4503599627370496)), (44505/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206453514350749/2251799813685248), (10121154901391/562949953421312)), (134335/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080612473912645/1125899906842624), (79874146741615/2251799813685248)), (271965/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080612473912645/1125899906842624), (79874146741615/2251799813685248)), (1037464150435637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((129466254266817/140737488355328), (76661343328615/1125899906842624)), (270673/1125899906842624), by norm_num⟩
  | 2 => ⟨((1895123599466649/2251799813685248), (17630442826221/140737488355328)), (1069703/2251799813685248), by norm_num⟩
  | 3 => ⟨((1559605926008245/2251799813685248), (474811205734495/2251799813685248)), (2068541/2251799813685248), by norm_num⟩
  | 4 => ⟨((15313618174563/35184372088832), (657712435801939/2251799813685248)), (934425/562949953421312), by norm_num⟩
  | 5 => ⟨((234458950356653/2251799813685248), (1145048953564205/4503599627370496)), (5437025/2251799813685248), by norm_num⟩
  | 6 => ⟨((-969227461355177/18014398509481984), (476893148543751/9007199254740992)), (1948481/1125899906842624), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-3083100519/33554432)), (1/134217728), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-352442413/134217728), (-3133313611/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((842947337058021/18014398509481984), (994631751766567/18014398509481984)), (2451049/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4894966281/34359738368), (-1443948119/8589934592)), (115/34359738368), by norm_num⟩
  | 2 => ⟨((7451417337/34359738368), (17584529789/68719476736)), (11/2147483648), by norm_num⟩
  | 3 => ⟨((-7562002425/34359738368), (-4461374625/17179869184)), (359/68719476736), by norm_num⟩
  | 4 => ⟨((11511343029/68719476736), (13582755149/68719476736)), (275/68719476736), by norm_num⟩
  | 5 => ⟨((-1752327107/17179869184), (-16541201127/137438953472)), (337/137438953472), by norm_num⟩
  | 6 => ⟨((14226664521/274877906944), (16786685993/274877906944)), (43/34359738368), by norm_num⟩
  | 7 => ⟨((-12375256957/549755813888), (-3650531583/137438953472)), (301/549755813888), by norm_num⟩
  | 8 => ⟨((4709593435/549755813888), (5557062657/549755813888)), (231/1099511627776), by norm_num⟩
  | 9 => ⟨((-12745300343/4398046511104), (-7519378643/2199023255552)), (315/4398046511104), by norm_num⟩
  | 10 => ⟨((3880335287/4398046511104), (18314333597/17592186044416)), (193/8796093022208), by norm_num⟩
  | 11 => ⟨((-4295915581/17592186044416), (-10137890831/35184372088832)), (27/4398046511104), by norm_num⟩
  | 12 => ⟨((4359670459/70368744177664), (10288345369/140737488355328)), (221/140737488355328), by norm_num⟩
  | 13 => ⟨((-4084035241/281474976710656), (-9637876407/562949953421312)), (13/35184372088832), by norm_num⟩
  | 14 => ⟨((55508647/17592186044416), (8383637421/2251799813685248)), (91/1125899906842624), by norm_num⟩
  | 15 => ⟨((-11536883799/18014398509481984), (-3403222965/4503599627370496)), (149/9007199254740992), by norm_num⟩
  | 16 => ⟨((8781075397/72057594037927936), (5180594339/36028797018963968)), (229/72057594037927936), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (1130350678869/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777918673711485/633825300114114700748351602688), (668247093967/316912650057057350374175801344)), (5771/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944392842512515/19807040628566084398385987584), (1503215121291/39614081257132168796771975168)), (6493/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888501241250373/2475880078570760549798248448), (798369210127/1237940039285380274899124224)), (13799/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770167764279669/154742504910672534362390528), (399064387527/38685626227668133590597632)), (1725/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548594725482531/9671406556917033397649408), (186997590787/1208925819614629174706176)), (12939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628975055816803/302231454903657293676544), (1308472630963/604462909807314587353088)), (2831/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235803738725565/9444732965739290427392), (1062655650813/37778931862957161709568)), (9201/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648259163806677/2361183241434822606848), (1593146815061/4722366482869645213696)), (13805/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620044838880765/590295810358705651712), (547304545225/147573952589676412928)), (18985/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455430420082663/18446744073709551616), (2734486238295/73786976294838206464)), (23737/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113792900858063/576460752303423488), (48023427483/144115188075855872)), (3339/1152921504606846976), by norm_num⟩
  | 6 => ⟨((198992110244233/144115188075855872), (1535003024341/576460752303423488)), (13361/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192790111492423/144115188075855872), (670582621945/36028797018963968)), (11697/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488955829361697/36028797018963968), (4015659027217/36028797018963968)), (35113/36028797018963968), by norm_num⟩
  | 3 => ⟨((185739176549671/1125899906842624), (312868033687/562949953421312)), (43931/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221282588506877/4503599627370496), (1246354631239/562949953421312)), (87983/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206162942150971/2251799813685248), (14854309383275/2251799813685248)), (66139/1125899906842624), by norm_num⟩
  | 0 => ⟨((67533756611101/70368744177664), (14651624262937/1125899906842624)), (132891/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((67533756611101/70368744177664), (14651624262937/1125899906842624)), (506938938621139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2073634153455045/2251799813685248), (28122691075239/1125899906842624)), (517067/2251799813685248), by norm_num⟩
  | 2 => ⟨((1908160322799709/2251799813685248), (103590332224501/2251799813685248)), (978143/2251799813685248), by norm_num⟩
  | 3 => ⟨((806098490308373/1125899906842624), (175563529737517/2251799813685248)), (1747741/2251799813685248), by norm_num⟩
  | 4 => ⟨((285144857873993/562949953421312), (251392677829581/2251799813685248)), (173447/140737488355328), by norm_num⟩
  | 5 => ⟨((1099319001239027/4503599627370496), (63667586216701/562949953421312)), (3430975/2251799813685248), by norm_num⟩
  | 6 => ⟨((842947337058021/18014398509481984), (994631751766567/18014398509481984)), (2451049/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-3133313611/33554432)), (1/134217728), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile057Terms2
