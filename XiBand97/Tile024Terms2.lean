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
namespace Reinmann.XiBand97.Tile024Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

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
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-20060163/8388608), (-1065696157/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((318203299038509/4503599627370496), (-523740173695697/9007199254740992)), (44386777/2251799813685248), by norm_num⟩
  | 1 => ⟨((-841376189/4294967296), (346211457/2147483648)), (237/4294967296), by norm_num⟩
  | 2 => ⟨((583197533/2147483648), (-959901981/4294967296)), (331/4294967296), by norm_num⟩
  | 3 => ⟨((-1077977935/4294967296), (443568901/2147483648)), (77/1073741824), by norm_num⟩
  | 4 => ⟨((373598683/2147483648), (-307458533/2147483648)), (27/536870912), by norm_num⟩
  | 5 => ⟨((-207167099/2147483648), (681964849/8589934592)), (241/8589934592), by norm_num⟩
  | 6 => ⟨((95731527/2147483648), (-315134675/8589934592)), (225/17179869184), by norm_num⟩
  | 7 => ⟨((-4739717/268435456), (499279341/34359738368)), (45/8589934592), by norm_num⟩
  | 8 => ⟨((420521149/68719476736), (-692148135/137438953472)), (251/137438953472), by norm_num⟩
  | 9 => ⟨((-518192087/274877906944), (426453803/274877906944)), (39/68719476736), by norm_num⟩
  | 10 => ⟨((1149386829/2199023255552), (-236476201/549755813888)), (87/549755813888), by norm_num⟩
  | 11 => ⟨((-1158827985/8796093022208), (953674543/8796093022208)), (177/4398046511104), by norm_num⟩
  | 12 => ⟨((1070984467/35184372088832), (-220345607/8796093022208)), (165/17592186044416), by norm_num⟩
  | 13 => ⟨((-913661371/140737488355328), (751911071/140737488355328)), (71/35184372088832), by norm_num⟩
  | 14 => ⟨((361886745/281474976710656), (-148910011/140737488355328)), (227/562949953421312), by norm_num⟩
  | 15 => ⟨((-535126991/2251799813685248), (880781263/4503599627370496)), (169/2251799813685248), by norm_num⟩
  | 16 => ⟨((370921765/9007199254740992), (-610511049/18014398509481984)), (59/4503599627370496), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-448481248417/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889140167187185/316912650057057350374175801344), (-1060953593419/633825300114114700748351602688)), (184609/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944596242121845/19807040628566084398385987584), (-1193325226501/39614081257132168796771975168)), (207699/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944466690470515/1237940039285380274899124224), (-633799432517/1237940039285380274899124224)), (220695/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770599808950029/154742504910672534362390528), (-633625589637/77371252455336267181195264)), (220713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548999666423849/9671406556917033397649408), (-593839347881/4835703278458516698824704)), (103469/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258304334044749/604462909807314587353088), (-1038849721755/604462909807314587353088)), (181089/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887005332064023/75557863725914323419136), (-26366234059/1180591620717411303424)), (9197/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648474864423275/2361183241434822606848), (-316243551931/1180591620717411303424)), (220759/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810318873399867/295147905179352825856), (-1738356954423/590295810358705651712)), (303593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822462412236105/73786976294838206464), (-2171473349291/73786976294838206464)), (189783/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821519183285999/9223372036854775808), (-305110503389/1152921504606846976)), (427115/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592768959633653/1152921504606846976), (-609589291313/288230376151711744)), (106811/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193517401675925/144115188075855872), (-1065361618079/72057594037927936)), (11687/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490045210503035/36028797018963968), (-3190414866759/36028797018963968)), (561267/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487272422326429/9007199254740992), (-497264422351/1125899906842624)), (43881/562949953421312), by norm_num⟩
  | 2 => ⟨((2223992471817233/4503599627370496), (-3963299043375/2251799813685248)), (702865/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105103735523049/1125899906842624), (-11816084076653/2251799813685248)), (2112463/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084544178392657/1125899906842624), (-23338522278325/2251799813685248)), (4240503/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084544178392657/1125899906842624), (-23338522278325/2251799813685248)), (16176235207564543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089173106920351/2251799813685248), (-22481268819203/1125899906842624)), (8257389/2251799813685248), by norm_num⟩
  | 2 => ⟨((484348410366525/562949953421312), (-41715308741997/1125899906842624)), (7825913/1125899906842624), by norm_num⟩
  | 3 => ⟨((415948770322529/562949953421312), (-71781668527873/1125899906842624)), (1755795/140737488355328), by norm_num⟩
  | 4 => ⟨((1220181129814525/2251799813685248), (-212150274278629/2251799813685248)), (22548015/1125899906842624), by norm_num⟩
  | 5 => ⟨((1282382423076947/4503599627370496), (-459830860250603/4503599627370496)), (114739261/4503599627370496), by norm_num⟩
  | 6 => ⟨((318203299038509/4503599627370496), (-523740173695697/9007199254740992)), (44386777/2251799813685248), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1065696157/16777216)), (1/8388608), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-40997585/16777216), (-136124795/2097152)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-759226916992175/18014398509481984), (-1367856712452143/18014398509481984)), (562247557/18014398509481984), by norm_num⟩
  | 1 => ⟨((512850721/4294967296), (115496811/536870912)), (191/2147483648), by norm_num⟩
  | 2 => ⟨((-726507753/4294967296), (-1308908425/4294967296)), (17/134217728), by norm_num⟩
  | 3 => ⟨((686117153/4294967296), (1236138939/4294967296)), (129/1073741824), by norm_num⟩
  | 4 => ⟨((-121494767/1073741824), (-437780667/2147483648)), (23/268435456), by norm_num⟩
  | 5 => ⟨((68844119/1073741824), (496130411/4294967296)), (419/8589934592), by norm_num⟩
  | 6 => ⟨((-260066769/8589934592), (-468547767/8589934592)), (199/8589934592), by norm_num⟩
  | 7 => ⟨((105260663/8589934592), (189642255/8589934592)), (81/8589934592), by norm_num⟩
  | 8 => ⟨((-298225915/68719476736), (-1074593935/137438953472)), (461/137438953472), by norm_num⟩
  | 9 => ⟨((375527841/274877906944), (84570941/34359738368)), (583/549755813888), by norm_num⟩
  | 10 => ⟨((-106395049/274877906944), (-766744059/1099511627776)), (83/274877906944), by norm_num⟩
  | 11 => ⟨((109614499/1099511627776), (789945273/4398046511104)), (43/549755813888), by norm_num⟩
  | 12 => ⟨((-207040841/8796093022208), (-373013915/8796093022208)), (327/17592186044416), by norm_num⟩
  | 13 => ⟨((360978999/70368744177664), (1300711387/140737488355328)), (573/140737488355328), by norm_num⟩
  | 14 => ⟨((-292208719/281474976710656), (-1052912245/562949953421312)), (233/281474976710656), by norm_num⟩
  | 15 => ⟨((220770571/1125899906842624), (397750003/1125899906842624)), (177/1125899906842624), by norm_num⟩
  | 16 => ⟨((-39093133/1125899906842624), (-140863827/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-2706185261325/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111137180370305/39614081257132168796771975168), (-25005305157/4951760157141521099596496896)), (92515/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889096103330283/39614081257132168796771975168), (-1799995895483/19807040628566084398385987584)), (208199/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944415320734555/1237940039285380274899124224), (-478004627397/309485009821345068724781056)), (221259/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885248346640697/77371252455336267181195264), (-119467618449/4835703278458516698824704)), (1729/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((1548902596086733/9671406556917033397649408), (-3582888572611/9671406556917033397649408)), (12971/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629109499226159/302231454903657293676544), (-1566943942657/302231454903657293676544)), (181651/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943432957128137/37778931862957161709568), (-2545215904969/37778931862957161709568)), (295287/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324211128049457/1180591620717411303424), (-1907977814917/2361183241434822606848)), (110779/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405123003424857/147573952589676412928), (-5243904575077/590295810358705651712)), (304791/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822278657983089/73786976294838206464), (-1637582909657/18446744073709551616)), (190607/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910655140185921/4611686018427387904), (-7362872240379/9223372036854775808)), (214587/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398139334603951/288230376151711744), (-7355064870101/1152921504606846976)), (214781/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193329183147193/144115188075855872), (-6426906985691/144115188075855872)), (376303/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489756803067845/36028797018963968), (-4811416102985/18014398509481984)), (565327/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486901319195885/9007199254740992), (-5998956813575/4503599627370496)), (177047/2251799813685248), by norm_num⟩
  | 2 => ⟨((138951166605293/281474976710656), (-23904138597469/4503599627370496)), (710487/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104484197805517/1125899906842624), (-35627654885099/2251799813685248)), (535747/562949953421312), by norm_num⟩
  | 0 => ⟨((1083150261669601/1125899906842624), (-70345103987925/2251799813685248)), (2166137/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083150261669601/1125899906842624), (-70345103987925/2251799813685248)), (8263156895164107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2081850036257217/2251799813685248), (-33837074383179/562949953421312)), (4303119/1125899906842624), by norm_num⟩
  | 2 => ⟨((958295756485577/1125899906842624), (-250266348201433/2251799813685248)), (4236997/562949953421312), by norm_num⟩
  | 3 => ⟨((1603468372546757/2251799813685248), (-426022203243859/2251799813685248)), (2038585/140737488355328), by norm_num⟩
  | 4 => ⟨((1061202638697353/2251799813685248), (-606726339306553/2251799813685248)), (58794415/2251799813685248), by norm_num⟩
  | 5 => ⟨((336634804285427/2251799813685248), (-142965548785967/562949953421312)), (174198275/4503599627370496), by norm_num⟩
  | 6 => ⟨((-759226916992175/18014398509481984), (-1367856712452143/18014398509481984)), (562247557/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-136124795/2097152)), (1/8388608), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2614043/1048576), (-555484131/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-722278147633081/9007199254740992), (90455240986867/4503599627370496)), (129258917/4503599627370496), by norm_num⟩
  | 1 => ⟨((995470219/4294967296), (-124668729/2147483648)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((-89914969/268435456), (360338973/4294967296)), (65/536870912), by norm_num⟩
  | 3 => ⟨((86629229/268435456), (-347171197/4294967296)), (503/4294967296), by norm_num⟩
  | 4 => ⟨((-250390677/1073741824), (7839483/134217728)), (365/4294967296), by norm_num⟩
  | 5 => ⟨((578977713/4294967296), (-290035459/8589934592)), (53/1073741824), by norm_num⟩
  | 6 => ⟨((-557820277/8589934592), (279436767/17179869184)), (411/17179869184), by norm_num⟩
  | 7 => ⟨((921318843/34359738368), (-230764611/34359738368)), (341/34359738368), by norm_num⟩
  | 8 => ⟨((-665738491/68719476736), (333497757/137438953472)), (495/137438953472), by norm_num⟩
  | 9 => ⟨((1710428207/549755813888), (-107103611/137438953472)), (319/274877906944), by norm_num⟩
  | 10 => ⟨((-988754677/1099511627776), (123827701/549755813888)), (185/549755813888), by norm_num⟩
  | 11 => ⟨((1039224943/4398046511104), (-260296793/4398046511104)), (391/4398046511104), by norm_num⟩
  | 12 => ⟨((-1001248809/17592186044416), (250784833/17592186044416)), (189/8796093022208), by norm_num⟩
  | 13 => ⟨((890455779/70368744177664), (-223034277/70368744177664)), (169/35184372088832), by norm_num⟩
  | 14 => ⟨((-735356639/281474976710656), (368372557/562949953421312)), (561/562949953421312), by norm_num⟩
  | 15 => ⟨((283393875/562949953421312), (-283928969/2251799813685248)), (435/2251799813685248), by norm_num⟩
  | 16 => ⟨((-819113653/9007199254740992), (410330137/18014398509481984)), (631/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (3772584478901/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778113757393529/633825300114114700748351602688), (4461575224661/633825300114114700748351602688)), (185279/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889004566858915/39614081257132168796771975168), (2509080488063/19807040628566084398385987584)), (208495/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944366513541643/1237940039285380274899124224), (5330437413267/2475880078570760549798248448)), (27699/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770398677810601/154742504910672534362390528), (2664454588723/77371252455336267181195264)), (221665/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548810280775065/9671406556917033397649408), (4994228948147/9671406556917033397649408)), (103945/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258137797134737/604462909807314587353088), (1092081827783/151115727451828646838272)), (90991/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471683291319215/18889465931478580854784), (7095489543997/75557863725914323419136)), (295867/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81046515878321/295147905179352825856), (1329738984213/1180591620717411303424)), (55507/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202544128578361/73786976294838206464), (7309241473239/590295810358705651712)), (152749/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455525808538743/18446744073709551616), (4565035067805/36893488147419103232)), (191093/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821110605775223/9223372036854775808), (10262420953089/9223372036854775808)), (430391/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592354766895221/1152921504606846976), (5125646307237/576460752303423488)), (430931/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596574341520473/72057594037927936), (8957370735655/144115188075855872)), (377673/144115188075855872), by norm_num⟩
  | 4 => ⟨((186184946919743/4503599627370496), (104773892311/281474976710656)), (567725/36028797018963968), by norm_num⟩
  | 3 => ⟨((743271749690231/4503599627370496), (16720127630093/9007199254740992)), (355895/4503599627370496), by norm_num⟩
  | 2 => ⟨((555617343050655/1125899906842624), (16654687377173/2251799813685248)), (178749/562949953421312), by norm_num⟩
  | 1 => ⟨((275970128073329/281474976710656), (1551174350449/70368744177664)), (1080533/1125899906842624), by norm_num⟩
  | 0 => ⟨((540889066135411/562949953421312), (48986772977693/1125899906842624)), (1096677/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((540889066135411/562949953421312), (48986772977693/1125899906842624)), (4183490755321311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1037254036913087/1125899906842624), (94134157851371/1125899906842624)), (137677/35184372088832), by norm_num⟩
  | 2 => ⟨((947717191318017/1125899906842624), (173445320759577/1125899906842624)), (1106785/140737488355328), by norm_num⟩
  | 3 => ⟨((385507002065885/562949953421312), (291992407563979/1125899906842624)), (17634049/1125899906842624), by norm_num⟩
  | 4 => ⟨((904526282305611/2251799813685248), (399911633287749/1125899906842624)), (2081125/70368744177664), by norm_num⟩
  | 5 => ⟨((39623979125849/1125899906842624), (642562594969811/2251799813685248)), (201621591/4503599627370496), by norm_num⟩
  | 6 => ⟨((-722278147633081/9007199254740992), (90455240986867/4503599627370496)), (129258917/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-555484131/8388608)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-42607059/16777216), (-565875003/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-123053664454701/18014398509481984), (707996379722865/9007199254740992)), (58999951/4503599627370496), by norm_num⟩
  | 1 => ⟨((86384775/4294967296), (-994039601/4294967296)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((-127177349/4294967296), (731722237/2147483648)), (31/536870912), by norm_num⟩
  | 3 => ⟨((124821981/4294967296), (-179542623/536870912)), (245/4294967296), by norm_num⟩
  | 4 => ⟨((-91882677/4294967296), (1057304595/4294967296)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((54108587/4294967296), (-1245267545/8589934592)), (27/1073741824), by norm_num⟩
  | 6 => ⟨((-106212955/17179869184), (611102383/8589934592)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((44676795/17179869184), (-1028202101/34359738368)), (181/34359738368), by norm_num⟩
  | 8 => ⟨((-131548097/137438953472), (378434793/34359738368)), (269/137438953472), by norm_num⟩
  | 9 => ⟨((86074521/274877906944), (-30952171/8589934592)), (89/137438953472), by norm_num⟩
  | 10 => ⟨((-50688235/549755813888), (72909423/68719476736)), (211/1099511627776), by norm_num⟩
  | 11 => ⟨((54272151/2199023255552), (-1249031837/4398046511104)), (57/1099511627776), by norm_num⟩
  | 12 => ⟨((-106534025/17592186044416), (612949671/8796093022208)), (113/8796093022208), by norm_num⟩
  | 13 => ⟨((48258913/35184372088832), (-1110641787/70368744177664)), (207/70368744177664), by norm_num⟩
  | 14 => ⟨((-162394771/562949953421312), (1868695411/562949953421312)), (175/281474976710656), by norm_num⟩
  | 15 => ⟨((31877433/562949953421312), (-1467269229/2251799813685248)), (277/2251799813685248), by norm_num⟩
  | 16 => ⟨((-23465289/2251799813685248), (540035589/4503599627370496)), (103/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (2159054447829/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889024548470117/316912650057057350374175801344), (2553167999555/633825300114114700748351602688)), (23113/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59029132435391/1237940039285380274899124224), (2871678859485/39614081257132168796771975168)), (13003/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944328362921529/1237940039285380274899124224), (1525184082553/1237940039285380274899124224)), (110545/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770322992763827/154742504910672534362390528), (3049479052143/154742504910672534362390528)), (55283/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193592497532693/1208925819614629174706176), (714485561037/2417851639229258349412352)), (51839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258076937854733/604462909807314587353088), (2499755451053/604462909807314587353088)), (90741/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471658873352971/18889465931478580854784), (2030166668885/37778931862957161709568)), (147495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648336035198523/2361183241434822606848), (3043702645007/4722366482869645213696)), (55329/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810127756531273/295147905179352825856), (130705565345/18446744073709551616)), (152215/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910991970664511/36893488147419103232), (5224455513779/73786976294838206464)), (95179/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910489986196609/4611686018427387904), (2936168349917/4611686018427387904)), (53569/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592228588041873/1152921504606846976), (5865873018311/1152921504606846976)), (214431/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193043275144285/144115188075855872), (640671938287/18014398509481984)), (93901/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489331428898375/36028797018963968), (7673557112445/36028797018963968)), (282051/36028797018963968), by norm_num⟩
  | 3 => ⟨((743187842138671/4503599627370496), (9566606978821/9007199254740992)), (176587/4503599627370496), by norm_num⟩
  | 2 => ⟨((555546390186557/1125899906842624), (2382172603701/562949953421312)), (88523/562949953421312), by norm_num⟩
  | 1 => ⟨((1103731929559335/1125899906842624), (7099283765841/562949953421312)), (533441/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081735096422097/1125899906842624), (56042395357333/2251799813685248)), (1076137/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081735096422097/1125899906842624), (56042395357333/2251799813685248)), (4105136875632857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2077210636940621/2251799813685248), (107688126763587/2251799813685248)), (4242829/2251799813685248), by norm_num⟩
  | 2 => ⟨((1911007928600399/2251799813685248), (99338724972823/1125899906842624)), (8233549/2251799813685248), by norm_num⟩
  | 3 => ⟨((1604262755553113/2251799813685248), (84304603760241/562949953421312)), (3856959/562949953421312), by norm_num⟩
  | 4 => ⟨((546217011490519/1125899906842624), (240246464383307/1125899906842624)), (13301739/1125899906842624), by norm_num⟩
  | 5 => ⟨((213726512037619/1125899906842624), (932421825415115/4503599627370496)), (74332235/4503599627370496), by norm_num⟩
  | 6 => ⟨((-123053664454701/18014398509481984), (707996379722865/9007199254740992)), (58999951/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-565875003/8388608)), (1/16777216), by norm_num⟩, -11, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-43349291/16777216), (-287866385/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((301169554184733/4503599627370496), (630761882721721/18014398509481984)), (127645073/18014398509481984), by norm_num⟩
  | 1 => ⟨((-107553405/536870912), (-112628563/1073741824)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((644402413/2147483648), (337405021/2147483648)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-321742851/1073741824), (-336925037/2147483648)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((963855443/4294967296), (126167151/1073741824)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-1154981143/8589934592), (-302370405/4294967296)), (133/8589934592), by norm_num⟩
  | 6 => ⟨((1153338095/17179869184), (603880521/17179869184)), (135/17179869184), by norm_num⟩
  | 7 => ⟨((-987169187/34359738368), (-516875533/34359738368)), (117/34359738368), by norm_num⟩
  | 8 => ⟨((2887983/268435456), (387105179/68719476736)), (89/68719476736), by norm_num⟩
  | 9 => ⟨((-984362539/274877906944), (-257702995/137438953472)), (15/34359738368), by norm_num⟩
  | 10 => ⟨((1179554651/1099511627776), (617607343/1099511627776)), (73/549755813888), by norm_num⟩
  | 11 => ⟨((-1284956341/4398046511104), (-84099375/549755813888)), (161/4398046511104), by norm_num⟩
  | 12 => ⟨((641564197/8796093022208), (335918949/8796093022208)), (163/17592186044416), by norm_num⟩
  | 13 => ⟨((-591370637/35184372088832), (-309637919/35184372088832)), (19/8796093022208), by norm_num⟩
  | 14 => ⟨((1012336059/281474976710656), (530052747/281474976710656)), (33/70368744177664), by norm_num⟩
  | 15 => ⟨((-202179187/281474976710656), (-211719483/562949953421312)), (107/1125899906842624), by norm_num⟩
  | 16 => ⟨((1211349431/9007199254740992), (79281861/1125899906842624)), (81/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (157076694685/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888992075298509/316912650057057350374175801344), (46433970999/39614081257132168796771975168)), (92273/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888859366396807/39614081257132168796771975168), (835625166835/39614081257132168796771975168)), (103813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888579555650951/2475880078570760549798248448), (887617853369/2475880078570760549798248448)), (55153/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770246110063481/154742504910672534362390528), (55459678781/9671406556917033397649408)), (110313/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548668207962431/9671406556917033397649408), (415807930411/4835703278458516698824704)), (103425/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157251805258661/75557863725914323419136), (727384680047/604462909807314587353088)), (11313/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886534509047057/75557863725914323419136), (1181476869151/75557863725914323419136)), (18385/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296596831455565/4722366482869645213696), (221412520231/1180591620717411303424)), (110321/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620152869914467/590295810358705651712), (304256449151/147573952589676412928)), (151709/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455464212802121/18446744073709551616), (1520168502307/73786976294838206464)), (94831/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910419331056687/4611686018427387904), (1708659553675/9223372036854775808)), (106703/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24876396188537/18014398509481984), (853374558017/576460752303423488)), (213451/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192923779317073/144115188075855872), (1491259086151/144115188075855872)), (93411/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489156834637013/36028797018963968), (2232602968185/36028797018963968)), (280335/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486165544767825/9007199254740992), (695817448689/2251799813685248)), (43825/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110894729496413/2251799813685248), (5544151668657/4503599627370496)), (701745/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206929687054341/2251799813685248), (8260480462485/2251799813685248)), (526997/1125899906842624), by norm_num⟩
  | 0 => ⟨((135164938110267/140737488355328), (8149652161791/1125899906842624)), (2113553/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((135164938110267/140737488355328), (8149652161791/1125899906842624)), (8062564858443450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519222644793955/562949953421312), (31307855296879/2251799813685248)), (4090331/2251799813685248), by norm_num⟩
  | 2 => ⟨((478783046105711/562949953421312), (57752016253943/2251799813685248)), (7658967/2251799813685248), by norm_num⟩
  | 3 => ⟨((1627318719079981/2251799813685248), (49117485653499/1125899906842624)), (3355151/562949953421312), by norm_num⟩
  | 4 => ⟨((1171736531748923/2251799813685248), (8873990857481/140737488355328)), (5142103/562949953421312), by norm_num⟩
  | 5 => ⟨((300383514754787/1125899906842624), (147764172739307/2251799813685248)), (5999899/562949953421312), by norm_num⟩
  | 6 => ⟨((301169554184733/4503599627370496), (630761882721721/18014398509481984)), (127645073/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-287866385/4194304)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-22027651/8388608), (-1170218949/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((524647094145937/9007199254740992), (-386921880068509/9007199254740992)), (68093509/4503599627370496), by norm_num⟩
  | 1 => ⟨((-761651921/4294967296), (561710523/4294967296)), (25/536870912), by norm_num⟩
  | 2 => ⟨((579716591/2147483648), (-427535073/2147483648)), (307/4294967296), by norm_num⟩
  | 3 => ⟨((-1176640113/4294967296), (433880041/2147483648)), (157/2147483648), by norm_num⟩
  | 4 => ⟨((447788403/2147483648), (-82559845/536870912)), (241/4294967296), by norm_num⟩
  | 5 => ⟨((-17041273/134217728), (402168481/4294967296)), (37/1073741824), by norm_num⟩
  | 6 => ⟨((553413739/8589934592), (-102034247/2147483648)), (151/8589934592), by norm_num⟩
  | 7 => ⟨((-962788883/34359738368), (355023491/17179869184)), (265/34359738368), by norm_num⟩
  | 8 => ⟨((732808089/68719476736), (-135109623/17179869184)), (51/17179869184), by norm_num⟩
  | 9 => ⟨((-991578075/274877906944), (365639359/137438953472)), (139/137438953472), by norm_num⟩
  | 10 => ⟨((1207552679/1099511627776), (-445278893/549755813888)), (341/1099511627776), by norm_num⟩
  | 11 => ⟨((-668440223/2199023255552), (61620981/274877906944)), (95/1099511627776), by norm_num⟩
  | 12 => ⟨((678360419/8796093022208), (-125070973/2199023255552)), (195/8796093022208), by norm_num⟩
  | 13 => ⟨((-635471851/35184372088832), (468654011/35184372088832)), (185/35184372088832), by norm_num⟩
  | 14 => ⟨((1105547605/281474976710656), (-815330087/281474976710656)), (81/70368744177664), by norm_num⟩
  | 15 => ⟨((-112195483/140737488355328), (661944199/1125899906842624)), (265/1125899906842624), by norm_num⟩
  | 16 => ⟨((683163331/4503599627370496), (-62978249/562949953421312)), (203/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-413869932601/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888959558950673/316912650057057350374175801344), (-978695850415/633825300114114700748351602688)), (184593/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888786209085203/39614081257132168796771975168), (-1100783514955/39614081257132168796771975168)), (3245/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1888501830623945/2475880078570760549798248448), (-1169269357045/2475880078570760549798248448)), (110337/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885084195120047/77371252455336267181195264), (-1168917263021/154742504910672534362390528)), (220691/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548595351162713/9671406556917033397649408), (-1095485981357/9671406556917033397649408)), (206915/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257950697910849/604462909807314587353088), (-958176446611/604462909807314587353088)), (45267/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943215467596795/37778931862957161709568), (-1556336226797/75557863725914323419136)), (294267/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162064895022871/590295810358705651712), (-583319792569/2361183241434822606848)), (220729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620046086756813/590295810358705651712), (-1603134637857/590295810358705651712)), (75887/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455430848642617/18446744073709551616), (-31287925967/1152921504606846976)), (23719/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1820688554144825/9223372036854775808), (-1125341183245/4611686018427387904)), (213519/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49748102707671/36028797018963968), (-2248124790625/1152921504606846976)), (427157/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596396256046125/72057594037927936), (-245529471069/18014398509481984)), (186949/72057594037927936), by norm_num⟩
  | 4 => ⟨((744480010608113/18014398509481984), (-2940616416585/36028797018963968)), (140279/9007199254740992), by norm_num⟩
  | 3 => ⟨((742959840910423/4503599627370496), (-1832875971281/4503599627370496)), (350935/4503599627370496), by norm_num⟩
  | 2 => ⟨((2221298197968273/4503599627370496), (-3650767151501/2251799813685248)), (1405169/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206193969446457/2251799813685248), (-10877678185481/2251799813685248)), (2111349/2251799813685248), by norm_num⟩
  | 0 => ⟨((2161172340136243/2251799813685248), (-10729330327029/1125899906842624)), (2118605/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2161172340136243/2251799813685248), (-10729330327029/1125899906842624)), (8081836704734420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((518496957552561/562949953421312), (-10297510369277/562949953421312)), (8214111/2251799813685248), by norm_num⟩
  | 2 => ⟨((1909463209922939/2251799813685248), (-37937495256103/1125899906842624)), (15431485/2251799813685248), by norm_num⟩
  | 3 => ⟨((202076840586595/281474976710656), (-128679736143331/2251799813685248)), (3401359/281474976710656), by norm_num⟩
  | 4 => ⟨((576624235826169/1125899906842624), (-46190952444933/562949953421312)), (42180469/2251799813685248), by norm_num⟩
  | 5 => ⟨((287735251617101/1125899906842624), (-378503595124505/4503599627370496)), (25063501/1125899906842624), by norm_num⟩
  | 6 => ⟨((524647094145937/9007199254740992), (-386921880068509/9007199254740992)), (68093509/4503599627370496), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1170218949/16777216)), (1/8388608), by norm_num⟩, -11, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile024Terms2
