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
namespace Reinmann.XiBand97.Tile050Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨50,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76013/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76013/2560))
  have he : value ((69/80), (76013/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-320962607/134217728), (-22099031391/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((164792282664861/2251799813685248), (-494786009227283/9007199254740992)), (10781483/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3485879703/17179869184), (1308286771/8589934592)), (115/34359738368), by norm_num⟩
  | 2 => ⟨((302028461/1073741824), (-14509364587/68719476736)), (321/68719476736), by norm_num⟩
  | 3 => ⟨((-17864548369/68719476736), (13409500207/68719476736)), (299/68719476736), by norm_num⟩
  | 4 => ⟨((6191380667/34359738368), (-9294757261/68719476736)), (209/68719476736), by norm_num⟩
  | 5 => ⟨((-6866460885/68719476736), (10308215663/137438953472)), (117/68719476736), by norm_num⟩
  | 6 => ⟨((12691914675/274877906944), (-9526814165/274877906944)), (109/137438953472), by norm_num⟩
  | 7 => ⟨((-10054131283/549755813888), (7546839289/549755813888)), (175/549755813888), by norm_num⟩
  | 8 => ⟨((435562047/68719476736), (-10462140751/2199023255552)), (61/549755813888), by norm_num⟩
  | 9 => ⟨((-17175245075/8796093022208), (6446047435/4398046511104)), (303/8796093022208), by norm_num⟩
  | 10 => ⟨((19047956319/35184372088832), (-14297790737/35184372088832)), (169/17592186044416), by norm_num⟩
  | 11 => ⟨((-4801104443/35184372088832), (7207616973/70368744177664)), (343/140737488355328), by norm_num⟩
  | 12 => ⟨((17748650711/562949953421312), (-13322505023/562949953421312)), (319/562949953421312), by norm_num⟩
  | 13 => ⟨((-15141448861/2251799813685248), (5682742643/1125899906842624)), (137/1125899906842624), by norm_num⟩
  | 14 => ⟨((5997287193/4503599627370496), (-4501688047/4503599627370496)), (219/9007199254740992), by norm_num⟩
  | 15 => ⟨((-17736544891/72057594037927936), (416044317/2251799813685248)), (163/36028797018963968), by norm_num⟩
  | 16 => ⟨((3073509021/72057594037927936), (-4614079125/144115188075855872)), (57/72057594037927936), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (-419374683049/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889140205068015/316912650057057350374175801344), (-992097392133/633825300114114700748351602688)), (5769/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889192573679241/39614081257132168796771975168), (-69742382175/2475880078570760549798248448)), (12981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472233370381115/618970019642690137449562112), (-592665690381/1237940039285380274899124224)), (13793/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13832811842031/1208925819614629174706176), (-1185006266901/154742504910672534362390528)), (6897/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387249943302243/2417851639229258349412352), (-555299032481/4835703278458516698824704)), (12933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258304434108315/604462909807314587353088), (-971428135249/604462909807314587353088)), (5659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887005507080541/75557863725914323419136), (-394480954393/18889465931478580854784)), (18393/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296949870958899/4722366482869645213696), (-1182877118121/4722366482869645213696)), (13797/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620637959813649/590295810358705651712), (-1625537253323/590295810358705651712)), (18973/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455615676219907/18446744073709551616), (-2030544355205/73786976294838206464)), (2965/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910759774357713/4611686018427387904), (-2282470300267/9223372036854775808)), (26691/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592769370227469/1152921504606846976), (-1140053761781/576460752303423488)), (26699/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298379452907139/36028797018963968), (-1992439183623/144115188075855872)), (23371/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490045926481453/36028797018963968), (-186459814175/2251799813685248)), (137/140737488355328), by norm_num⟩
  | 3 => ⟨((1487273493425385/9007199254740992), (-3719936308137/9007199254740992)), (21935/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223995139558997/4503599627370496), (-3706082443331/2251799813685248)), (21957/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105106388319139/1125899906842624), (-11049230053521/2251799813685248)), (131969/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084552062458005/1125899906842624), (-21823898177971/2251799813685248)), (264849/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084552062458005/1125899906842624), (-21823898177971/2251799813685248)), (1010318764693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((261154232805481/281474976710656), (-21022431599775/1125899906842624)), (128845/562949953421312), by norm_num⟩
  | 2 => ⟨((1937619114693843/2251799813685248), (-78018970784583/2251799813685248)), (121949/281474976710656), by norm_num⟩
  | 3 => ⟨((832285545776449/1125899906842624), (-67133431747445/1125899906842624)), (1746551/2251799813685248), by norm_num⟩
  | 4 => ⟨((305618788965051/562949953421312), (-99252490460643/1125899906842624)), (2790447/2251799813685248), by norm_num⟩
  | 5 => ⟨((1292336263998157/4503599627370496), (-431063908995767/4503599627370496)), (3521779/2251799813685248), by norm_num⟩
  | 6 => ⟨((164792282664861/2251799813685248), (-494786009227283/9007199254740992)), (10781483/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-22099031391/268435456)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-655961365/268435456), (-22582242409/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1198968329603421/18014398509481984), (-1004953904773203/18014398509481984)), (35769611/18014398509481984), by norm_num⟩
  | 1 => ⟨((202472989/1073741824), (5430696131/34359738368)), (97/17179869184), by norm_num⟩
  | 2 => ⟨((-2294596697/8589934592), (-7693160373/34359738368)), (69/8589934592), by norm_num⟩
  | 3 => ⟨((17336218617/68719476736), (14530909751/68719476736)), (131/17179869184), by norm_num⟩
  | 4 => ⟨((-1534912685/8589934592), (-2573072963/17179869184)), (373/68719476736), by norm_num⟩
  | 5 => ⟨((3478988081/34359738368), (11664103447/137438953472)), (425/137438953472), by norm_num⟩
  | 6 => ⟨((-13142287273/274877906944), (-5507815589/137438953472)), (101/68719476736), by norm_num⟩
  | 7 => ⟨((10638543907/549755813888), (8917038071/549755813888)), (329/549755813888), by norm_num⟩
  | 8 => ⟨((-1883829035/274877906944), (-6315967813/1099511627776)), (117/549755813888), by norm_num⟩
  | 9 => ⟨((9488514773/4398046511104), (31066813/17179869184)), (37/549755813888), by norm_num⟩
  | 10 => ⟨((-2688298667/4398046511104), (-9013136297/17592186044416)), (337/17592186044416), by norm_num⟩
  | 11 => ⟨((1384822483/8796093022208), (4642934187/35184372088832)), (349/70368744177664), by norm_num⟩
  | 12 => ⟨((-10462660101/281474976710656), (-2192403849/70368744177664)), (83/70368744177664), by norm_num⟩
  | 13 => ⟨((18241814285/2251799813685248), (15289963915/2251799813685248)), (581/2251799813685248), by norm_num⟩
  | 14 => ⟨((-14766557615/9007199254740992), (-1547133207/1125899906842624)), (59/1125899906842624), by norm_num⟩
  | 15 => ⟨((11156482155/36028797018963968), (9351164687/36028797018963968)), (179/18014398509481984), by norm_num⟩
  | 16 => ⟨((-15804347057/288230376151711744), (-13246922287/288230376151711744)), (509/288230376151711744), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-3183582314453/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778192777933221/633825300114114700748351602688), (-3765309565191/633825300114114700748351602688)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944546807591575/19807040628566084398385987584), (-2117529931559/19807040628566084398385987584)), (6511/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888827843197467/2475880078570760549798248448), (-2249313962283/1237940039285380274899124224)), (13839/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885246860616797/77371252455336267181195264), (-4497364629847/154742504910672534362390528)), (13843/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774449812646763/4835703278458516698824704), (-2107468713263/4835703278458516698824704)), (6491/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629108107332973/302231454903657293676544), (-1843364356311/302231454903657293676544)), (11363/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886861045293069/75557863725914323419136), (-5988419582813/75557863725914323419136)), (18473/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296840558660157/4722366482869645213696), (-4489115237837/4722366482869645213696)), (6931/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810243043878033/295147905179352825856), (-3084480427245/295147905179352825856)), (9535/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455567629223935/18446744073709551616), (-7705844809967/73786976294838206464)), (11927/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821300114630887/9223372036854775808), (-8661714843217/9223372036854775808)), (26859/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796272958271669/576460752303423488), (-270391267611/36028797018963968)), (26887/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193317779487127/144115188075855872), (-236269399063/4503599627370496)), (11779/72057594037927936), by norm_num⟩
  | 4 => ⟨((744868443793277/18014398509481984), (-11320283812105/36028797018963968)), (35401/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486871527689573/9007199254740992), (-1764283955709/1125899906842624)), (11091/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223144472340663/4503599627370496), (-14060246423119/2251799813685248)), (11133/562949953421312), by norm_num⟩
  | 1 => ⟨((2208820862890563/2251799813685248), (-41911309306405/2251799813685248)), (134443/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165862179107243/2251799813685248), (-41374537620117/1125899906842624)), (8509/70368744177664), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2165862179107243/2251799813685248), (-41374537620117/1125899906842624)), (32459259301638581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2080163405719509/2251799813685248), (-19897760374801/281474976710656)), (543805/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910356699029447/2251799813685248), (-294097851760261/2251799813685248)), (270399/562949953421312), by norm_num⟩
  | 3 => ⟨((1582276163921341/2251799813685248), (-249503440699243/1125899906842624)), (1058855/1125899906842624), by norm_num⟩
  | 4 => ⟨((1001239087741453/2251799813685248), (-701276098586543/2251799813685248)), (3914695/2251799813685248), by norm_num⟩
  | 5 => ⟨((453585208835049/4503599627370496), (-38976879568535/140737488355328)), (11839113/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1198968329603421/18014398509481984), (-1004953904773203/18014398509481984)), (35769611/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-22582242409/268435456)), (1/134217728), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-5759456469/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-805124180714881/18014398509481984), (39149060168367/562949953421312)), (16851799/9007199254740992), by norm_num⟩
  | 1 => ⟨((8877213263/68719476736), (-6906453727/34359738368)), (187/34359738368), by norm_num⟩
  | 2 => ⟨((-3207305813/17179869184), (1247638675/4294967296)), (543/68719476736), by norm_num⟩
  | 3 => ⟨((3090102047/17179869184), (-9616372241/34359738368)), (263/34359738368), by norm_num⟩
  | 4 => ⟨((-4465771843/34359738368), (13897445369/68719476736)), (191/34359738368), by norm_num⟩
  | 5 => ⟨((5163096325/68719476736), (-16067513441/137438953472)), (111/34359738368), by norm_num⟩
  | 6 => ⟨((-9948845201/274877906944), (15480362357/274877906944)), (215/137438953472), by norm_num⟩
  | 7 => ⟨((8215960341/549755813888), (-12784000617/549755813888)), (357/549755813888), by norm_num⟩
  | 8 => ⟨((-11873589867/2199023255552), (1154703573/137438953472)), (259/1099511627776), by norm_num⟩
  | 9 => ⟨((7626464181/4398046511104), (-11866747009/4398046511104)), (335/4398046511104), by norm_num⟩
  | 10 => ⟨((-8817326673/17592186044416), (13719724165/17592186044416)), (389/17592186044416), by norm_num⟩
  | 11 => ⟨((4633700363/35184372088832), (-7210018773/35184372088832)), (411/70368744177664), by norm_num⟩
  | 12 => ⟨((-8928744443/281474976710656), (13893089757/281474976710656)), (199/140737488355328), by norm_num⟩
  | 13 => ⟨((3970367811/562949953421312), (-12355752081/1125899906842624)), (355/1125899906842624), by norm_num⟩
  | 14 => ⟨((-13115244559/9007199254740992), (20407266779/9007199254740992)), (589/9007199254740992), by norm_num⟩
  | 15 => ⟨((1263597749/4503599627370496), (-3932305837/9007199254740992)), (57/4503599627370496), by norm_num⟩
  | 16 => ⟨((-3652267247/72057594037927936), (11365825735/144115188075855872)), (331/144115188075855872), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (2790200755871/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55566205964323/19807040628566084398385987584), (3299777813979/633825300114114700748351602688)), (11567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889010271294367/39614081257132168796771975168), (927859586089/9903520314283042199192993792)), (13015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888739442475677/2475880078570760549798248448), (3942399569021/2475880078570760549798248448)), (13831/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885202745777803/77371252455336267181195264), (985317692431/38685626227668133590597632)), (6917/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48400534112055/302231454903657293676544), (115429448235/302231454903657293676544)), (6487/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629072089576765/302231454903657293676544), (100963310521/18889465931478580854784)), (2839/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943372163790215/37778931862957161709568), (163995174153/2361183241434822606848)), (4615/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296753317587995/4722366482869645213696), (1966959626981/2361183241434822606848)), (6925/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620366613720913/590295810358705651712), (2702973759825/295147905179352825856)), (19053/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911060948540939/36893488147419103232), (6752649929055/73786976294838206464)), (2979/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910566954793239/4611686018427387904), (7590156927787/9223372036854775808)), (13415/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398095237386807/288230376151711744), (7581945729265/1152921504606846976)), (26855/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298293705766627/36028797018963968), (6624973992111/144115188075855872)), (11763/72057594037927936), by norm_num⟩
  | 4 => ⟨((372381306152319/9007199254740992), (4959513314031/18014398509481984)), (17673/18014398509481984), by norm_num⟩
  | 3 => ⟨((743305890977969/4503599627370496), (12366574157555/9007199254740992)), (5535/1125899906842624), by norm_num⟩
  | 2 => ⟨((2222639410352371/4503599627370496), (24636724784865/4503599627370496)), (11107/562949953421312), by norm_num⟩
  | 1 => ⟨((1104049550516465/1125899906842624), (1147335660013/70368744177664)), (134027/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164560529451717/2251799813685248), (72472368890567/2251799813685248)), (135519/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164560529451717/2251799813685248), (72472368890567/2251799813685248)), (516963963035201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039184303365845/1125899906842624), (139329285154931/2251799813685248)), (269261/1125899906842624), by norm_num⟩
  | 2 => ⟨((119354621068325/140737488355328), (257196586041509/2251799813685248)), (530367/1125899906842624), by norm_num⟩
  | 3 => ⟨((1590152215299073/2251799813685248), (218119574434547/1125899906842624)), (2041455/2251799813685248), by norm_num⟩
  | 4 => ⟨((259601170872705/562949953421312), (616117511653133/2251799813685248)), (1837103/1125899906842624), by norm_num⟩
  | 5 => ⟨((620555605594949/4503599627370496), (1136476352459189/4503599627370496)), (10798573/4503599627370496), by norm_num⟩
  | 6 => ⟨((-805124180714881/18014398509481984), (39149060168367/562949953421312)), (16851799/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-5759456469/67108864)), (1/134217728), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-681712945/268435456), (-11734385433/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((1221557037562239/18014398509481984), (45413726933825/1125899906842624)), (17326539/18014398509481984), by norm_num⟩
  | 1 => ⟨((-13720703723/68719476736), (-2040373959/17179869184)), (197/68719476736), by norm_num⟩
  | 2 => ⟨((2524985929/8589934592), (6007756617/34359738368)), (73/17179869184), by norm_num⟩
  | 3 => ⟨((-19825778643/68719476736), (-737061365/4294967296)), (289/68719476736), by norm_num⟩
  | 4 => ⟨((14593948857/68719476736), (8680928853/68719476736)), (215/68719476736), by norm_num⟩
  | 5 => ⟨((-8594198375/68719476736), (-2556046529/34359738368)), (255/137438953472), by norm_num⟩
  | 6 => ⟨((16870061793/274877906944), (5017415355/137438953472)), (63/68719476736), by norm_num⟩
  | 7 => ⟨((-1774030983/68719476736), (-8441984769/549755813888)), (213/549755813888), by norm_num⟩
  | 8 => ⟨((10447051953/1099511627776), (3107113627/549755813888)), (79/549755813888), by norm_num⟩
  | 9 => ⟨((-854464083/274877906944), (-4066091767/2199023255552)), (209/4398046511104), by norm_num⟩
  | 10 => ⟨((8050935527/8796093022208), (9577887273/17592186044416)), (31/2199023255552), by norm_num⟩
  | 11 => ⟨((-17240355189/70368744177664), (-10255092591/70368744177664)), (67/17592186044416), by norm_num⟩
  | 12 => ⟨((2115132243/35184372088832), (10065164787/281474976710656)), (265/281474976710656), by norm_num⟩
  | 13 => ⟨((-15330160793/1125899906842624), (-9118850317/1125899906842624)), (121/562949953421312), by norm_num⟩
  | 14 => ⟨((12896777999/4503599627370496), (239731235/140737488355328)), (103/2251799813685248), by norm_num⟩
  | 15 => ⟨((-20252680451/36028797018963968), (-12046916145/36028797018963968)), (163/18014398509481984), by norm_num⟩
  | 16 => ⟨((7454097719/72057594037927936), (8867852369/144115188075855872)), (241/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (87374284631/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889026112678739/316912650057057350374175801344), (413294306175/316912650057057350374175801344)), (721/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((236116991206543/4951760157141521099596496896), (464854100797/19807040628566084398385987584)), (12979/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888660877679921/2475880078570760549798248448), (987559188481/2475880078570760549798248448)), (13791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885163701188171/77371252455336267181195264), (246817894597/38685626227668133590597632)), (431/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548744387946761/9671406556917033397649408), (3614303265/37778931862957161709568)), (6465/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258081068012791/604462909807314587353088), (809298593945/604462909807314587353088)), (11315/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471660679274231/18889465931478580854784), (1314537986769/75557863725914323419136)), (4597/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296677935807549/4722366482869645213696), (985403069339/4722366482869645213696)), (13793/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810132152237021/295147905179352825856), (1354116559627/590295810358705651712)), (18967/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821996018633947/73786976294838206464), (1691427623017/73786976294838206464)), (741/2305843009213693952), by norm_num⟩
  | 7 => ⟨((56906095397205/288230376151711744), (475295676395/2305843009213693952)), (26681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796122765495933/576460752303423488), (949546608919/576460752303423488)), (417/18014398509481984), by norm_num⟩
  | 5 => ⟨((596530095061161/72057594037927936), (1659358947919/144115188075855872)), (23359/144115188075855872), by norm_num⟩
  | 4 => ⟨((744680483637233/18014398509481984), (2484350815879/36028797018963968)), (35053/36028797018963968), by norm_num⟩
  | 3 => ⟨((185802483303043/1125899906842624), (96789135817/281474976710656)), (43841/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222295578295985/4503599627370496), (6170014572079/4503599627370496)), (21939/1125899906842624), by norm_num⟩
  | 1 => ⟨((2207682585329901/2251799813685248), (9194035303879/2251799813685248)), (8239/140737488355328), by norm_num⟩
  | 0 => ⟨((2164119858929621/2251799813685248), (18145551627291/2251799813685248)), (264415/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164119858929621/2251799813685248), (18145551627291/2251799813685248)), (1008663186080168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079707740585281/2251799813685248), (4359751296407/281474976710656)), (512501/2251799813685248), by norm_num⟩
  | 2 => ⟨((480056862111375/562949953421312), (32212485188283/1125899906842624)), (60159/140737488355328), by norm_num⟩
  | 3 => ⟨((1635635128207855/2251799813685248), (109877082083871/2251799813685248)), (848351/1125899906842624), by norm_num⟩
  | 4 => ⟨((1182711395246843/2251799813685248), (19952796663931/281474976710656)), (2630443/2251799813685248), by norm_num⟩
  | 5 => ⟨((304939838354813/1125899906842624), (167676716823979/2251799813685248)), (6272197/4503599627370496), by norm_num⟩
  | 6 => ⟨((1221557037562239/18014398509481984), (45413726933825/1125899906842624)), (17326539/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-11734385433/134217728)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-693588655/268435456), (-23877606159/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((93773024645785/2251799813685248), (-1134166585065393/18014398509481984)), (2722475/2251799813685248), by norm_num⟩
  | 1 => ⟨((-8572963755/68719476736), (12961042185/68719476736)), (251/68719476736), by norm_num⟩
  | 2 => ⟨((3210288025/17179869184), (-9706953093/34359738368)), (189/34359738368), by norm_num⟩
  | 3 => ⟨((-801430287/4294967296), (19386288439/68719476736)), (379/68719476736), by norm_num⟩
  | 4 => ⟨((9603482303/68719476736), (-14519032485/68719476736)), (143/34359738368), by norm_num⟩
  | 5 => ⟨((-11507784749/137438953472), (8699026839/68719476736)), (345/137438953472), by norm_num⟩
  | 6 => ⟨((11491414057/274877906944), (-17373303633/274877906944)), (347/274877906944), by norm_num⟩
  | 7 => ⟨((-9835771417/549755813888), (14870218969/549755813888)), (299/549755813888), by norm_num⟩
  | 8 => ⟨((7366334467/1099511627776), (-2718945/268435456)), (113/549755813888), by norm_num⟩
  | 9 => ⟨((-9807807067/4398046511104), (3706985261/1099511627776)), (303/4398046511104), by norm_num⟩
  | 10 => ⟨((11752625665/17592186044416), (-8884108307/8796093022208)), (365/17592186044416), by norm_num⟩
  | 11 => ⟨((-6401403637/35184372088832), (19355934529/70368744177664)), (25/4398046511104), by norm_num⟩
  | 12 => ⟨((6392297157/140737488355328), (-19328399251/281474976710656)), (201/140737488355328), by norm_num⟩
  | 13 => ⟨((-92065437/8796093022208), (17816218287/1125899906842624)), (373/1125899906842624), by norm_num⟩
  | 14 => ⟨((1260815547/562949953421312), (-15249320033/4503599627370496)), (321/4503599627370496), by norm_num⟩
  | 15 => ⟨((-8057740427/18014398509481984), (12182101379/18014398509481984)), (129/9007199254740992), by norm_num⟩
  | 16 => ⟨((12069416525/144115188075855872), (-9123578565/72057594037927936)), (389/144115188075855872), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (-1284922541415/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111123950549531/39614081257132168796771975168), (-1519361128499/633825300114114700748351602688)), (11545/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888858255132877/39614081257132168796771975168), (-1708899345589/39614081257132168796771975168)), (12989/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944289152944655/1237940039285380274899124224), (-907613569835/1237940039285380274899124224)), (6901/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885122391358105/77371252455336267181195264), (-226836146439/19342813113834066795298816)), (13803/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387166720301211/2417851639229258349412352), (-850349860975/4835703278458516698824704)), (6471/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629006599430161/302231454903657293676544), (-743770561059/302231454903657293676544)), (11327/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886532334683293/75557863725914323419136), (-1208091979785/37778931862957161709568)), (2301/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648297532979005/2361183241434822606848), (-452800478625/1180591620717411303424)), (6905/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620150223719503/590295810358705651712), (-1244441252231/295147905179352825856)), (18991/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113865826001327/4611686018427387904), (-3108824620405/73786976294838206464)), (11873/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820834123120829/9223372036854775808), (-3494297477205/9223372036854775808)), (26723/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592084256555333/1152921504606846976), (-3490388793565/1152921504606846976)), (26735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192918688363739/144115188075855872), (-762424636503/36028797018963968)), (11703/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489147944690875/36028797018963968), (-4565778555639/36028797018963968)), (35135/36028797018963968), by norm_num⟩
  | 3 => ⟨((743076124105475/4503599627370496), (-5691908507813/9007199254740992)), (10991/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221756351498141/4503599627370496), (-2834499699593/1125899906842624)), (43/2199023255552), by norm_num⟩
  | 1 => ⟨((2206863872272215/2251799813685248), (-8446445982517/1125899906842624)), (16555/281474976710656), by norm_num⟩
  | 0 => ⟨((2162443556059893/2251799813685248), (-16665992883521/1125899906842624)), (266269/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162443556059893/2251799813685248), (-16665992883521/1125899906842624)), (1015735634810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519034938569727/562949953421312), (-8002325228309/281474976710656)), (519289/2251799813685248), by norm_num⟩
  | 2 => ⟨((239045333412095/281474976710656), (-59024591554509/1125899906842624)), (987087/2251799813685248), by norm_num⟩
  | 3 => ⟨((1617903749479087/2251799813685248), (-200508810162039/2251799813685248)), (890041/1125899906842624), by norm_num⟩
  | 4 => ⟨((286149854880723/562949953421312), (-36016074096951/281474976710656)), (1437483/1125899906842624), by norm_num⟩
  | 5 => ⟨((544937315359779/2251799813685248), (-146456988776093/1125899906842624)), (7316893/4503599627370496), by norm_num⟩
  | 6 => ⟨((93773024645785/2251799813685248), (-1134166585065393/18014398509481984)), (2722475/2251799813685248), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-23877606159/268435456)), (1/134217728), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-352442413/134217728), (-24266490151/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-991736695324865/18014398509481984), (-846351500159105/18014398509481984)), (7475399/4503599627370496), by norm_num⟩
  | 1 => ⟨((11517961965/68719476736), (9829468279/68719476736)), (349/68719476736), by norm_num⟩
  | 2 => ⟨((-4383336705/17179869184), (-14963018363/68719476736)), (267/34359738368), by norm_num⟩
  | 3 => ⟨((8896777967/34359738368), (7592540857/34359738368)), (17/2147483648), by norm_num⟩
  | 4 => ⟨((-1692902509/8589934592), (-11557830499/68719476736)), (13/2147483648), by norm_num⟩
  | 5 => ⟨((16493054955/137438953472), (7037614857/68719476736)), (509/137438953472), by norm_num⟩
  | 6 => ⟨((-4184456323/68719476736), (-1785514695/34359738368)), (519/274877906944), by norm_num⟩
  | 7 => ⟨((14559624189/549755813888), (12425233261/549755813888)), (227/274877906944), by norm_num⟩
  | 8 => ⟨((-692610977/68719476736), (-2364306341/274877906944)), (347/1099511627776), by norm_num⟩
  | 9 => ⟨((7497492125/2199023255552), (12796771031/4398046511104)), (59/549755813888), by norm_num⟩
  | 10 => ⟨((-18261026401/17592186044416), (-7792011307/8796093022208)), (577/17592186044416), by norm_num⟩
  | 11 => ⟨((10108382657/35184372088832), (4313264229/17592186044416)), (321/35184372088832), by norm_num⟩
  | 12 => ⟨((-10258399269/140737488355328), (-4377276575/70368744177664)), (41/17592186044416), by norm_num⟩
  | 13 => ⟨((9609823615/562949953421312), (8201056461/562949953421312)), (309/562949953421312), by norm_num⟩
  | 14 => ⟨((-16718470639/4503599627370496), (-7133800117/2251799813685248)), (135/1125899906842624), by norm_num⟩
  | 15 => ⟨((13573269063/18014398509481984), (2895868603/4503599627370496)), (55/2251799813685248), by norm_num⟩
  | 16 => ⟨((-5165515277/36028797018963968), (-8816536939/72057594037927936)), (337/72057594037927936), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (-396502943259/1267650600228229401496703205376)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777912088352939/633825300114114700748351602688), (-3750509565365/633825300114114700748351602688)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888777915573369/39614081257132168796771975168), (-1054587781257/9903520314283042199192993792)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944246251782873/1237940039285380274899124224), (-4480796200237/2475880078570760549798248448)), (13839/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770158484223135/154742504910672534362390528), (-4479444472803/154742504910672534362390528)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387146362405953/2417851639229258349412352), (-2099021698301/4835703278458516698824704)), (6491/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314485354993557/151115727451828646838272), (-3671852640417/604462909807314587353088)), (11363/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471603677078109/18889465931478580854784), (-5964070282015/75557863725914323419136)), (2309/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296505984751077/4722366482869645213696), (-4470699723167/4722366482869645213696)), (13861/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620026339190335/590295810358705651712), (-95990474461/9223372036854775808)), (19069/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821696266968195/73786976294838206464), (-7673508566947/73786976294838206464)), (11927/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820654682562339/9223372036854775808), (-1078103061505/1152921504606846976)), (26857/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591901233202887/1152921504606846976), (-2153747895291/288230376151711744)), (13443/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192754523679375/144115188075855872), (-3763533231715/72057594037927936)), (11779/72057594037927936), by norm_num⟩
  | 4 => ⟨((372223421897271/9007199254740992), (-5634262241533/18014398509481984)), (4425/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485820473014211/9007199254740992), (-14047084997357/9007199254740992)), (44361/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221051194156425/4503599627370496), (-13989351057669/2251799813685248)), (89059/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205703006358143/2251799813685248), (-20840118363345/1125899906842624)), (134433/2251799813685248), by norm_num⟩
  | 0 => ⟨((539928650741869/562949953421312), (-2569197588517/70368744177664)), (136131/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((539928650741869/562949953421312), (-2569197588517/70368744177664)), (519298557761764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((517098360951723/562949953421312), (-78852246329987/1125899906842624)), (271069/1125899906842624), by norm_num⟩
  | 2 => ⟨((236110061023653/281474976710656), (-72429826287031/562949953421312)), (1071901/2251799813685248), by norm_num⟩
  | 3 => ⟨((96698544252051/140737488355328), (-7594551967111/35184372088832)), (1037057/1125899906842624), by norm_num⟩
  | 4 => ⟨((479063427699627/1125899906842624), (-166979161682817/562949953421312)), (3745579/2251799813685248), by norm_num⟩
  | 5 => ⟨((209563221911911/2251799813685248), (-1136777563462211/4503599627370496)), (1352357/562949953421312), by norm_num⟩
  | 6 => ⟨((-991736695324865/18014398509481984), (-846351500159105/18014398509481984)), (7475399/4503599627370496), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-24266490151/268435456)), (1/134217728), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile050Terms2
