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
namespace Reinmann.XiBand97.Tile014Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26103/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26103/1280))
  have he : value ((69/80), (26103/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1897211715/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((824184690429349/9007199254740992), (12120013303623/18014398509481984)), (102768669/18014398509481984), by norm_num⟩
  | 1 => ⟨((-272408149/1073741824), (-8011773/4294967296)), (69/4294967296), by norm_num⟩
  | 2 => ⟨((377637881/1073741824), (2776669/1073741824)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((-174505755/536870912), (-2566187/1073741824)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((1935330753/8589934592), (7114981/4294967296)), (65/4294967296), by norm_num⟩
  | 5 => ⟨((-268293811/2147483648), (-3945383/4294967296)), (37/4294967296), by norm_num⟩
  | 6 => ⟨((495912263/8589934592), (14585233/34359738368)), (35/8589934592), by norm_num⟩
  | 7 => ⟨((-49105741/2147483648), (-5776979/34359738368)), (113/68719476736), by norm_num⟩
  | 8 => ⟨((544600095/68719476736), (8008593/137438953472)), (5/8589934592), by norm_num⟩
  | 9 => ⟨((-335544907/137438953472), (-4934341/274877906944)), (25/137438953472), by norm_num⟩
  | 10 => ⟨((186065605/274877906944), (10944719/2199023255552)), (113/2199023255552), by norm_num⟩
  | 11 => ⟨((-1500751703/8796093022208), (-2758655/2199023255552)), (29/2199023255552), by norm_num⟩
  | 12 => ⟨((693494541/17592186044416), (5099077/17592186044416)), (109/35184372088832), by norm_num⟩
  | 13 => ⟨((-591623121/70368744177664), (-1087511/17592186044416)), (95/140737488355328), by norm_num⟩
  | 14 => ⟨((1874660107/1125899906842624), (6891933/562949953421312)), (153/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1386043059/4503599627370496), (-5095599/2251799813685248)), (115/4503599627370496), by norm_num⟩
  | 16 => ⟨((1921463677/36028797018963968), (110375/281474976710656)), (81/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (9577577829/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778280937467159/633825300114114700748351602688), (11328640439/633825300114114700748351602688)), (92201/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889193196191151/39614081257132168796771975168), (12742081365/39614081257132168796771975168)), (103727/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888934181637309/2475880078570760549798248448), (13535160505/2475880078570760549798248448)), (55105/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885300329689297/77371252455336267181195264), (13531448625/154742504910672534362390528)), (55105/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774500258251249/4835703278458516698824704), (6340895327/4835703278458516698824704)), (103323/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258305130621877/604462909807314587353088), (11092626013/604462909807314587353088)), (90407/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471751681332797/18889465931478580854784), (18018131697/75557863725914323419136)), (4591/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648475430090083/2361183241434822606848), (13507139839/4722366482869645213696)), (110185/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620639442583087/590295810358705651712), (4640456991/147573952589676412928)), (9469/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822464741962075/73786976294838206464), (2898320283/9223372036854775808)), (47345/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821522092482047/9223372036854775808), (26063282167/9223372036854775808)), (106527/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796386114205901/576460752303423488), (3254538643/144115188075855872)), (3329/18014398509481984), by norm_num⟩
  | 5 => ⟨((596760332688309/72057594037927936), (22751463555/144115188075855872)), (186425/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490050910573649/36028797018963968), (8516668893/9007199254740992)), (279641/36028797018963968), by norm_num⟩
  | 3 => ⟨((743640474833883/4503599627370496), (21238823167/4503599627370496)), (349559/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112006855351939/2251799813685248), (84639042315/4503599627370496)), (699141/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210249711254549/2251799813685248), (31542720967/562949953421312)), (1048779/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169213895414371/2251799813685248), (249208664201/2251799813685248)), (1048941/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2169213895414371/2251799813685248), (249208664201/2251799813685248)), (4001392368796920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2089656830663347/2251799813685248), (480137616103/2251799813685248)), (1010587/562949953421312), by norm_num⟩
  | 2 => ⟨((969594502332661/1125899906842624), (891129702605/2251799813685248)), (7504275/2251799813685248), by norm_num⟩
  | 3 => ⟨((834988345511153/1125899906842624), (767416761703/1125899906842624)), (12930897/2251799813685248), by norm_num⟩
  | 4 => ⟨((154810597277281/281474976710656), (569130566827/562949953421312)), (19197217/2251799813685248), by norm_num⟩
  | 5 => ⟨((1362323021791551/4503599627370496), (626041035753/562949953421312)), (5288917/562949953421312), by norm_num⟩
  | 6 => ⟨((824184690429349/9007199254740992), (12120013303623/18014398509481984)), (102768669/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1897211715/33554432)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-1938695597/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((262210677227843/9007199254740992), (-736959902979265/9007199254740992)), (223942591/18014398509481984), by norm_num⟩
  | 1 => ⟨((-88560437/1073741824), (995619121/4294967296)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((62727653/536870912), (-705200345/2147483648)), (219/4294967296), by norm_num⟩
  | 3 => ⟨((-118480549/1073741824), (1331988685/4294967296)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((10490021/134217728), (-943452029/4294967296)), (75/2147483648), by norm_num⟩
  | 5 => ⟨((-11888187/268435456), (1069200351/8589934592)), (43/2147483648), by norm_num⟩
  | 6 => ⟨((179636107/8589934592), (-1009757567/17179869184)), (41/4294967296), by norm_num⟩
  | 7 => ⟨((-290827095/34359738368), (817388175/34359738368)), (135/34359738368), by norm_num⟩
  | 8 => ⟨((411987603/137438953472), (-578958771/68719476736)), (193/137438953472), by norm_num⟩
  | 9 => ⟨((-518777233/549755813888), (364514159/137438953472)), (245/549755813888), by norm_num⟩
  | 10 => ⟨((73490329/274877906944), (-51637319/68719476736)), (141/1099511627776), by norm_num⟩
  | 11 => ⟨((-37857051/549755813888), (851197331/4398046511104)), (147/4398046511104), by norm_num⟩
  | 12 => ⟨((286018939/17592186044416), (-401937273/8796093022208)), (141/17592186044416), by norm_num⟩
  | 13 => ⟨((-498678569/140737488355328), (175196007/17592186044416)), (31/17592186044416), by norm_num⟩
  | 14 => ⟨((403675079/562949953421312), (-1134554663/562949953421312)), (203/562949953421312), by norm_num⟩
  | 15 => ⟨((-19061627/140737488355328), (107147847/281474976710656)), (155/2251799813685248), by norm_num⟩
  | 16 => ⟨((6750707/281474976710656), (-151786355/2251799813685248)), (111/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-800431040235/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889099227470139/316912650057057350374175801344), (-946691605345/316912650057057350374175801344)), (92387/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889100315987609/39614081257132168796771975168), (-1064801811985/19807040628566084398385987584)), (103947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888835379217003/2475880078570760549798248448), (-1131069923421/1237940039285380274899124224)), (55229/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885250862629051/77371252455336267181195264), (-282688199937/19342813113834066795298816)), (55237/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548907625948559/9671406556917033397649408), (-16558498769/75557863725914323419136)), (51793/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629111855850615/302231454903657293676544), (-463469616153/151115727451828646838272)), (45327/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((14741204358985/590295810358705651712), (-1505645218017/37778931862957161709568)), (147343/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648425602994767/2361183241434822606848), (-2257364067813/4722366482869645213696)), (110535/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810251023511847/295147905179352825856), (-3102083017353/590295810358705651712)), (76015/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911146220922653/36893488147419103232), (-968729178559/18446744073709551616)), (23763/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821327492274015/9223372036854775808), (-544448691609/1152921504606846976)), (106979/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796288338589513/576460752303423488), (-2175489608043/576460752303423488)), (214073/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149168561394945/18014398509481984), (-950481561799/36028797018963968)), (187443/144115188075855872), by norm_num⟩
  | 4 => ⟨((744895261495991/18014398509481984), (-5692543318687/36028797018963968)), (281423/36028797018963968), by norm_num⟩
  | 3 => ⟨((743475880560797/4503599627370496), (-7097607443875/9007199254740992)), (44029/1125899906842624), by norm_num⟩
  | 2 => ⟨((555836072177147/1125899906842624), (-14141135086327/4503599627370496)), (705829/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209218200618345/2251799813685248), (-10538487831519/1125899906842624)), (1062163/2251799813685248), by norm_num⟩
  | 0 => ⟨((541760690917515/562949953421312), (-10404467564543/562949953421312)), (2138077/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541760690917515/562949953421312), (-10404467564543/562949953421312)), (8156116494185637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((521176689854957/562949953421312), (-80102772932317/2251799813685248)), (2097117/1125899906842624), by norm_num⟩
  | 2 => ⟨((481790809307911/562949953421312), (-148317617903147/2251799813685248)), (8064411/2251799813685248), by norm_num⟩
  | 3 => ⟨((409889902814507/562949953421312), (-253870045569395/2251799813685248)), (14865915/2251799813685248), by norm_num⟩
  | 4 => ⟨((145644924944353/281474976710656), (-184845504779847/1125899906842624)), (6250015/562949953421312), by norm_num⟩
  | 5 => ⟨((67774951418947/281474976710656), (-765163851780297/4503599627370496)), (1065019/70368744177664), by norm_num⟩
  | 6 => ⟨((262210677227843/9007199254740992), (-736959902979265/9007199254740992)), (223942591/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-1938695597/33554432)), (1/16777216), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-1977807641/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1092657384867527/18014398509481984), (-1011808910626047/18014398509481984)), (272766053/18014398509481984), by norm_num⟩
  | 1 => ⟨((376485115/2147483648), (5447313/33554432)), (95/2147483648), by norm_num⟩
  | 2 => ⟨((-136022743/536870912), (-503832309/2147483648)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((524208393/2147483648), (970841785/4294967296)), (269/4294967296), by norm_num⟩
  | 4 => ⟨((-757578567/4294967296), (-701523419/4294967296)), (49/1073741824), by norm_num⟩
  | 5 => ⟨((437936739/4294967296), (811065391/8589934592)), (229/8589934592), by norm_num⟩
  | 6 => ⟨((-843866655/17179869184), (-781426833/17179869184)), (223/17179869184), by norm_num⟩
  | 7 => ⟨((696882385/34359738368), (161329575/8589934592)), (93/17179869184), by norm_num⟩
  | 8 => ⟨((-503562291/68719476736), (-932604895/137438953472)), (271/137438953472), by norm_num⟩
  | 9 => ⟨((646880989/274877906944), (599016633/274877906944)), (11/17179869184), by norm_num⟩
  | 10 => ⟨((-747890617/1099511627776), (-43284519/68719476736)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((98258269/549755813888), (727903135/4398046511104)), (109/2199023255552), by norm_num⟩
  | 12 => ⟨((-757341135/17592186044416), (-701303555/17592186044416)), (53/4398046511104), by norm_num⟩
  | 13 => ⟨((336768835/35184372088832), (77962615/8796093022208)), (95/35184372088832), by norm_num⟩
  | 14 => ⟨((-556221217/281474976710656), (-515065007/281474976710656)), (79/140737488355328), by norm_num⟩
  | 15 => ⟨((857432585/2251799813685248), (793988987/2251799813685248)), (123/1125899906842624), by norm_num⟩
  | 16 => ⟨((-154893683/2251799813685248), (-143432709/2251799813685248)), (179/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-3119224965957/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778117133191683/633825300114114700748351602688), (-461111504155/79228162514264337593543950336)), (23141/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889008550961361/39614081257132168796771975168), (-518636589499/4951760157141521099596496896)), (52079/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888737507728941/2475880078570760549798248448), (-1101822147915/618970019642690137449562112)), (110695/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770403436672693/154742504910672534362390528), (-4406026182913/154742504910672534362390528)), (110725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548815037586201/9671406556917033397649408), (-4129308593455/9671406556917033397649408)), (103837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157267781808395/75557863725914323419136), (-3611804466669/604462909807314587353088)), (45445/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886740961254935/75557863725914323419136), (-5866669573049/75557863725914323419136)), (36939/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296750584206125/4722366482869645213696), (-4397804430947/4722366482869645213696)), (110871/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620362516722241/590295810358705651712), (-6043411345785/590295810358705651712)), (152533/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822116268701061/73786976294838206464), (-7548912353247/73786976294838206464)), (47699/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821126881593557/9223372036854775808), (-2121293041927/2305843009213693952)), (214823/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592373053335619/1152921504606846976), (-529749136405/72057594037927936)), (215047/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193166939692185/144115188075855872), (-1851540756873/36028797018963968)), (188417/144115188075855872), by norm_num⟩
  | 4 => ⟨((186188932193961/4503599627370496), (-5544309075335/18014398509481984)), (35391/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486591188973509/9007199254740992), (-13824729084133/9007199254740992)), (44349/1125899906842624), by norm_num⟩
  | 2 => ⟨((2222588129100847/4503599627370496), (-13770768806683/2251799813685248)), (356117/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207997140507495/2251799813685248), (-20521620331577/1125899906842624)), (1074995/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164257646321377/2251799813685248), (-81014629866225/2251799813685248)), (1088339/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164257646321377/2251799813685248), (-81014629866225/2251799813685248)), (4151683811668014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2077204092913203/2251799813685248), (-155730124042351/2251799813685248)), (4340737/2251799813685248), by norm_num⟩
  | 2 => ⟨((1905375844693465/2251799813685248), (-287310842717627/2251799813685248)), (8608741/2251799813685248), by norm_num⟩
  | 3 => ⟨((1575588366086499/2251799813685248), (-30388754825455/140737488355328)), (8382749/1125899906842624), by norm_num⟩
  | 4 => ⟨((997454890180403/2251799813685248), (-85052264898241/281474976710656)), (15350941/1125899906842624), by norm_num⟩
  | 5 => ⟨((472464237536027/4503599627370496), (-1205589193541379/4503599627370496)), (45753499/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1092657384867527/18014398509481984), (-1011808910626047/18014398509481984)), (272766053/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1977807641/33554432)), (1/16777216), by norm_num⟩, -9, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-2014804461/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-666206059822427/9007199254740992), (247414451155297/9007199254740992)), (126119107/9007199254740992), by norm_num⟩
  | 1 => ⟨((935365243/4294967296), (-173687161/2147483648)), (179/4294967296), by norm_num⟩
  | 2 => ⟨((-1377062941/4294967296), (511411247/4294967296)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((1351559267/4294967296), (-501939737/4294967296)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((-994895947/4294967296), (92370683/1073741824)), (195/4294967296), by norm_num⟩
  | 5 => ⟨((1171764163/8589934592), (-435167743/8589934592)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((-287515673/4294967296), (6673567/268435456)), (115/8589934592), by norm_num⟩
  | 7 => ⟨((483755631/17179869184), (-359312655/34359738368)), (49/8589934592), by norm_num⟩
  | 8 => ⟨((-178048617/17179869184), (264493547/68719476736)), (291/137438953472), by norm_num⟩
  | 9 => ⟨((932005845/274877906944), (-346126715/274877906944)), (3/4294967296), by norm_num⟩
  | 10 => ⟨((-1097693735/1099511627776), (407659597/1099511627776)), (229/1099511627776), by norm_num⟩
  | 11 => ⟨((587653131/2199023255552), (-436483203/4398046511104)), (247/4398046511104), by norm_num⟩
  | 12 => ⟨((-576769595/8796093022208), (214199693/8796093022208)), (61/4398046511104), by norm_num⟩
  | 13 => ⟨((65317803/4398046511104), (-48515225/8796093022208)), (223/70368744177664), by norm_num⟩
  | 14 => ⟨((-219799183/70368744177664), (326514559/281474976710656)), (189/281474976710656), by norm_num⟩
  | 15 => ⟨((1380661935/2251799813685248), (-512747837/2251799813685248)), (299/2251799813685248), by norm_num⟩
  | 16 => ⟨((-1016318705/9007199254740992), (377438679/9007199254740992)), (111/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (3629077331047/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444510679503461/158456325028528675187087900672), (4291528691579/633825300114114700748351602688)), (92623/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888924710417731/39614081257132168796771975168), (2413442419371/19807040628566084398385987584)), (26057/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944324130091861/1237940039285380274899124224), (2563617106937/1237940039285380274899124224)), (55387/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442578500375493/38685626227668133590597632), (5125737190951/154742504910672534362390528)), (110809/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774365496468511/4835703278458516698824704), (4803788403371/9671406556917033397649408)), (51961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314517129104955/151115727451828646838272), (131303908111/18889465931478580854784)), (90969/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886620764260873/75557863725914323419136), (6824823251265/75557863725914323419136)), (147895/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648330055397819/2361183241434822606848), (639501357067/590295810358705651712)), (110983/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620237587361981/590295810358705651712), (7030280905507/590295810358705651712)), (76351/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455489828935387/18446744073709551616), (137210984807/1152921504606846976)), (47757/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820949223760213/9223372036854775808), (9870467023887/9223372036854775808)), (107557/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398048510411859/288230376151711744), (1232446164381/144115188075855872)), (107687/576460752303423488), by norm_num⟩
  | 5 => ⟨((596504392980695/72057594037927936), (8614873054793/144115188075855872)), (188745/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489271201387771/36028797018963968), (12897833967783/36028797018963968)), (141851/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486285599714285/9007199254740992), (4019878865821/2251799813685248)), (177827/4503599627370496), by norm_num⟩
  | 2 => ⟨((555490311481835/1125899906842624), (8007730349865/1125899906842624)), (89299/562949953421312), by norm_num⟩
  | 1 => ⟨((551754477941969/562949953421312), (23863442026355/1125899906842624)), (539661/1125899906842624), by norm_num⟩
  | 0 => ⟨((270268213740311/281474976710656), (23545108922105/562949953421312)), (1094855/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((270268213740311/281474976710656), (23545108922105/562949953421312)), (4176540379050826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1036061040620097/1125899906842624), (90430696256737/1125899906842624)), (2194113/1125899906842624), by norm_num⟩
  | 2 => ⟨((946127415582261/1125899906842624), (83214964934579/562949953421312)), (8781067/2251799813685248), by norm_num⟩
  | 3 => ⟨((385228811055123/562949953421312), (559424220450365/2251799813685248)), (17354013/2251799813685248), by norm_num⟩
  | 4 => ⟨((114434258260665/281474976710656), (765632276936163/2251799813685248)), (32373499/2251799813685248), by norm_num⟩
  | 5 => ⟨((223732128102525/4503599627370496), (1245077807419845/4503599627370496)), (48337597/2251799813685248), by norm_num⟩
  | 6 => ⟨((-666206059822427/9007199254740992), (247414451155297/9007199254740992)), (126119107/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-2014804461/33554432)), (1/16777216), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1024951577/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-228961265079331/18014398509481984), (1340405497479443/18014398509481984)), (57671267/4503599627370496), by norm_num⟩
  | 1 => ⟨((163532889/4294967296), (-957368853/4294967296)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((-244950377/4294967296), (1434010385/4294967296)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((244601917/4294967296), (-1431970397/4294967296)), (253/4294967296), by norm_num⟩
  | 4 => ⟨((-2862351/67108864), (1072449983/4294967296)), (191/4294967296), by norm_num⟩
  | 5 => ⟨((109757917/4294967296), (-642554605/4294967296)), (231/8589934592), by norm_num⟩
  | 6 => ⟨((-54800889/4294967296), (1283281045/17179869184)), (233/17179869184), by norm_num⟩
  | 7 => ⟨((46905369/8589934592), (-274597603/8589934592)), (201/34359738368), by norm_num⟩
  | 8 => ⟨((-281031855/137438953472), (1645241803/137438953472)), (19/8589934592), by norm_num⟩
  | 9 => ⟨((46772011/68719476736), (-273816887/68719476736)), (51/68719476736), by norm_num⟩
  | 10 => ⟨((-224186277/1099511627776), (1312451337/1099511627776)), (123/549755813888), by norm_num⟩
  | 11 => ⟨((244218933/4398046511104), (-1429728301/4398046511104)), (135/2199023255552), by norm_num⟩
  | 12 => ⟨((-243871513/17592186044416), (1427694405/17592186044416)), (17/1099511627776), by norm_num⟩
  | 13 => ⟨((224791927/70368744177664), (-1315996987/70368744177664)), (253/70368744177664), by norm_num⟩
  | 14 => ⟨((-96202347/140737488355328), (281598189/70368744177664)), (109/140737488355328), by norm_num⟩
  | 15 => ⟨((153704787/1125899906842624), (-449916151/562949953421312)), (175/1125899906842624), by norm_num⟩
  | 16 => ⟨((-57557299/2251799813685248), (673914167/4503599627370496)), (33/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1133258076093/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444495148823757/158456325028528675187087900672), (670012476965/158456325028528675187087900672)), (92465/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888855171388557/39614081257132168796771975168), (11774914131/154742504910672534362390528)), (13005/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944287418911981/1237940039285380274899124224), (1600966120863/1237940039285380274899124224)), (55281/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442560274838645/38685626227668133590597632), (3200982651359/154742504910672534362390528)), (13823/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774331599741105/4835703278458516698824704), (2999912634889/9671406556917033397649408)), (6481/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258009748985905/604462909807314587353088), (2623915336091/604462909807314587353088)), (90757/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886526300882209/75557863725914323419136), (4261972819737/75557863725914323419136)), (147525/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162073770844283/590295810358705651712), (3194827023293/4722366482869645213696)), (110683/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620142880614155/590295810358705651712), (2195101606699/295147905179352825856)), (152251/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455460782126677/18446744073709551616), (5483730755735/73786976294838206464)), (190407/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910410763798719/4611686018427387904), (6163669427289/9223372036854775808)), (107169/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592070105641073/1152921504606846976), (6156766298287/1152921504606846976)), (53625/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192904561229541/144115188075855872), (5379413369283/144115188075855872)), (93935/72057594037927936), by norm_num⟩
  | 4 => ⟨((744561637811951/18014398509481984), (8053627945423/36028797018963968)), (282171/36028797018963968), by norm_num⟩
  | 3 => ⟨((371528837807253/2251799813685248), (2509993394381/2251799813685248)), (353355/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110832240617239/2251799813685248), (19998962145045/4503599627370496)), (708639/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103340622219457/1125899906842624), (7449169018535/562949953421312)), (533897/1125899906842624), by norm_num⟩
  | 0 => ⟨((2161901208982445/2251799813685248), (58790445447053/2251799813685248)), (2155023/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161901208982445/2251799813685248), (58790445447053/2251799813685248)), (8220760354048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2074056713452019/2251799813685248), (56443354474123/1125899906842624)), (531313/281474976710656), by norm_num⟩
  | 2 => ⟨((59521385619685/70368744177664), (51988066419287/562949953421312)), (8256163/2251799813685248), by norm_num⟩
  | 3 => ⟨((1591872540271079/2251799813685248), (351792749479975/2251799813685248)), (15491851/2251799813685248), by norm_num⟩
  | 4 => ⟨((267597060719373/562949953421312), (497388102050809/2251799813685248)), (13371959/1125899906842624), by norm_num⟩
  | 5 => ⟨((797882707840233/4503599627370496), (945729497527623/4503599627370496)), (74479947/4503599627370496), by norm_num⟩
  | 6 => ⟨((-228961265079331/18014398509481984), (1340405497479443/18014398509481984)), (57671267/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1024951577/16777216)), (1/16777216), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1041644509/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((479196944558837/9007199254740992), (883930773300715/18014398509481984)), (291984703/18014398509481984), by norm_num⟩
  | 1 => ⟨((-86958757/536870912), (-641619461/4294967296)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((264747887/1073741824), (976712423/4294967296)), (41/536870912), by norm_num⟩
  | 3 => ⟨((-1074707843/4294967296), (-991207629/4294967296)), (335/4294967296), by norm_num⟩
  | 4 => ⟨((204498259/1073741824), (754438467/4294967296)), (257/4294967296), by norm_num⟩
  | 5 => ⟨((-996159261/8589934592), (-57422621/536870912)), (315/8589934592), by norm_num⟩
  | 6 => ⟨((505471537/8589934592), (466198555/8589934592)), (161/8589934592), by norm_num⟩
  | 7 => ⟨((-879382535/34359738368), (-101382283/4294967296)), (141/17179869184), by norm_num⟩
  | 8 => ⟨((669324965/68719476736), (617321271/68719476736)), (27/8589934592), by norm_num⟩
  | 9 => ⟨((-452838861/137438953472), (-835310427/274877906944)), (147/137438953472), by norm_num⟩
  | 10 => ⟨((1102942459/1099511627776), (1017248535/1099511627776)), (45/137438953472), by norm_num⟩
  | 11 => ⟨((-152633321/549755813888), (-563097453/2199023255552)), (201/2199023255552), by norm_num⟩
  | 12 => ⟨((309797047/4398046511104), (571454277/8796093022208)), (205/8796093022208), by norm_num⟩
  | 13 => ⟨((-580420961/35184372088832), (-535324729/35184372088832)), (97/17592186044416), by norm_num⟩
  | 14 => ⟨((1972215/549755813888), (465659471/140737488355328)), (85/70368744177664), by norm_num⟩
  | 15 => ⟨((-409903979/562949953421312), (-378056189/562949953421312)), (139/562949953421312), by norm_num⟩
  | 16 => ⟨((623980931/4503599627370496), (575500275/4503599627370496)), (213/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (485224227523/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444479731379179/158456325028528675187087900672), (573715194787/316912650057057350374175801344)), (92313/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888785982108483/39614081257132168796771975168), (1290566747453/39614081257132168796771975168)), (207719/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944250787680111/1237940039285380274899124224), (1370860039957/2475880078570760549798248448)), (110359/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885084059565669/77371252455336267181195264), (1370447221753/154742504910672534362390528)), (220737/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774297540088219/4835703278458516698824704), (1284355822345/9671406556917033397649408)), (103481/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257950443991285/604462909807314587353088), (561686544645/302231454903657293676544)), (22639/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886430491094337/75557863725914323419136), (1824659950943/75557863725914323419136)), (36793/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648259399797949/2361183241434822606848), (683888359089/2361183241434822606848)), (27599/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810022773151067/295147905179352825856), (1879526606133/590295810358705651712)), (151821/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821722652136807/73786976294838206464), (2347660026555/73786976294838206464)), (189817/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227585953392371/1152921504606846976), (659678972313/2305843009213693952)), (6675/144115188075855872), by norm_num⟩
  | 6 => ⟨((795969122593479/576460752303423488), (1317858550485/576460752303423488)), (106835/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192791472409991/144115188075855872), (1151441653599/72057594037927936)), (5845/2251799813685248), by norm_num⟩
  | 4 => ⟨((1488958205761739/36028797018963968), (3447597834399/36028797018963968)), (140359/9007199254740992), by norm_num⟩
  | 3 => ⟨((371479241650079/2251799813685248), (4297749946783/9007199254740992)), (351175/4503599627370496), by norm_num⟩
  | 2 => ⟨((277661429712689/562949953421312), (8560358138729/4503599627370496)), (43949/140737488355328), by norm_num⟩
  | 1 => ⟨((2206180531948947/2251799813685248), (3188258210951/562949953421312)), (2113749/2251799813685248), by norm_num⟩
  | 0 => ⟨((540283110151949/562949953421312), (12579070311659/1125899906842624)), (4244419/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((540283110151949/562949953421312), (12579070311659/1125899906842624)), (16191173562056731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2073834656805123/2251799813685248), (48290326267897/2251799813685248)), (4120941/1125899906842624), by norm_num⟩
  | 2 => ⟨((1908898918114837/2251799813685248), (22236912800631/562949953421312)), (970907/140737488355328), by norm_num⟩
  | 3 => ⟨((1614700992880435/2251799813685248), (75402828491879/1125899906842624)), (13782563/1125899906842624), by norm_num⟩
  | 4 => ⟨((143469511284009/281474976710656), (216276813403891/2251799813685248)), (43224459/2251799813685248), by norm_num⟩
  | 5 => ⟨((1128491418303393/4503599627370496), (440950440195125/4503599627370496)), (6545829/281474976710656), by norm_num⟩
  | 6 => ⟨((479196944558837/9007199254740992), (883930773300715/18014398509481984)), (291984703/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1041644509/16777216)), (1/8388608), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile014Terms2
