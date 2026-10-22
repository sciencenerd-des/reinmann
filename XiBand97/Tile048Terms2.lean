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
namespace Reinmann.XiBand97.Tile048Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨48,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37559/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37559/1280))
  have he : value ((69/80), (37559/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-320962607/134217728), (-10919415363/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((1561896962622551/18014398509481984), (131754133975903/4503599627370496)), (17093323/18014398509481984), by norm_num⟩
  | 1 => ⟨((-16519538513/68719476736), (-5574036041/68719476736)), (91/34359738368), by norm_num⟩
  | 2 => ⟨((22900943089/68719476736), (1931813683/17179869184)), (255/68719476736), by norm_num⟩
  | 3 => ⟨((-21164965513/68719476736), (-7141499775/68719476736)), (119/34359738368), by norm_num⟩
  | 4 => ⟨((3667609043/17179869184), (2475055217/34359738368)), (167/68719476736), by norm_num⟩
  | 5 => ⟨((-16270034353/137438953472), (-5489848145/137438953472)), (187/137438953472), by norm_num⟩
  | 6 => ⟨((7518352293/137438953472), (2536848509/137438953472)), (87/137438953472), by norm_num⟩
  | 7 => ⟨((-23823198603/1099511627776), (-8038442933/1099511627776)), (139/549755813888), by norm_num⟩
  | 8 => ⟨((516030717/68719476736), (5571824055/2199023255552)), (97/1099511627776), by norm_num⟩
  | 9 => ⟨((-20348315681/8796093022208), (-858243141/1099511627776)), (241/8796093022208), by norm_num⟩
  | 10 => ⟨((11283502115/17592186044416), (1903644203/8796093022208)), (269/35184372088832), by norm_num⟩
  | 11 => ⟨((-22752371427/140737488355328), (-7677123561/140737488355328)), (137/70368744177664), by norm_num⟩
  | 12 => ⟨((21027656141/562949953421312), (7095168735/562949953421312)), (255/562949953421312), by norm_num⟩
  | 13 => ⟨((-8969391119/1125899906842624), (-6052918405/2251799813685248)), (55/562949953421312), by norm_num⟩
  | 14 => ⟨((7105266475/4503599627370496), (1198732379/2251799813685248)), (11/562949953421312), by norm_num⟩
  | 15 => ⟨((-21013313811/72057594037927936), (-7090329333/72057594037927936)), (263/72057594037927936), by norm_num⟩
  | 16 => ⟨((14565319223/288230376151711744), (4914641787/288230376151711744)), (185/288230376151711744), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580860756610801/10141204801825835211973625643008), (423902083783/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111142550177021/39614081257132168796771975168), (250701919333/316912650057057350374175801344)), (2883/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889193037254901/39614081257132168796771975168), (563962468295/39614081257132168796771975168)), (6487/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888934002887783/2475880078570760549798248448), (149766004575/618970019642690137449562112)), (13785/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885300234762921/77371252455336267181195264), (598899724783/154742504910672534362390528)), (6893/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193625040840875/1208925819614629174706176), (280646996761/4835703278458516698824704)), (12925/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258304952789497/604462909807314587353088), (490957817221/604462909807314587353088)), (5655/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943503207144467/37778931862957161709568), (797479553701/75557863725914323419136)), (18379/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296950607612549/4722366482869645213696), (597823779871/4722366482869645213696)), (13785/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50644970750051/18446744073709551616), (821543417365/590295810358705651712)), (4739/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911232110925673/36893488147419103232), (128279168515/9223372036854775808)), (23697/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821521443001753/9223372036854775808), (1153556427615/9223372036854775808)), (13331/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398192874662775/288230376151711744), (1152362524067/1152921504606846976)), (13333/576460752303423488), by norm_num⟩
  | 5 => ⟨((596759968372999/72057594037927936), (503487862919/72057594037927936)), (23337/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490049638010201/36028797018963968), (1507784764689/36028797018963968)), (17507/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487279045895265/9007199254740992), (940026158289/4503599627370496)), (43783/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112004484494241/2251799813685248), (3746105850519/4503599627370496)), (87611/4503599627370496), by norm_num⟩
  | 1 => ⟨((552560070201191/562949953421312), (5584291450495/2251799813685248)), (131533/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084592933871447/1125899906842624), (5514944329645/1125899906842624)), (263541/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084592933871447/1125899906842624), (5514944329645/1125899906842624)), (1005329140670012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089548831905777/2251799813685248), (10625224523557/1125899906842624)), (510327/2251799813685248), by norm_num⟩
  | 2 => ⟨((969394062651861/1125899906842624), (19719271097727/1125899906842624)), (956745/2251799813685248), by norm_num⟩
  | 3 => ⟨((208574490801373/281474976710656), (67912766333077/2251799813685248)), (1681019/2251799813685248), by norm_num⟩
  | 4 => ⟨((1234390466200139/2251799813685248), (100647459481949/2251799813685248)), (1296343/1125899906842624), by norm_num⟩
  | 5 => ⟨((672168948032959/2251799813685248), (110345745369307/2251799813685248)), (6148565/4503599627370496), by norm_num⟩
  | 6 => ⟨((1561896962622551/18014398509481984), (131754133975903/4503599627370496)), (17093323/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/134217728), (-10919415363/134217728)), (1/134217728), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-655961365/268435456), (-22316352273/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((22888818881289/2251799813685248), (-388420514085977/4503599627370496)), (30481389/18014398509481984), by norm_num⟩
  | 1 => ⟨((-494757897/17179869184), (2098995559/8589934592)), (331/68719476736), by norm_num⟩
  | 2 => ⟨((350438669/8589934592), (-5946902227/17179869184)), (471/68719476736), by norm_num⟩
  | 3 => ⟨((-1323823351/34359738368), (22465123661/68719476736)), (447/68719476736), by norm_num⟩
  | 4 => ⟨((58604281/2147483648), (-15912122033/68719476736)), (319/68719476736), by norm_num⟩
  | 5 => ⟨((-531322979/34359738368), (18032974591/137438953472)), (363/137438953472), by norm_num⟩
  | 6 => ⟨((2007135139/274877906944), (-17030421415/274877906944)), (43/34359738368), by norm_num⟩
  | 7 => ⟨((-812377437/274877906944), (6892973887/274877906944)), (559/1099511627776), by norm_num⟩
  | 8 => ⟨((2301638595/2199023255552), (-19529265597/2199023255552)), (199/1099511627776), by norm_num⟩
  | 9 => ⟨((-2898236969/8796093022208), (12295683531/4398046511104)), (503/8796093022208), by norm_num⟩
  | 10 => ⟨((1642264731/17592186044416), (-6967258931/8796093022208)), (143/8796093022208), by norm_num⟩
  | 11 => ⟨((-1691958673/70368744177664), (7178083991/35184372088832)), (37/8796093022208), by norm_num⟩
  | 12 => ⟨((3195786593/562949953421312), (-13558028899/281474976710656)), (561/562949953421312), by norm_num⟩
  | 13 => ⟨((-2785952375/2251799813685248), (23638639013/2251799813685248)), (491/2251799813685248), by norm_num⟩
  | 14 => ⟨((1127599635/4503599627370496), (-19135230711/9007199254740992)), (399/9007199254740992), by norm_num⟩
  | 15 => ⟨((-3407712355/72057594037927936), (7228558799/18014398509481984)), (605/72057594037927936), by norm_num⟩
  | 16 => ⟨((2413694029/288230376151711744), (-640001539/9007199254740992)), (215/144115188075855872), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-1893322100363/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889098844418233/316912650057057350374175801344), (-2239283646639/633825300114114700748351602688)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889099411723005/39614081257132168796771975168), (-2518657862345/39614081257132168796771975168)), (12999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888834362237375/2475880078570760549798248448), (-334425851533/309485009821345068724781056)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885250322560079/77371252455336267181195264), (-2674656535329/154742504910672534362390528)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548906546263801/9671406556917033397649408), (-2506693595687/9671406556917033397649408)), (12955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629111349989111/302231454903657293676544), (-548140071495/151115727451828646838272)), (5669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471718097099385/18889465931478580854784), (-445177181143/9444732965739290427392)), (18429/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296849769130395/4722366482869645213696), (-2669757326611/4722366482869645213696)), (6913/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620499893313407/590295810358705651712), (-3668795641349/590295810358705651712)), (19017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822289483057305/73786976294838206464), (-4582815587383/73786976294838206464)), (23781/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227665474703997/1152921504606846976), (-2575649902507/4611686018427387904)), (13383/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796286262993207/576460752303423488), (-5145845155607/1152921504606846976)), (837/36028797018963968), by norm_num⟩
  | 5 => ⟨((1193344346559553/144115188075855872), (-562060614885/18014398509481984)), (23455/144115188075855872), by norm_num⟩
  | 4 => ⟨((186222910594397/4503599627370496), (-6732485398179/36028797018963968)), (8805/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486940933340623/9007199254740992), (-4197110971025/4503599627370496)), (44091/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223317322525053/4503599627370496), (-8362221933217/2251799813685248)), (88383/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209164577076627/2251799813685248), (-6231801267423/562949953421312)), (16635/281474976710656), by norm_num⟩
  | 0 => ⟨((2166883430222953/2251799813685248), (-49219794447953/2251799813685248)), (268187/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166883430222953/2251799813685248), (-49219794447953/2251799813685248)), (1023052224166106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084093436498199/2251799813685248), (-94727387736747/2251799813685248)), (1031/4398046511104), by norm_num⟩
  | 2 => ⟨((1924892322898695/2251799813685248), (-43836207339337/562949953421312)), (510765/1125899906842624), by norm_num⟩
  | 3 => ⟨((1631790101074049/2251799813685248), (-299777905512447/2251799813685248)), (476387/562949953421312), by norm_num⟩
  | 4 => ⟨((1142584756288401/2251799813685248), (-434474339826283/2251799813685248)), (3269115/2251799813685248), by norm_num⟩
  | 5 => ⟨((991857239305407/4503599627370496), (-440912868601353/2251799813685248)), (2289541/1125899906842624), by norm_num⟩
  | 6 => ⟨((22888818881289/2251799813685248), (-388420514085977/4503599627370496)), (30481389/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-22316352273/268435456)), (1/134217728), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-11383285781/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1489091438075575/18014398509481984), (-16251811526027/18014398509481984)), (15128155/9007199254740992), by norm_num⟩
  | 1 => ⟨((16418563223/68719476736), (179190739/68719476736)), (335/68719476736), by norm_num⟩
  | 2 => ⟨((-23727875723/68719476736), (-129481963/34359738368)), (243/34359738368), by norm_num⟩
  | 3 => ⟨((22860793955/68719476736), (249500673/68719476736)), (235/34359738368), by norm_num⟩
  | 4 => ⟨((-33038096605/137438953472), (-360574849/137438953472)), (341/68719476736), by norm_num⟩
  | 5 => ⟨((1193654767/8589934592), (6513721/4294967296)), (99/34359738368), by norm_num⟩
  | 6 => ⟨((-18400565479/274877906944), (-25102767/34359738368)), (3/2147483648), by norm_num⟩
  | 7 => ⟨((30391128451/1099511627776), (165843037/549755813888)), (637/1099511627776), by norm_num⟩
  | 8 => ⟨((-21960414841/2199023255552), (-239674015/2199023255552)), (231/1099511627776), by norm_num⟩
  | 9 => ⟨((14105280633/4398046511104), (307887557/8796093022208)), (149/2199023255552), by norm_num⟩
  | 10 => ⟨((-32615603823/35184372088832), (-44495475/4398046511104)), (691/35184372088832), by norm_num⟩
  | 11 => ⟨((17140221847/70368744177664), (187066857/70368744177664)), (365/70368744177664), by norm_num⟩
  | 12 => ⟨((-33027742101/562949953421312), (-22528865/35184372088832)), (353/281474976710656), by norm_num⟩
  | 13 => ⟨((7343265615/562949953421312), (320574991/2251799813685248)), (315/1125899906842624), by norm_num⟩
  | 14 => ⟨((-12128438597/4503599627370496), (-33092175/1125899906842624)), (261/4503599627370496), by norm_num⟩
  | 15 => ⟨((18696371407/36028797018963968), (102025267/18014398509481984)), (101/9007199254740992), by norm_num⟩
  | 16 => ⟨((-27019731945/288230376151711744), (-147445475/144115188075855872)), (293/144115188075855872), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-4078059168655/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889055979769617/316912650057057350374175801344), (-2411419526087/316912650057057350374175801344)), (11585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472250611258779/9903520314283042199192993792), (-1356121828227/9903520314283042199192993792)), (13037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472182660204053/618970019642690137449562112), (-2881024250853/1237940039285380274899124224)), (433/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442599035842187/38685626227668133590597632), (-5760395715083/154742504910672534362390528)), (13861/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774403873710639/4835703278458516698824704), (-1349653805081/2417851639229258349412352)), (1625/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258135423271755/604462909807314587353088), (-4722032917893/604462909807314587353088)), (11381/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886729013329143/75557863725914323419136), (-1917503221983/18889465931478580854784)), (18503/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296740882763559/4722366482869645213696), (-5749631159427/4722366482869645213696)), (6943/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620347975486103/590295810358705651712), (-7901066719079/590295810358705651712)), (4777/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911048146124963/36893488147419103232), (-4934660873635/36893488147419103232)), (23905/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227637742204595/1152921504606846976), (-2773337517509/2305843009213693952)), (13461/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99521564246467/72057594037927936), (-11081310145519/1152921504606846976)), (26959/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596569479980385/72057594037927936), (-9682609991955/144115188075855872)), (11815/72057594037927936), by norm_num⟩
  | 4 => ⟨((372365648913221/9007199254740992), (-3624215893981/9007199254740992)), (35527/36028797018963968), by norm_num⟩
  | 3 => ⟨((743259050561893/4503599627370496), (-4518446912611/2251799813685248)), (44553/9007199254740992), by norm_num⟩
  | 2 => ⟨((555601531445717/1125899906842624), (-4500736614773/562949953421312)), (44769/2251799813685248), by norm_num⟩
  | 1 => ⟨((551908819508053/562949953421312), (-26827655642183/1125899906842624)), (4231/70368744177664), by norm_num⟩
  | 0 => ⟨((540795686586879/562949953421312), (-13237574254589/281474976710656)), (68787/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((540795686586879/562949953421312), (-13237574254589/281474976710656)), (262401582958030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((518268168190145/562949953421312), (-50866497202799/562949953421312)), (69315/281474976710656), by norm_num⟩
  | 2 => ⟨((472536665124121/562949953421312), (-5853647861441/35184372088832)), (560613/1125899906842624), by norm_num⟩
  | 3 => ⟨((762124622630271/1125899906842624), (-628929965218111/2251799813685248)), (2255379/2251799813685248), by norm_num⟩
  | 4 => ⟨((856107567294407/2251799813685248), (-851448711363507/2251799813685248)), (1078301/562949953421312), by norm_num⟩
  | 5 => ⟨((7065689097071/4503599627370496), (-647421392018339/2251799813685248)), (6541469/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1489091438075575/18014398509481984), (-16251811526027/18014398509481984)), (15128155/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-11383285781/134217728)), (1/134217728), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-681712945/268435456), (-23192442475/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((3399079622389/9007199254740992), (710656645138467/9007199254740992)), (3593475/2251799813685248), by norm_num⟩
  | 1 => ⟨((-76357899/68719476736), (-31928789165/137438953472)), (81/17179869184), by norm_num⟩
  | 2 => ⟨((112415587/68719476736), (5875773211/17179869184)), (479/68719476736), by norm_num⟩
  | 3 => ⟨((-27583403/17179869184), (-23067807567/68719476736)), (59/8589934592), by norm_num⟩
  | 4 => ⟨((81217647/68719476736), (16980437941/68719476736)), (697/137438953472), by norm_num⟩
  | 5 => ⟨((-47828081/68719476736), (-19999145343/137438953472)), (103/34359738368), by norm_num⟩
  | 6 => ⟨((93884577/274877906944), (9814377183/137438953472)), (203/137438953472), by norm_num⟩
  | 7 => ⟨((-157964233/1099511627776), (-16513048419/549755813888)), (343/549755813888), by norm_num⟩
  | 8 => ⟨((116279011/2199023255552), (24310831715/2199023255552)), (507/2199023255552), by norm_num⟩
  | 9 => ⟨((-9510457/549755813888), (-31814115785/8796093022208)), (333/4398046511104), by norm_num⟩
  | 10 => ⟨((89609473/17592186044416), (18734944521/17592186044416)), (197/8796093022208), by norm_num⟩
  | 11 => ⟨((-47972659/35184372088832), (-10029800167/35184372088832)), (53/8796093022208), by norm_num⟩
  | 12 => ⟨((47084189/140737488355328), (9844044855/140737488355328)), (209/140737488355328), by norm_num⟩
  | 13 => ⟨((-42657391/562949953421312), (-17837039621/1125899906842624)), (381/1125899906842624), by norm_num⟩
  | 14 => ⟨((17943155/1125899906842624), (7502867819/2251799813685248)), (643/9007199254740992), by norm_num⟩
  | 15 => ⟨((-112709387/36028797018963968), (-5891129723/9007199254740992)), (507/36028797018963968), by norm_num⟩
  | 16 => ⟨((41483239/72057594037927936), (4336517997/36028797018963968)), (375/144115188075855872), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580667682406957/10141204801825835211973625643008), (2039907235665/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778049472003247/633825300114114700748351602688), (603067917227/158456325028528675187087900672)), (2889/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888932680529623/39614081257132168796771975168), (2713206111243/39614081257132168796771975168)), (6501/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59020538237587/77371252455336267181195264), (2882034566567/2475880078570760549798248448)), (13817/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770323521428317/154742504910672534362390528), (720298650831/38685626227668133590597632)), (13819/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548740508695235/9671406556917033397649408), (2700227782721/9671406556917033397649408)), (6479/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258077433016149/604462909807314587353088), (295225936613/75557863725914323419136)), (11341/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886636359454175/75557863725914323419136), (479533217915/9444732965739290427392)), (9217/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296672773597031/4722366482869645213696), (2875737527805/4722366482869645213696)), (6915/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620256567058997/590295810358705651712), (1975882532693/295147905179352825856)), (19023/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910992694634593/36893488147419103232), (4936147651561/73786976294838206464)), (23789/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820981780362419/9223372036854775808), (5548276776257/9223372036854775808)), (26777/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592230619320153/1152921504606846976), (5542170887615/1152921504606846976)), (26795/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149130662883439/18014398509481984), (4842538337205/144115188075855872)), (23467/144115188075855872), by norm_num⟩
  | 4 => ⟨((372333742556467/9007199254740992), (7250104944675/36028797018963968)), (35241/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486380981219639/9007199254740992), (4519348116437/4503599627370496)), (22061/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111099375277913/2251799813685248), (18005765478109/4503599627370496)), (88461/4503599627370496), by norm_num⟩
  | 1 => ⟨((137968130100349/140737488355328), (26830201987211/2251799813685248)), (133235/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163548078210507/2251799813685248), (52950336439373/2251799813685248)), (268657/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163548078210507/2251799813685248), (52950336439373/2251799813685248)), (1024845131880950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1038754981719089/1125899906842624), (101750251463533/2251799813685248)), (528891/2251799813685248), by norm_num⟩
  | 2 => ⟨((1912112483687171/2251799813685248), (11734344673599/140737488355328)), (255927/562949953421312), by norm_num⟩
  | 3 => ⟨((804006698989635/1125899906842624), (318854445968621/2251799813685248)), (954635/1125899906842624), by norm_num⟩
  | 4 => ⟨((1103134885823423/2251799813685248), (227694406050993/1125899906842624)), (3267531/2251799813685248), by norm_num⟩
  | 5 => ⟨((896640633858857/4503599627370496), (892362246750957/4503599627370496)), (9046141/4503599627370496), by norm_num⟩
  | 6 => ⟨((3399079622389/9007199254740992), (710656645138467/9007199254740992)), (3593475/2251799813685248), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-681712945/268435456), (-23192442475/268435456)), (1/134217728), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-693588655/268435456), (-23596464019/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((678648858987765/9007199254740992), (20695828588363/4503599627370496)), (2800233/4503599627370496), by norm_num⟩
  | 1 => ⟨((-15510942759/68719476736), (-1892064259/137438953472)), (129/68719476736), by norm_num⟩
  | 2 => ⟨((5808328977/17179869184), (1417029491/68719476736)), (195/68719476736), by norm_num⟩
  | 3 => ⟨((-11600132381/34359738368), (-353753415/17179869184)), (197/68719476736), by norm_num⟩
  | 4 => ⟨((4343861369/17179869184), (529875261/34359738368)), (149/68719476736), by norm_num⟩
  | 5 => ⟨((-2602609139/17179869184), (-79368221/8589934592)), (45/34359738368), by norm_num⟩
  | 6 => ⟨((2598906731/34359738368), (1268085019/274877906944)), (91/137438953472), by norm_num⟩
  | 7 => ⟨((-17795722903/549755813888), (-33918243/17179869184)), (157/549755813888), by norm_num⟩
  | 8 => ⟨((6663902679/549755813888), (1625759603/2199023255552)), (237/2199023255552), by norm_num⟩
  | 9 => ⟨((-17745127399/4398046511104), (-270574473/1099511627776)), (5/137438953472), by norm_num⟩
  | 10 => ⟨((21263860339/17592186044416), (648454945/8796093022208)), (193/17592186044416), by norm_num⟩
  | 11 => ⟨((-5790984789/17592186044416), (-706399057/35184372088832)), (53/17592186044416), by norm_num⟩
  | 12 => ⟨((1445686669/17592186044416), (705394151/140737488355328)), (213/281474976710656), by norm_num⟩
  | 13 => ⟨((-10660652829/562949953421312), (-1300413553/1125899906842624)), (99/562949953421312), by norm_num⟩
  | 14 => ⟨((18249406707/4503599627370496), (17391477/70368744177664)), (171/4503599627370496), by norm_num⟩
  | 15 => ⟨((-14578756439/18014398509481984), (-889176899/18014398509481984)), (69/9007199254740992), by norm_num⟩
  | 16 => ⟨((10918512793/72057594037927936), (1331867967/144115188075855872)), (209/144115188075855872), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790305027129445/5070602400912917605986812821504), (79349647103/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777984441839369/633825300114114700748351602688), (93827266223/633825300114114700748351602688)), (11527/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888859710042141/39614081257132168796771975168), (105532162359/39614081257132168796771975168)), (1621/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888579942124819/2475880078570760549798248448), (28024596673/618970019642690137449562112)), (13779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770246520529249/154742504910672534362390528), (56032587767/77371252455336267181195264)), (13779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548668618245327/9671406556917033397649408), (52512914567/4835703278458516698824704)), (12917/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258014826515355/604462909807314587353088), (91862343237/604462909807314587353088)), (11303/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886535181439711/75557863725914323419136), (74605116849/37778931862957161709568)), (18367/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648298688705605/2361183241434822606848), (27962473435/1180591620717411303424)), (861/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810076844106319/295147905179352825856), (76849885621/295147905179352825856)), (9471/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113866123458577/4611686018427387904), (191984074091/73786976294838206464)), (11839/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820840065729339/9223372036854775808), (53947220099/2305843009213693952)), (13319/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398022733253235/288230376151711744), (26943455239/144115188075855872)), (13319/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192925353616185/144115188075855872), (5885411175/4503599627370496)), (11655/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489159583715101/36028797018963968), (281958587473/36028797018963968)), (17483/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486169656522141/9007199254740992), (351503265803/9007199254740992)), (43711/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221799696981865/4503599627370496), (700179776045/4503599627370496)), (87431/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103475019663351/1125899906842624), (521615609163/1125899906842624)), (65587/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162699451399973/2251799813685248), (2058478658115/2251799813685248)), (131233/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162699451399973/2251799813685248), (2058478658115/2251799813685248)), (500614170554732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2077122775890387/2251799813685248), (3954055451615/2251799813685248)), (252321/1125899906842624), by norm_num⟩
  | 2 => ⟨((1915988874920093/2251799813685248), (7294661439945/2251799813685248)), (932765/2251799813685248), by norm_num⟩
  | 3 => ⟨((815116897697097/1125899906842624), (775851059245/140737488355328)), (199171/281474976710656), by norm_num⟩
  | 4 => ⟨((1180170685515071/2251799813685248), (8987076803447/1125899906842624)), (581167/562949953421312), by norm_num⟩
  | 5 => ⟨((1236770487579289/4503599627370496), (2355068271931/281474976710656)), (1236917/1125899906842624), by norm_num⟩
  | 6 => ⟨((678648858987765/9007199254740992), (20695828588363/4503599627370496)), (2800233/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-693588655/268435456), (-23596464019/268435456)), (1/134217728), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-352442413/134217728), (-23980769173/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((64775875640107/4503599627370496), (-1277778505702887/18014398509481984)), (24741659/18014398509481984), by norm_num⟩
  | 1 => ⟨((-3009210309/68719476736), (14840031933/68719476736)), (289/68719476736), by norm_num⟩
  | 2 => ⟨((4580804153/68719476736), (-11295202549/34359738368)), (221/34359738368), by norm_num⟩
  | 3 => ⟨((-4648787009/68719476736), (11462832533/34359738368)), (225/34359738368), by norm_num⟩
  | 4 => ⟨((3538334089/68719476736), (-17449425423/68719476736)), (43/8589934592), by norm_num⟩
  | 5 => ⟨((-2154507505/68719476736), (10625033445/68719476736)), (421/137438953472), by norm_num⟩
  | 6 => ⟨((2186482147/137438953472), (-10782717575/137438953472)), (429/274877906944), by norm_num⟩
  | 7 => ⟨((-3803882261/549755813888), (18758986055/549755813888)), (375/549755813888), by norm_num⟩
  | 8 => ⟨((5790502447/2199023255552), (-28556076977/2199023255552)), (573/2199023255552), by norm_num⟩
  | 9 => ⟨((-30606449/34359738368), (19319914909/4398046511104)), (195/2199023255552), by norm_num⟩
  | 10 => ⟨((4770919461/17592186044416), (-11763982887/8796093022208)), (477/17592186044416), by norm_num⟩
  | 11 => ⟨((-2640940245/35184372088832), (26047788987/70368744177664)), (265/35184372088832), by norm_num⟩
  | 12 => ⟨((335016743/17592186044416), (-26434359341/281474976710656)), (135/70368744177664), by norm_num⟩
  | 13 => ⟨((-5021371033/1125899906842624), (12381538483/562949953421312)), (127/281474976710656), by norm_num⟩
  | 14 => ⟨((4367907651/4503599627370496), (-21540498129/4503599627370496)), (111/1125899906842624), by norm_num⟩
  | 15 => ⟨((-443273095/2251799813685248), (4372035325/4503599627370496)), (181/9007199254740992), by norm_num⟩
  | 16 => ⟨((5398219535/144115188075855872), (-26621519291/144115188075855872)), (553/144115188075855872), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238385567/10141204801825835211973625643008), (-1785532058309/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888958620734279/316912650057057350374175801344), (-2111161839339/633825300114114700748351602688)), (361/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1888783995254897/39614081257132168796771975168), (-148407296993/2475880078570760549798248448)), (6499/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888499340894705/2475880078570760549798248448), (-1261124153845/1237940039285380274899124224)), (3453/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770165745963121/154742504910672534362390528), (-2521488431371/154742504910672534362390528)), (6907/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548592708078153/9671406556917033397649408), (-2363088330729/9671406556917033397649408)), (12953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19655440957589/9444732965739290427392), (-516723886881/151115727451828646838272)), (1417/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943213301815987/37778931862957161709568), (-3357193328537/75557863725914323419136)), (18425/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324128910790569/1180591620717411303424), (-78642898647/147573952589676412928)), (13823/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810020407688265/295147905179352825856), (-1729070110555/295147905179352825856)), (4753/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455429038290775/18446744073709551616), (-1079864151543/18446744073709551616)), (11887/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227584939061015/1152921504606846976), (-4854966759523/9223372036854775808)), (26759/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49747785270579/36028797018963968), (-606180621931/144115188075855872)), (26775/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192782371429419/144115188075855872), (-4237060064797/144115188075855872)), (11723/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488942313973385/36028797018963968), (-3171600396307/18014398509481984)), (35205/36028797018963968), by norm_num⟩
  | 3 => ⟨((742946599315999/4503599627370496), (-7907363008333/9007199254740992)), (44069/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110616130566921/2251799813685248), (-7874992477681/2251799813685248)), (11041/562949953421312), by norm_num⟩
  | 1 => ⟨((2206062906253885/2251799813685248), (-23463728459389/2251799813685248)), (132969/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160783182253965/2251799813685248), (-23143035875841/1125899906842624)), (16741/140737488355328), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160783182253965/2251799813685248), (-23143035875841/1125899906842624)), (63861847460699037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1036246990498617/1125899906842624), (-88830423384709/2251799813685248)), (525071/2251799813685248), by norm_num⟩
  | 2 => ⟨((1903961635974419/2251799813685248), (-40878526740117/562949953421312)), (1007949/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597980880102459/2251799813685248), (-276511779334275/2251799813685248)), (1850885/2251799813685248), by norm_num⟩
  | 4 => ⟨((550023166803731/1125899906842624), (-196225496517891/1125899906842624)), (1540755/1125899906842624), by norm_num⟩
  | 5 => ⟨((117248894387739/562949953421312), (-766878606856415/4503599627370496)), (2042431/1125899906842624), by norm_num⟩
  | 6 => ⟨((64775875640107/4503599627370496), (-1277778505702887/18014398509481984)), (24741659/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-352442413/134217728), (-23980769173/268435456)), (1/134217728), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile048Terms2
