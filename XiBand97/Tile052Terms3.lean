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
namespace Reinmann.XiBand97.Tile052Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨52,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76729/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76729/2560))
  have he : value ((69/80), (76729/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-715655399/268435456), (-6217337311/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-9842399770707/4503599627370496), (1251888224228125/18014398509481984)), (25654121/18014398509481984), by norm_num⟩
  | 1 => ⟨((58027793/8589934592), (-29523007567/137438953472)), (607/137438953472), by norm_num⟩
  | 2 => ⟨((-717465487/68719476736), (22814217435/68719476736)), (471/68719476736), by norm_num⟩
  | 3 => ⟨((92404845/8589934592), (-2938321443/8589934592)), (487/68719476736), by norm_num⟩
  | 4 => ⟨((-285627299/34359738368), (4541238161/17179869184)), (189/34359738368), by norm_num⟩
  | 5 => ⟨((353154443/68719476736), (-11229727957/68719476736)), (469/137438953472), by norm_num⟩
  | 6 => ⟨((-22741987/8589934592), (23141043903/274877906944)), (485/274877906944), by norm_num⟩
  | 7 => ⟨((642710375/549755813888), (-20437128319/549755813888)), (215/274877906944), by norm_num⟩
  | 8 => ⟨((-993322527/2199023255552), (31586015629/2199023255552)), (667/2199023255552), by norm_num⟩
  | 9 => ⟨((341155789/2199023255552), (-5424095291/1099511627776)), (115/1099511627776), by norm_num⟩
  | 10 => ⟨((-421810811/8796093022208), (3353221763/2199023255552)), (571/17592186044416), by norm_num⟩
  | 11 => ⟨((948243727/70368744177664), (-15076292109/35184372088832)), (161/17592186044416), by norm_num⟩
  | 12 => ⟨((-977020539/281474976710656), (15533819649/140737488355328)), (333/140737488355328), by norm_num⟩
  | 13 => ⟨((464617225/562949953421312), (-14774060307/562949953421312)), (159/281474976710656), by norm_num⟩
  | 14 => ⟨((-410329019/2251799813685248), (26095570067/4503599627370496)), (141/1125899906842624), by norm_num⟩
  | 15 => ⟨((169112589/4503599627370496), (-21510003979/18014398509481984)), (233/9007199254740992), by norm_num⟩
  | 16 => ⟨((-32670887/4503599627370496), (33244167735/144115188075855872)), (361/72057594037927936), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (521772214417/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444463642739391/158456325028528675187087900672), (2467550383277/633825300114114700748351602688)), (2889/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888713459164549/39614081257132168796771975168), (1387676142893/19807040628566084398385987584)), (13003/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944212176047103/1237940039285380274899124224), (368501224213/309485009821345068724781056)), (13817/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442522676877337/38685626227668133590597632), (1473553956277/77371252455336267181195264)), (3455/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548522306826651/9671406556917033397649408), (2761955763313/9671406556917033397649408)), (12959/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257886567552055/604462909807314587353088), (603938443803/151115727451828646838272)), (5671/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886326317750211/75557863725914323419136), (980951340287/18889465931478580854784)), (18435/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648220171319773/2361183241434822606848), (2941284634461/4722366482869645213696)), (13831/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404984284368783/147573952589676412928), (252607353715/36893488147419103232)), (19025/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821586346696567/73786976294838206464), (1262081674563/18446744073709551616)), (23791/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820533193419399/9223372036854775808), (5674118892273/9223372036854775808)), (6695/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795891226076335/576460752303423488), (5667564643805/1152921504606846976)), (26799/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192653628818197/144115188075855872), (4951754539481/144115188075855872)), (23471/144115188075855872), by norm_num⟩
  | 4 => ⟨((744374201165841/18014398509481984), (7412925250881/36028797018963968)), (35247/36028797018963968), by norm_num⟩
  | 3 => ⟨((742824710583357/4503599627370496), (2310117654829/2251799813685248)), (11033/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110370287386891/2251799813685248), (18404085196093/4503599627370496)), (88487/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205315160724459/2251799813685248), (27414692421481/2251799813685248)), (133287/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159247498753047/2251799813685248), (54067859512245/2251799813685248)), (134407/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159247498753047/2251799813685248), (54067859512245/2251799813685248)), (512722019675826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034600500257955/1125899906842624), (103691180455053/2251799813685248)), (528441/2251799813685248), by norm_num⟩
  | 2 => ⟨((1896634369394637/2251799813685248), (190565691531105/2251799813685248)), (127481/281474976710656), by norm_num⟩
  | 3 => ⟨((790680109914513/1125899906842624), (80254345432651/562949953421312)), (1890601/2251799813685248), by norm_num⟩
  | 4 => ⟨((1064769599372421/2251799813685248), (450878549911279/2251799813685248)), (399307/281474976710656), by norm_num⟩
  | 5 => ⟨((12912488203365/70368744177664), (832809121933/4398046511104)), (8600537/4503599627370496), by norm_num⟩
  | 6 => ⟨((-9842399770707/4503599627370496), (1251888224228125/18014398509481984)), (25654121/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-6217337311/67108864)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-725947119/268435456), (-6306747795/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1161752559094531/18014398509481984), (321417043665457/18014398509481984)), (12000593/18014398509481984), by norm_num⟩
  | 1 => ⟨((-13895677297/68719476736), (-480557099/8589934592)), (145/68719476736), by norm_num⟩
  | 2 => ⟨((21784907895/68719476736), (6027136017/68719476736)), (229/68719476736), by norm_num⟩
  | 3 => ⟨((-11384408783/34359738368), (-787418755/8589934592)), (241/68719476736), by norm_num⟩
  | 4 => ⟨((17847873945/68719476736), (308618369/4294967296)), (191/68719476736), by norm_num⟩
  | 5 => ⟨((-699523819/4294967296), (-3096547555/68719476736)), (241/137438953472), by norm_num⟩
  | 6 => ⟨((11697882071/137438953472), (809100579/34359738368)), (127/137438953472), by norm_num⟩
  | 7 => ⟨((-20959223755/549755813888), (-5798697567/549755813888)), (229/549755813888), by norm_num⟩
  | 8 => ⟨((16429381213/1099511627776), (2272722835/549755813888)), (181/1099511627776), by norm_num⟩
  | 9 => ⟨((-5723803307/1099511627776), (-6334319381/4398046511104)), (127/2199023255552), by norm_num⟩
  | 10 => ⟨((7178780865/4398046511104), (993061089/2199023255552)), (161/8796093022208), by norm_num⟩
  | 11 => ⟨((-16370200639/35184372088832), (-4529072437/35184372088832)), (93/17592186044416), by norm_num⟩
  | 12 => ⟨((2138694559/17592186044416), (2366813405/70368744177664)), (49/35184372088832), by norm_num⟩
  | 13 => ⟨((-8253371593/281474976710656), (-285428067/35184372088832)), (191/562949953421312), by norm_num⟩
  | 14 => ⟨((14787656509/2251799813685248), (2045618407/1125899906842624)), (173/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1545553715/1125899906842624), (-6841626329/18014398509481984)), (73/4503599627370496), by norm_num⟩
  | 16 => ⟨((19384298935/72057594037927936), (5362969945/72057594037927936)), (231/72057594037927936), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (175796629211/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777798700101207/633825300114114700748351602688), (415659892685/633825300114114700748351602688)), (11531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472162698332053/9903520314283042199192993792), (58438580355/4951760157141521099596496896)), (12973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888358021474395/2475880078570760549798248448), (124147748039/618970019642690137449562112)), (1723/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770024659880931/154742504910672534362390528), (496437015101/154742504910672534362390528)), (1723/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548460687617287/9671406556917033397649408), (58155771049/1208925819614629174706176)), (12923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157229118865035/75557863725914323419136), (406926939897/604462909807314587353088)), (2827/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886239752989843/75557863725914323419136), (660949955647/75557863725914323419136)), (18377/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162046988811027/590295810358705651712), (495444596187/4722366482869645213696)), (1723/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619849340766291/590295810358705651712), (340400665823/295147905179352825856)), (18953/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821477795212453/73786976294838206464), (425174854821/36893488147419103232)), (23693/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820412712305015/9223372036854775808), (119468480167/1152921504606846976)), (26657/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795832007840195/576460752303423488), (477314823219/576460752303423488)), (6665/288230376151711744), by norm_num⟩
  | 5 => ⟨((298138072741293/36028797018963968), (834044732731/144115188075855872)), (5833/36028797018963968), by norm_num⟩
  | 4 => ⟨((744300484149847/18014398509481984), (1248559079983/36028797018963968)), (8751/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485473096435115/9007199254740992), (1556319690669/9007199254740992)), (5471/1125899906842624), by norm_num⟩
  | 2 => ⟨((2220411691181283/4503599627370496), (774885327017/1125899906842624)), (43787/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204880770568389/2251799813685248), (2308352141341/1125899906842624)), (65731/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158611598626087/2251799813685248), (2275949894817/562949953421312)), (131665/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158611598626087/2251799813685248), (2275949894817/562949953421312)), (502262119773482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2069243067806555/2251799813685248), (17454098045433/2251799813685248)), (506995/2251799813685248), by norm_num⟩
  | 2 => ⟨((1901351177891765/2251799813685248), (32078136933691/2251799813685248)), (939645/2251799813685248), by norm_num⟩
  | 3 => ⟨((1604986052861641/2251799813685248), (54171603597061/2251799813685248)), (403397/562949953421312), by norm_num⟩
  | 4 => ⟨((1142661817274565/2251799813685248), (38611189016905/1125899906842624)), (1188915/1125899906842624), by norm_num⟩
  | 5 => ⟨((577188400624713/2251799813685248), (39186015684923/1125899906842624)), (5152639/4503599627370496), by norm_num⟩
  | 6 => ⟨((1161752559094531/18014398509481984), (321417043665457/18014398509481984)), (12000593/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-6306747795/67108864)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-735800759/268435456), (-25569409615/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((77778380116477/2251799813685248), (-245326582927251/4503599627370496)), (9420429/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3771726667/34359738368), (2974171015/17179869184)), (115/34359738368), by norm_num⟩
  | 2 => ⟨((11986750381/68719476736), (-18904151173/68719476736)), (367/68719476736), by norm_num⟩
  | 3 => ⟨((-12698179321/68719476736), (10013068341/34359738368)), (391/68719476736), by norm_num⟩
  | 4 => ⟨((5044437179/34359738368), (-7955517549/34359738368)), (313/68719476736), by norm_num⟩
  | 5 => ⟨((-12825194319/137438953472), (1264153151/8589934592)), (25/8589934592), by norm_num⟩
  | 6 => ⟨((6793192989/137438953472), (-10713458037/137438953472)), (107/68719476736), by norm_num⟩
  | 7 => ⟨((-3084161857/137438953472), (303999521/8589934592)), (391/549755813888), by norm_num⟩
  | 8 => ⟨((9801632403/1099511627776), (-7729014737/549755813888)), (313/1099511627776), by norm_num⟩
  | 9 => ⟨((-6922247867/2199023255552), (1364623605/274877906944)), (223/2199023255552), by norm_num⟩
  | 10 => ⟨((8799710539/8796093022208), (-867369455/549755813888)), (143/4398046511104), by norm_num⟩
  | 11 => ⟨((-2542359435/8796093022208), (8019045291/17592186044416)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((5386503427/70368744177664), (-16989971735/140737488355328)), (177/70368744177664), by norm_num⟩
  | 13 => ⟨((-10534521753/562949953421312), (16613859923/562949953421312)), (87/140737488355328), by norm_num⟩
  | 14 => ⟨((4782753887/1125899906842624), (-15085640333/2251799813685248)), (159/1125899906842624), by norm_num⟩
  | 15 => ⟨((-8106586299/9007199254740992), (6392396939/4503599627370496)), (271/9007199254740992), by norm_num⟩
  | 16 => ⟨((3220395955/18014398509481984), (-20315381577/72057594037927936)), (433/72057594037927936), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-81876792515/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777740979135519/633825300114114700748351602688), (-774322808007/316912650057057350374175801344)), (11545/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888585807096853/39614081257132168796771975168), (-870907437479/19807040628566084398385987584)), (12989/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888288904889677/2475880078570760549798248448), (-925080525457/1237940039285380274899124224)), (13803/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769955466104033/154742504910672534362390528), (-1849579432393/154742504910672534362390528)), (3451/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548395736513129/9671406556917033397649408), (-866681497741/4835703278458516698824704)), (12943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78611002303383/37778931862957161709568), (-1516075176977/604462909807314587353088)), (11327/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943073557175523/37778931862957161709568), (-2462465046077/75557863725914323419136)), (18409/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81019143598455/295147905179352825856), (-1845836898395/4722366482869645213696)), (6905/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202469175714915/73786976294838206464), (-2536382527283/590295810358705651712)), (1187/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455339387769839/18446744073709551616), (-792003820729/18446744073709551616)), (23747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56883655979037/288230376151711744), (-445079235195/1152921504606846976)), (26725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795763869143421/576460752303423488), (-1778204725891/576460752303423488)), (26737/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192432424320455/144115188075855872), (-1553556127637/72057594037927936)), (23409/144115188075855872), by norm_num⟩
  | 4 => ⟨((372104981395299/9007199254740992), (-4651192501213/36028797018963968)), (35139/36028797018963968), by norm_num⟩
  | 3 => ⟨((742622314831091/4503599627370496), (-5797444104777/9007199254740992)), (21985/4503599627370496), by norm_num⟩
  | 2 => ⟨((277493539138229/562949953421312), (-5772696708391/2251799813685248)), (44039/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204169750969123/2251799813685248), (-17194858443445/2251799813685248)), (132469/2251799813685248), by norm_num⟩
  | 0 => ⟨((33705104634071/35184372088832), (-16949905381365/1125899906842624)), (266357/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((33705104634071/35184372088832), (-16949905381365/1125899906842624)), (1016071328170012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065923604602001/2251799813685248), (-64949101035439/2251799813685248)), (259169/1125899906842624), by norm_num⟩
  | 2 => ⟨((1893517322638167/2251799813685248), (-119175674597111/2251799813685248)), (981005/2251799813685248), by norm_num⟩
  | 3 => ⟨((396483402744245/562949953421312), (-200427411811005/2251799813685248)), (1753675/2251799813685248), by norm_num⟩
  | 4 => ⟨((274781782996361/562949953421312), (-4411257039541/35184372088832)), (2782395/2251799813685248), by norm_num⟩
  | 5 => ⟨((1002198870984057/4503599627370496), (-137803576146817/1125899906842624)), (3413921/2251799813685248), by norm_num⟩
  | 6 => ⟨((77778380116477/2251799813685248), (-245326582927251/4503599627370496)), (9420429/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-25569409615/268435456)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-745252095/268435456), (-6474461955/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-686368198587821/18014398509481984), (-443628293183419/9007199254740992)), (25673875/18014398509481984), by norm_num⟩
  | 1 => ⟨((4213970187/34359738368), (5447328141/34359738368)), (317/68719476736), by norm_num⟩
  | 2 => ⟨((-13564246761/68719476736), (-17534272863/68719476736)), (1/134217728), by norm_num⟩
  | 3 => ⟨((14553875327/68719476736), (1175846813/4294967296)), (551/68719476736), by norm_num⟩
  | 4 => ⟨((-5855889681/34359738368), (-236556555/1073741824)), (445/68719476736), by norm_num⟩
  | 5 => ⟨((7539752691/68719476736), (4873255527/34359738368)), (9/2147483648), by norm_num⟩
  | 6 => ⟨((-4044921277/68719476736), (-1307200367/17179869184)), (155/68719476736), by norm_num⟩
  | 7 => ⟨((14880113499/549755813888), (9617635793/274877906944)), (573/549755813888), by norm_num⟩
  | 8 => ⟨((-11974309403/1099511627776), (-15478987673/1099511627776)), (463/1099511627776), by norm_num⟩
  | 9 => ⟨((8565292235/2199023255552), (5536104357/1099511627776)), (333/2199023255552), by norm_num⟩
  | 10 => ⟨((-11028244843/8796093022208), (-14256025983/8796093022208)), (431/8796093022208), by norm_num⟩
  | 11 => ⟨((1613570487/4398046511104), (16686682689/35184372088832)), (507/35184372088832), by norm_num⟩
  | 12 => ⟨((-13850354753/140737488355328), (-17904119835/140737488355328)), (273/70368744177664), by norm_num⟩
  | 13 => ⟨((6858857243/281474976710656), (1108291125/35184372088832)), (543/562949953421312), by norm_num⟩
  | 14 => ⟨((-12615891295/2251799813685248), (-4077087439/562949953421312)), (501/2251799813685248), by norm_num⟩
  | 15 => ⟨((10829063333/9007199254740992), (6999273703/4503599627370496)), (27/562949953421312), by norm_num⟩
  | 16 => ⟨((-4357176271/18014398509481984), (-11264896457/36028797018963968)), (349/36028797018963968), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-1451905031655/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777681728297329/633825300114114700748351602688), (-3432528764707/633825300114114700748351602688)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888518890752895/39614081257132168796771975168), (-3860661027989/39614081257132168796771975168)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888217455749621/2475880078570760549798248448), (-4100789919035/2475880078570760549798248448)), (6917/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769883623116821/154742504910672534362390528), (-4099482662627/154742504910672534362390528)), (13837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774163982808465/4835703278458516698824704), (-3841876500885/9671406556917033397649408)), (811/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((628858159818677/302231454903657293676544), (-1680126982675/302231454903657293676544)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471512322899017/18889465931478580854784), (-5457811354279/75557863725914323419136)), (18463/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296232246892455/4722366482869645213696), (-2045541726609/2361183241434822606848)), (6927/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404912619198795/147573952589676412928), (-1405386212811/147573952589676412928)), (9529/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821227228941143/73786976294838206464), (-7021392356609/73786976294838206464)), (11919/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820128099729631/9223372036854775808), (-1972864146883/2305843009213693952)), (26839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591376004670851/1152921504606846976), (-7881953179563/1152921504606846976)), (1679/72057594037927936), by norm_num⟩
  | 5 => ⟨((1192296469713471/144115188075855872), (-6886029872051/144115188075855872)), (1471/9007199254740992), by norm_num⟩
  | 4 => ⟨((744104821086743/18014398509481984), (-10307716900587/36028797018963968)), (17681/18014398509481984), by norm_num⟩
  | 3 => ⟨((185621339236845/1125899906842624), (-6423695327617/4503599627370496)), (44305/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219367510811901/4503599627370496), (-25583288064891/4503599627370496)), (44459/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101608432864469/1125899906842624), (-4762144211513/281474976710656)), (16769/281474976710656), by norm_num⟩
  | 0 => ⟨((2154898644952091/2251799813685248), (-75088911022117/2251799813685248)), (271417/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154898644952091/2251799813685248), (-75088911022117/2251799813685248)), (1035373696334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029831736655911/1125899906842624), (-143715255351829/2251799813685248)), (537577/2251799813685248), by norm_num⟩
  | 2 => ⟨((937374522152829/1125899906842624), (-65726327048897/562949953421312)), (263009/562949953421312), by norm_num⟩
  | 3 => ⟨((382534534942587/562949953421312), (-437766689815933/2251799813685248)), (249677/281474976710656), by norm_num⟩
  | 4 => ⟨((477325524010355/1125899906842624), (-297470274372269/1125899906842624)), (1745593/1125899906842624), by norm_num⟩
  | 5 => ⟨((495074529768569/4503599627370496), (-504450364474875/2251799813685248)), (600621/281474976710656), by norm_num⟩
  | 6 => ⟨((-686368198587821/18014398509481984), (-443628293183419/9007199254740992)), (25673875/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-6474461955/67108864)), (1/134217728), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-754332693/268435456), (-26213402727/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1047104347749165/18014398509481984), (141050621246953/9007199254740992)), (23741219/18014398509481984), by norm_num⟩
  | 1 => ⟨((26028190997/137438953472), (-3506138159/68719476736)), (37/8589934592), by norm_num⟩
  | 2 => ⟨((-21200589745/68719476736), (5711668299/68719476736)), (121/17179869184), by norm_num⟩
  | 3 => ⟨((5756130671/17179869184), (-3101527785/34359738368)), (33/4294967296), by norm_num⟩
  | 4 => ⟨((-4688507353/17179869184), (5052538469/68719476736)), (27/4294967296), by norm_num⟩
  | 5 => ⟨((3055121915/17179869184), (-3292331619/68719476736)), (565/137438953472), by norm_num⟩
  | 6 => ⟨((-6635921423/68719476736), (7151156167/274877906944)), (77/34359738368), by norm_num⟩
  | 7 => ⟨((3088638945/68719476736), (-6656902043/549755813888)), (575/549755813888), by norm_num⟩
  | 8 => ⟨((-5031541927/274877906944), (5422207375/1099511627776)), (235/549755813888), by norm_num⟩
  | 9 => ⟨((14571777185/2199023255552), (-1962897231/1099511627776)), (171/1099511627776), by norm_num⟩
  | 10 => ⟨((-296726605/137438953472), (2558123469/4398046511104)), (7/137438953472), by norm_num⟩
  | 11 => ⟨((175775259/274877906944), (-3030768443/17592186044416)), (533/35184372088832), by norm_num⟩
  | 12 => ⟨((-12217445607/70368744177664), (3291512057/70368744177664)), (581/140737488355328), by norm_num⟩
  | 13 => ⟨((24495764453/562949953421312), (-6599424023/562949953421312)), (585/562949953421312), by norm_num⟩
  | 14 => ⟨((-712585405/70368744177664), (3071651509/1125899906842624)), (273/1125899906842624), by norm_num⟩
  | 15 => ⟨((19811601417/9007199254740992), (-1334364953/2251799813685248)), (119/2251799813685248), by norm_num⟩
  | 16 => ⟨((-16137027497/36028797018963968), (2173744917/18014398509481984)), (389/36028797018963968), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (3749476513697/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55550794496227/19807040628566084398385987584), (17312204631/2475880078570760549798248448)), (2895/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888455334043389/39614081257132168796771975168), (1246170957967/9903520314283042199192993792)), (13031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888149635678405/2475880078570760549798248448), (5294706126359/2475880078570760549798248448)), (6925/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769815475995253/154742504910672534362390528), (5292996040841/154742504910672534362390528)), (13855/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548263730514891/9671406556917033397649408), (1240091833645/2417851639229258349412352)), (12993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257659767102313/604462909807314587353088), (1084626384835/151115727451828646838272)), (5687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58936148255975/2361183241434822606848), (110104186749/1180591620717411303424)), (4623/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296162268748249/4722366482869645213696), (165063252523/147573952589676412928)), (6939/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809776667961427/295147905179352825856), (7257947968237/590295810358705651712)), (9547/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821104423930907/73786976294838206464), (9065186258117/73786976294838206464)), (11943/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909994026040813/4611686018427387904), (10188374094711/9223372036854775808)), (13449/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198904199750721/144115188075855872), (2543983329491/288230376151711744)), (26933/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298042304555297/36028797018963968), (8889959228299/144115188075855872)), (5901/36028797018963968), by norm_num⟩
  | 4 => ⟨((744006747080971/18014398509481984), (6653503808833/18014398509481984)), (35481/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484716351157271/9007199254740992), (8292477771173/4503599627370496)), (11121/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109415718088657/2251799813685248), (16511900917187/2251799813685248)), (44683/2251799813685248), by norm_num⟩
  | 1 => ⟨((137646563913653/140737488355328), (49171489180995/2251799813685248)), (16881/281474976710656), by norm_num⟩
  | 0 => ⟨((2152887866216225/2251799813685248), (24223120614773/562949953421312)), (274115/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2152887866216225/2251799813685248), (24223120614773/562949953421312)), (1045665749556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2054151520589171/2251799813685248), (92636409571577/1125899906842624)), (547739/2251799813685248), by norm_num⟩
  | 2 => ⟨((929303845437335/1125899906842624), (84505390055945/562949953421312)), (544729/1125899906842624), by norm_num⟩
  | 3 => ⟨((1483330779717897/2251799813685248), (278998811393093/1125899906842624)), (531383/562949953421312), by norm_num⟩
  | 4 => ⟨((838844040906159/2251799813685248), (735140880515109/2251799813685248)), (1926863/1125899906842624), by norm_num⟩
  | 5 => ⟨((144974886104205/4503599627370496), (547711695416991/2251799813685248)), (2693715/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1047104347749165/18014398509481984), (141050621246953/9007199254740992)), (23741219/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-26213402727/268435456)), (1/134217728), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-763070545/268435456), (-26517047019/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-23035327299995/2251799813685248), (516702733868523/9007199254740992)), (2798711/2251799813685248), by norm_num⟩
  | 1 => ⟨((144807207/4294967296), (-25985228257/137438953472)), (565/137438953472), by norm_num⟩
  | 2 => ⟨((-1909043725/34359738368), (21410768315/68719476736)), (117/17179869184), by norm_num⟩
  | 3 => ⟨((131081181/2147483648), (-23522133181/68719476736)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((-1728088755/34359738368), (9690639213/34359738368)), (427/68719476736), by norm_num⟩
  | 5 => ⟨((4556398901/137438953472), (-25551012779/137438953472)), (565/137438953472), by norm_num⟩
  | 6 => ⟨((-5005715825/274877906944), (28070656627/274877906944)), (623/274877906944), by norm_num⟩
  | 7 => ⟨((1178430197/137438953472), (-13216614995/274877906944)), (589/549755813888), by norm_num⟩
  | 8 => ⟨((-3883913687/1099511627776), (1361243967/68719476736)), (487/1099511627776), by norm_num⟩
  | 9 => ⟨((2844610203/2199023255552), (-7975889867/1099511627776)), (179/1099511627776), by norm_num⟩
  | 10 => ⟨((-3750148471/8796093022208), (10514892745/4398046511104)), (237/4398046511104), by norm_num⟩
  | 11 => ⟨((1123625235/8796093022208), (-6300976573/8796093022208)), (285/17592186044416), by norm_num⟩
  | 12 => ⟨((-1234428491/35184372088832), (27689321175/140737488355328)), (157/35184372088832), by norm_num⟩
  | 13 => ⟨((5007353759/562949953421312), (-7019960425/140737488355328)), (639/562949953421312), by norm_num⟩
  | 14 => ⟨((-4715263177/2251799813685248), (6610469819/562949953421312)), (151/562949953421312), by norm_num⟩
  | 15 => ⟨((518024607/1125899906842624), (-23239498807/9007199254740992)), (533/9007199254740992), by norm_num⟩
  | 16 => ⟨((-3414649195/36028797018963968), (19148399229/36028797018963968)), (441/36028797018963968), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (2276010235117/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777581962397249/633825300114114700748351602688), (2690125588463/633825300114114700748351602688)), (11559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888406815112897/39614081257132168796771975168), (378205936793/4951760157141521099596496896)), (6503/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236012323624417/309485009821345068724781056), (3213818220531/2475880078570760549798248448)), (13821/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884882498215341/77371252455336267181195264), (3212769921155/154742504910672534362390528)), (27/302231454903657293676544), by norm_num⟩
  | 13 => ⟨((774108503989115/4835703278458516698824704), (376357300837/1208925819614629174706176)), (12963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257619486366023/604462909807314587353088), (2633388188135/604462909807314587353088)), (5673/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((942946207280765/37778931862957161709568), (66830782773/1180591620717411303424)), (9221/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162014375757309/590295810358705651712), (3206053590405/4722366482869645213696)), (13837/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619489947316301/590295810358705651712), (4405361611447/590295810358705651712)), (19033/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821027580585905/73786976294838206464), (2751131109095/36893488147419103232)), (23803/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819904886434905/9223372036854775808), (772993207755/1152921504606846976)), (13397/4611686018427387904), by norm_num⟩
  | 6 => ⟨((198894315823665/144115188075855872), (1544082392013/288230376151711744)), (13407/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192104623471241/144115188075855872), (1348932838933/36028797018963968)), (23485/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487925754402069/36028797018963968), (4038255346273/18014398509481984)), (17637/18014398509481984), by norm_num⟩
  | 3 => ⟨((185577827344441/1125899906842624), (2516449871751/2251799813685248)), (44173/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218691501731381/4503599627370496), (20042330771611/4503599627370496)), (88587/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101126456339097/1125899906842624), (7460298298949/562949953421312)), (133489/2251799813685248), by norm_num⟩
  | 0 => ⟨((269146079740031/281474976710656), (3674897752891/140737488355328)), (269425/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((269146079740031/281474976710656), (3674897752891/140737488355328)), (1027774819380950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2057322283958749/2251799813685248), (112445868994207/2251799813685248)), (529319/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874025781942459/2251799813685248), (205468879262661/2251799813685248)), (1020073/2251799813685248), by norm_num⟩
  | 3 => ⟨((1540880832280141/2251799813685248), (170998316451087/1125899906842624)), (1884037/2251799813685248), by norm_num⟩
  | 4 => ⟨((1002465684850369/2251799813685248), (468048760942803/2251799813685248)), (3150735/2251799813685248), by norm_num⟩
  | 5 => ⟨((697990826632401/4503599627370496), (52091977585033/281474976710656)), (2057555/1125899906842624), by norm_num⟩
  | 6 => ⟨((-23035327299995/2251799813685248), (516702733868523/9007199254740992)), (2798711/2251799813685248), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-26517047019/268435456)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨52,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile052Terms3
