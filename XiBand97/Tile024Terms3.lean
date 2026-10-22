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
namespace Reinmann.XiBand97.Tile024Terms3
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-22364231/8388608), (-148512473/2097152)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-162902799073885/18014398509481984), (-1241868290586723/18014398509481984)), (52688785/2251799813685248), by norm_num⟩
  | 1 => ⟨((240106329/8589934592), (1830419353/8589934592)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-92772357/2147483648), (-707237991/2147483648)), (121/1073741824), by norm_num⟩
  | 3 => ⟨((191175529/4294967296), (728700885/2147483648)), (501/4294967296), by norm_num⟩
  | 4 => ⟨((-147732919/4294967296), (-563111343/2147483648)), (389/4294967296), by norm_num⟩
  | 5 => ⟨((91329745/4294967296), (696240427/4294967296)), (483/8589934592), by norm_num⟩
  | 6 => ⟨((-94101373/8589934592), (-1434739145/17179869184)), (499/17179869184), by norm_num⟩
  | 7 => ⟨((83106097/17179869184), (1267097031/34359738368)), (443/34359738368), by norm_num⟩
  | 8 => ⟨((-128442237/68719476736), (-979162679/68719476736)), (43/8589934592), by norm_num⟩
  | 9 => ⟨((88226757/137438953472), (336292601/68719476736)), (475/274877906944), by norm_num⟩
  | 10 => ⟨((-218170121/1099511627776), (-831595765/549755813888)), (589/1099511627776), by norm_num⟩
  | 11 => ⟨((30653323/549755813888), (1869452955/4398046511104)), (83/549755813888), by norm_num⟩
  | 12 => ⟨((-126334297/8796093022208), (-963093075/8796093022208)), (343/8796093022208), by norm_num⟩
  | 13 => ⟨((240310569/70368744177664), (915988179/35184372088832)), (655/70368744177664), by norm_num⟩
  | 14 => ⟨((-212231477/281474976710656), (-101119941/17592186044416)), (581/281474976710656), by norm_num⟩
  | 15 => ⟨((174937735/1125899906842624), (166701883/140737488355328)), (481/1125899906842624), by norm_num⟩
  | 16 => ⟨((-135184991/4503599627370496), (-1030565195/4503599627370496)), (373/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-277004797037/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888927077500937/316912650057057350374175801344), (-1310003243257/316912650057057350374175801344)), (46229/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236089121057979/4951760157141521099596496896), (-2946825051699/39614081257132168796771975168)), (3251/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1888423800241385/2475880078570760549798248448), (-3130149976605/2475880078570760549798248448)), (110553/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110630632587629/9671406556917033397649408), (-3129192272003/154742504910672534362390528)), (221149/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774260860492733/4835703278458516698824704), (-1466300276463/4835703278458516698824704)), (103687/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314471504652229/151115727451828646838272), (-1282504342825/302231454903657293676544)), (90749/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886325357666061/75557863725914323419136), (-260389592227/4722366482869645213696)), (295021/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296439563102415/4722366482869645213696), (-1561504265317/2361183241434822606848)), (221341/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202491996137433/73786976294838206464), (-4291430150783/590295810358705651712)), (304467/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910792370845805/36893488147419103232), (-5360230631473/73786976294838206464)), (11899/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1820531189430529/9223372036854775808), (-3012342786217/4611686018427387904)), (214309/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591780200781905/1152921504606846976), (-6017725055547/1152921504606846976)), (428935/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192651381341067/144115188075855872), (-5257688243165/144115188075855872)), (93919/36028797018963968), by norm_num⟩
  | 4 => ⟨((744372238999503/18014398509481984), (-3935456741001/18014398509481984)), (282115/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485643552147047/9007199254740992), (-9811361566117/9007199254740992)), (353271/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110362981636811/2251799813685248), (-19541092970105/4503599627370496)), (1416859/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205286120311801/2251799813685248), (-29108299975851/2251799813685248)), (1067377/1125899906842624), by norm_num⟩
  | 0 => ⟨((2159161286320219/2251799813685248), (-7175955686905/281474976710656)), (4307557/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159161286320219/2251799813685248), (-7175955686905/281474976710656)), (16432025918013762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1034435164766795/1125899906842624), (-110091816278517/2251799813685248)), (8480325/2251799813685248), by norm_num⟩
  | 2 => ⟨((1895419036129963/2251799813685248), (-101148286290303/1125899906842624)), (16412035/2251799813685248), by norm_num⟩
  | 3 => ⟨((788633473912887/1125899906842624), (-340560268530801/2251799813685248)), (15289007/1125899906842624), by norm_num⟩
  | 4 => ⟨((1053286226327659/2251799813685248), (-29818062202497/140737488355328)), (26042879/1125899906842624), by norm_num⟩
  | 5 => ⟨((783193923219455/4503599627370496), (-892639326754973/4503599627370496)), (141594745/4503599627370496), by norm_num⟩
  | 6 => ⟨((-162902799073885/18014398509481984), (-1241868290586723/18014398509481984)), (52688785/2251799813685248), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-148512473/2097152)), (1/8388608), by norm_num⟩, -11, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45371695/16777216), (-1205185647/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1099663398429011/18014398509481984), (-493678360728343/18014398509481984)), (433310659/18014398509481984), by norm_num⟩
  | 1 => ⟨((822064453/4294967296), (369054233/4294967296)), (163/2147483648), by norm_num⟩
  | 2 => ⟨((-1288789169/4294967296), (-289291853/2147483648)), (257/2147483648), by norm_num⟩
  | 3 => ⟨((1346996995/4294967296), (75589411/536870912)), (539/4294967296), by norm_num⟩
  | 4 => ⟨((-527937661/2147483648), (-237010161/2147483648)), (425/4294967296), by norm_num⟩
  | 5 => ⟨((662138193/4294967296), (594515191/8589934592)), (535/8589934592), by norm_num⟩
  | 6 => ⟨((-1384086983/17179869184), (-310683157/8589934592)), (561/17179869184), by norm_num⟩
  | 7 => ⟨((1239941923/34359738368), (69581803/4294967296)), (505/34359738368), by norm_num⟩
  | 8 => ⟨((-485978841/34359738368), (-218173341/34359738368)), (199/34359738368), by norm_num⟩
  | 9 => ⟨((1354474529/274877906944), (608072221/274877906944)), (557/274877906944), by norm_num⟩
  | 10 => ⟨((-424694705/274877906944), (-190660693/274877906944)), (351/549755813888), by norm_num⟩
  | 11 => ⟨((968456575/2199023255552), (434774909/2199023255552)), (201/1099511627776), by norm_num⟩
  | 12 => ⟨((-1012196663/8796093022208), (-113602851/2199023255552)), (211/4398046511104), by norm_num⟩
  | 13 => ⟨((488267197/17592186044416), (109600333/8796093022208)), (409/35184372088832), by norm_num⟩
  | 14 => ⟨((-437416849/70368744177664), (-24546515/8796093022208)), (23/8796093022208), by norm_num⟩
  | 15 => ⟨((1462952533/1125899906842624), (656771889/1125899906842624)), (309/562949953421312), by norm_num⟩
  | 16 => ⟨((-1146769801/4503599627370496), (-514826115/4503599627370496)), (243/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-3542613906111/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777789384003851/633825300114114700748351602688), (-4188142066875/633825300114114700748351602688)), (185225/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888639804273803/39614081257132168796771975168), (-4710539466809/39614081257132168796771975168)), (13027/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944172831539131/1237940039285380274899124224), (-5003565551429/2475880078570760549798248448)), (13845/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770011534524021/154742504910672534362390528), (-5002010470785/154742504910672534362390528)), (221589/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548447568375861/9671406556917033397649408), (-4687732999695/9671406556917033397649408)), (207813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628910329063055/302231454903657293676544), (-2050057535485/302231454903657293676544)), (90955/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471554563395643/18889465931478580854784), (-6659591885697/75557863725914323419136)), (147871/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324089613595929/1180591620717411303424), (-4991986787651/4722366482869645213696)), (221927/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619823177881999/590295810358705651712), (-6859584795879/590295810358705651712)), (152673/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821441855787397/73786976294838206464), (-8567889015473/73786976294838206464)), (381977/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56886494993375/288230376151711744), (-1203727122789/1152921504606846976)), (215065/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591613605198517/1152921504606846976), (-2404625749875/288230376151711744)), (215319/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192501969244015/144115188075855872), (-4201736940077/72057594037927936)), (377379/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488513104686399/36028797018963968), (-12579808296855/36028797018963968)), (141803/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485341699031945/9007199254740992), (-15680373376615/9007199254740992)), (711019/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220084587226071/4503599627370496), (-3903481931287/562949953421312)), (714033/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102115358661599/1125899906842624), (-46510498767425/2251799813685248)), (2157213/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156682114519627/2251799813685248), (-91701522662077/2251799813685248)), (1093789/562949953421312), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156682114519627/2251799813685248), (-91701522662077/2251799813685248)), (4172473909618186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((515461959097497/562949953421312), (-43913991065629/562949953421312)), (4368519/1125899906842624), by norm_num⟩
  | 2 => ⟨((1874216996109493/2251799813685248), (-321676791749029/2251799813685248)), (17363139/2251799813685248), by norm_num⟩
  | 3 => ⟨((1513994880644517/2251799813685248), (-133868940455085/562949953421312)), (33864121/2251799813685248), by norm_num⟩
  | 4 => ⟨((890597021517051/2251799813685248), (-720052961349553/2251799813685248)), (7705339/281474976710656), by norm_num⟩
  | 5 => ⟨((60992719227833/1125899906842624), (-142392103155685/562949953421312)), (11022831/281474976710656), by norm_num⟩
  | 6 => ⟨((-1099663398429011/18014398509481984), (-493678360728343/18014398509481984)), (433310659/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1205185647/16777216)), (1/8388608), by norm_num⟩, -11, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45987547/16777216), (-305386057/4194304)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-123589582131731/2251799813685248), (305191763321797/9007199254740992)), (423939943/18014398509481984), by norm_num⟩
  | 1 => ⟨((374578805/2147483648), (-462491919/4294967296)), (323/4294967296), by norm_num⟩
  | 2 => ⟨((-595215803/2147483648), (734912107/4294967296)), (515/4294967296), by norm_num⟩
  | 3 => ⟨((630542621/2147483648), (-778530079/4294967296)), (137/1073741824), by norm_num⟩
  | 4 => ⟨((-250487299/1073741824), (618552625/4294967296)), (437/4294967296), by norm_num⟩
  | 5 => ⟨((19901553/134217728), (-98289677/1073741824)), (279/4294967296), by norm_num⟩
  | 6 => ⟨((-337323769/4294967296), (416493179/8589934592)), (297/8589934592), by norm_num⟩
  | 7 => ⟨((1225180681/34359738368), (-94545553/4294967296)), (541/34359738368), by norm_num⟩
  | 8 => ⟨((-973422539/68719476736), (300470857/34359738368)), (27/4294967296), by norm_num⟩
  | 9 => ⟨((687464273/137438953472), (-424405581/137438953472)), (307/137438953472), by norm_num⟩
  | 10 => ⟨((-436959693/274877906944), (539513513/549755813888)), (49/68719476736), by norm_num⟩
  | 11 => ⟨((63121883/137438953472), (-623491995/2199023255552)), (455/2199023255552), by norm_num⟩
  | 12 => ⟨((-1069891957/8796093022208), (660497041/8796093022208)), (121/2199023255552), by norm_num⟩
  | 13 => ⟨((32693983/1099511627776), (-645875431/35184372088832)), (475/35184372088832), by norm_num⟩
  | 14 => ⟨((-949972461/140737488355328), (586464825/140737488355328)), (433/140737488355328), by norm_num⟩
  | 15 => ⟨((805083631/562949953421312), (-497017809/562949953421312)), (369/562949953421312), by norm_num⟩
  | 16 => ⟨((-639649779/2251799813685248), (197443669/1125899906842624)), (589/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (3371828362247/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777733742323489/633825300114114700748351602688), (3985994574115/633825300114114700748351602688)), (185185/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944288635747731/19807040628566084398385987584), (1120791651515/9903520314283042199192993792)), (208385/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888279305709585/2475880078570760549798248448), (4762031090253/2475880078570760549798248448)), (221467/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884972635626931/77371252455336267181195264), (4760531406619/154742504910672534362390528)), (55383/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548385546474199/9671406556917033397649408), (4461405252177/9671406556917033397649408)), (207757/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257766488802573/604462909807314587353088), (487767148117/75557863725914323419136)), (90929/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235766301934509/9444732965739290427392), (6337988283291/75557863725914323419136)), (295649/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296292739311097/4722366482869645213696), (4750880778269/4722366482869645213696)), (55463/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619733085063233/590295810358705651712), (204006913401/18446744073709551616)), (305233/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910664818680139/36893488147419103232), (1019240059201/9223372036854775808)), (190911/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820242139919769/9223372036854775808), (4582213478853/4611686018427387904)), (429935/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591488586410149/1152921504606846976), (9153519003281/1152921504606846976)), (215209/576460752303423488), by norm_num⟩
  | 5 => ⟨((149049167788095/18014398509481984), (1999267517825/36028797018963968)), (47145/18014398509481984), by norm_num⟩
  | 4 => ⟨((186043961124757/4503599627370496), (11971117965999/36028797018963968)), (141707/9007199254740992), by norm_num⟩
  | 3 => ⟨((742571294032587/4503599627370496), (7460557312763/4503599627370496)), (177611/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219694302824655/4503599627370496), (7428539824775/1125899906842624)), (1426625/4503599627370496), by norm_num⟩
  | 1 => ⟨((275458125059025/281474976710656), (44252038449989/2251799813685248)), (2154327/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155628717884899/2251799813685248), (87233116951097/2251799813685248)), (2183237/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155628717884899/2251799813685248), (87233116951097/2251799813685248)), (8328388218406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((515046400270901/562949953421312), (167015034735837/2251799813685248)), (4349143/1125899906842624), by norm_num⟩
  | 2 => ⟨((1872489136671439/2251799813685248), (305606180119655/2251799813685248)), (17206529/2251799813685248), by norm_num⟩
  | 3 => ⟨((1515596727952417/2251799813685248), (508254995755761/2251799813685248)), (33286673/2251799813685248), by norm_num⟩
  | 4 => ⟨((452684623357543/1125899906842624), (342086185393287/1125899906842624)), (59834175/2251799813685248), by norm_num⟩
  | 5 => ⟨((78071247233629/1125899906842624), (17192598010871/70368744177664)), (168947369/4503599627370496), by norm_num⟩
  | 6 => ⟨((-123589582131731/2251799813685248), (305191763321797/9007199254740992)), (423939943/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-305386057/4194304)), (1/8388608), by norm_num⟩, -12, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2911141/1048576), (-1237234923/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-92416347305419/18014398509481984), (558968863949395/9007199254740992)), (373494383/18014398509481984), by norm_num⟩
  | 1 => ⟨((70923983/4294967296), (-857949907/4294967296)), (575/8589934592), by norm_num⟩
  | 2 => ⟨((-114147747/4294967296), (345204277/1073741824)), (465/4294967296), by norm_num⟩
  | 3 => ⟨((3827369/134217728), (-1481559603/4294967296)), (501/4294967296), by norm_num⟩
  | 4 => ⟨((-24639651/1073741824), (1192239097/4294967296)), (405/4294967296), by norm_num⟩
  | 5 => ⟨((126899163/8589934592), (-1535067843/8589934592)), (523/8589934592), by norm_num⟩
  | 6 => ⟨((-136157549/17179869184), (1647064257/17179869184)), (563/17179869184), by norm_num⟩
  | 7 => ⟨((31305303/8589934592), (-1514770091/34359738368)), (65/4294967296), by norm_num⟩
  | 8 => ⟨((-100767883/68719476736), (1218964207/68719476736)), (105/17179869184), by norm_num⟩
  | 9 => ⟨((72079845/137438953472), (-871932093/137438953472)), (603/274877906944), by norm_num⟩
  | 10 => ⟨((-23201607/137438953472), (561328227/274877906944)), (195/274877906944), by norm_num⟩
  | 11 => ⟨((1697343/34359738368), (-328517429/549755813888)), (229/1099511627776), by norm_num⟩
  | 12 => ⟨((-58277721/4398046511104), (704971207/4398046511104)), (493/8796093022208), by norm_num⟩
  | 13 => ⟨((115439229/35184372088832), (-698219931/17592186044416)), (245/17592186044416), by norm_num⟩
  | 14 => ⟨((-26541753/35184372088832), (1284276147/140737488355328)), (453/140737488355328), by norm_num⟩
  | 15 => ⟨((11391281/70368744177664), (-551190059/281474976710656)), (391/562949953421312), by norm_num⟩
  | 16 => ⟨((-36667119/1125899906842624), (443553089/1125899906842624)), (631/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (1076788027157/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777684572804735/633825300114114700748351602688), (79552936403/19807040628566084398385987584)), (92451/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888522245469571/39614081257132168796771975168), (11184444287/154742504910672534362390528)), (208047/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888221228464831/2475880078570760549798248448), (190081704565/154742504910672534362390528)), (221087/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884943814961403/77371252455336267181195264), (3040338434607/154742504910672534362390528)), (221129/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548331970507029/9671406556917033397649408), (2849288277369/9671406556917033397649408)), (103677/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257720072187101/604462909807314587353088), (1246049335809/302231454903657293676544)), (181479/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886055854490751/75557863725914323419136), (4047732692461/75557863725914323419136)), (294987/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648118787716717/2361183241434822606848), (3034113747967/4722366482869645213696)), (110657/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619658462941941/590295810358705651712), (4169168751721/590295810358705651712)), (152213/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821238199071195/73786976294838206464), (5207357482043/73786976294838206464)), (47589/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820141796174363/9223372036854775808), (731579977143/1152921504606846976)), (428547/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397847847723941/288230376151711744), (365350029971/72057594037927936)), (53607/144115188075855872), by norm_num⟩
  | 5 => ⟨((596155914065199/72057594037927936), (5106991261405/144115188075855872)), (375597/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488236456935111/36028797018963968), (3822346894029/18014398509481984)), (564091/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485010811351455/9007199254740992), (9528285950441/9007199254740992)), (706335/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109733659590103/2251799813685248), (4743513558939/1125899906842624)), (708171/2251799813685248), by norm_num⟩
  | 1 => ⟨((275426897643773/281474976710656), (7063894262243/562949953421312)), (1066863/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155487116131851/2251799813685248), (55693861629463/2251799813685248)), (2152245/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155487116131851/2251799813685248), (55693861629463/2251799813685248)), (8210163120750045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030958185840803/1125899906842624), (53311755538993/1125899906842624)), (8453689/2251799813685248), by norm_num⟩
  | 2 => ⟨((470749056479707/562949953421312), (195264926981297/2251799813685248)), (2035279/281474976710656), by norm_num⟩
  | 3 => ⟨((1557663507119295/2251799813685248), (163284106484739/1125899906842624)), (30054831/2251799813685248), by norm_num⟩
  | 4 => ⟨((515069943072067/1125899906842624), (225900803808673/1125899906842624)), (50297781/2251799813685248), by norm_num⟩
  | 5 => ⟨((761225298244233/4503599627370496), (413374984580867/2251799813685248)), (132406745/4503599627370496), by norm_num⟩
  | 6 => ⟨((-92416347305419/18014398509481984), (558968863949395/9007199254740992)), (373494383/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1237234923/16777216)), (1/8388608), by norm_num⟩, -12, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47145793/16777216), (-1252310135/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((789972174811695/18014398509481984), (92866893398295/2251799813685248)), (245017985/18014398509481984), by norm_num⟩
  | 1 => ⟨((-153410769/1073741824), (-144276287/1073741824)), (3/67108864), by norm_num⟩
  | 2 => ⟨((999654191/4294967296), (940132143/4294967296)), (315/4294967296), by norm_num⟩
  | 3 => ⟨((-271414155/1073741824), (-3988335/16777216)), (43/536870912), by norm_num⟩
  | 4 => ⟨((884293519/4294967296), (831640349/4294967296)), (141/2147483648), by norm_num⟩
  | 5 => ⟨((-576222731/4294967296), (-135478227/1073741824)), (93/2147483648), by norm_num⟩
  | 6 => ⟨((156449107/2147483648), (588534857/8589934592)), (51/2147483648), by norm_num⟩
  | 7 => ⟨((-36409021/1073741824), (-547858109/17179869184)), (191/17179869184), by norm_num⟩
  | 8 => ⟨((474496421/34359738368), (111560913/8589934592)), (313/68719476736), by norm_num⟩
  | 9 => ⟨((-85886397/17179869184), (-646179955/137438953472)), (229/137438953472), by norm_num⟩
  | 10 => ⟨((895443753/549755813888), (421063335/274877906944)), (75/137438953472), by norm_num⟩
  | 11 => ⟨((-530444035/1099511627776), (-249429999/549755813888)), (357/2199023255552), by norm_num⟩
  | 12 => ⟨((576079291/4398046511104), (541778011/4398046511104)), (49/1099511627776), by norm_num⟩
  | 13 => ⟨((-144378611/4398046511104), (-543127711/17592186044416)), (99/8796093022208), by norm_num⟩
  | 14 => ⟨((1075198749/140737488355328), (252794645/35184372088832)), (371/140737488355328), by norm_num⟩
  | 15 => ⟨((-934160353/562949953421312), (-439268991/281474976710656)), (325/562949953421312), by norm_num⟩
  | 16 => ⟨((760896153/2251799813685248), (357795195/1125899906842624)), (267/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (491555447861/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777635238975823/633825300114114700748351602688), (581024195865/316912650057057350374175801344)), (184629/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888466908663859/39614081257132168796771975168), (1306988880437/39614081257132168796771975168)), (207723/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944081326217357/1237940039285380274899124224), (1388277850383/2475880078570760549798248448)), (220723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884914650171813/77371252455336267181195264), (1387830526203/154742504910672534362390528)), (110371/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548277548167579/9671406556917033397649408), (1300616035517/9671406556917033397649408)), (103483/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257672714041137/604462909807314587353088), (284391043109/151115727451828646838272)), (45279/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885979387120983/75557863725914323419136), (1847651896327/75557863725914323419136)), (18397/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296180652812245/4722366482869645213696), (1384960749629/4722366482869645213696)), (110399/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((395405490413/144115188075855872), (951528695853/295147905179352825856)), (303651/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910571135616065/36893488147419103232), (1188463919957/36893488147419103232)), (189823/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820035304545373/9223372036854775808), (333930279821/1152921504606846976)), (427215/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591286679202519/1152921504606846976), (2668194054011/1152921504606846976)), (213679/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192222202265483/144115188075855872), (2331020797203/144115188075855872)), (187049/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488105997998615/36028797018963968), (3489246194885/36028797018963968)), (140367/9007199254740992), by norm_num⟩
  | 3 => ⟨((742427335653491/4503599627370496), (4348838186015/9007199254740992)), (351199/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109587857930323/2251799813685248), (4329817102485/2251799813685248)), (351623/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203029035563775/2251799813685248), (12894752445963/2251799813685248)), (1057003/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154917282106809/2251799813685248), (25413139099365/2251799813685248)), (265327/140737488355328), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154917282106809/2251799813685248), (25413139099365/2251799813685248)), (1012142181933355287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1030958133326479/1125899906842624), (12159875914587/562949953421312)), (2055247/562949953421312), by norm_num⟩
  | 2 => ⟨((1886994067389099/2251799813685248), (11134491528239/281474976710656)), (15410655/2251799813685248), by norm_num⟩
  | 3 => ⟨((1577765513198655/2251799813685248), (149290140833935/2251799813685248)), (6761821/562949953421312), by norm_num⟩
  | 4 => ⟨((1095593157746677/2251799813685248), (209205839912443/2251799813685248)), (20744369/1125899906842624), by norm_num⟩
  | 5 => ⟨((1027229220660665/4503599627370496), (407148957692839/4503599627370496)), (6010133/281474976710656), by norm_num⟩
  | 6 => ⟨((789972174811695/18014398509481984), (92866893398295/2251799813685248)), (245017985/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1252310135/16777216)), (1/8388608), by norm_num⟩, -12, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47691909/16777216), (-633408167/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1043373617619655/18014398509481984), (-115145327556839/18014398509481984)), (36373927/9007199254740992), by norm_num⟩
  | 1 => ⟨((-819871243/4294967296), (45239951/2147483648)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((675540467/2147483648), (-74551749/2147483648)), (97/4294967296), by norm_num⟩
  | 3 => ⟨((-1484314117/4294967296), (163806935/4294967296)), (27/1073741824), by norm_num⟩
  | 4 => ⟨((1223014297/4294967296), (-67485117/2147483648)), (91/4294967296), by norm_num⟩
  | 5 => ⟨((-1612342243/8589934592), (177935949/8589934592)), (61/4294967296), by norm_num⟩
  | 6 => ⟨((885669501/8589934592), (-48870655/4294967296)), (17/2147483648), by norm_num⟩
  | 7 => ⟨((-1668012681/34359738368), (11504979/2147483648)), (65/17179869184), by norm_num⟩
  | 8 => ⟨((687187211/34359738368), (-18959267/8589934592)), (109/68719476736), by norm_num⟩
  | 9 => ⟨((-503301543/68719476736), (27771845/34359738368)), (81/137438953472), by norm_num⟩
  | 10 => ⟨((82939989/34359738368), (-146450353/549755813888)), (27/137438953472), by norm_num⟩
  | 11 => ⟨((-1590438827/2199023255552), (175518717/2199023255552)), (131/2199023255552), by norm_num⟩
  | 12 => ⟨((218409455/1099511627776), (-192827019/8796093022208)), (73/4398046511104), by norm_num⟩
  | 13 => ⟨((-885959303/17592186044416), (24443323/4398046511104)), (75/17592186044416), by norm_num⟩
  | 14 => ⟨((417139619/35184372088832), (-184139897/140737488355328)), (143/140737488355328), by norm_num⟩
  | 15 => ⟨((-1466479077/562949953421312), (161838683/562949953421312)), (127/562949953421312), by norm_num⟩
  | 16 => ⟨((1208318951/2251799813685248), (-66674237/1125899906842624)), (107/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-143175123545/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777585830626067/633825300114114700748351602688), (-84612770527/316912650057057350374175801344)), (92217/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944205688209649/19807040628566084398385987584), (-47583089933/9903520314283042199192993792)), (51873/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888103718618749/2475880078570760549798248448), (-25271191963/309485009821345068724781056)), (110231/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769770444284447/154742504910672534362390528), (-202103651987/154742504910672534362390528)), (110233/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548222453166489/9671406556917033397649408), (-47350550665/2417851639229258349412352)), (103345/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628812294199753/302231454903657293676544), (-82828495221/302231454903657293676544)), (22607/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885901337462667/75557863725914323419136), (-269061550423/75557863725914323419136)), (36737/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296122250615541/4722366482869645213696), (-201681558721/4722366482869645213696)), (55107/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619500804884209/590295810358705651712), (-69281511887/147573952589676412928)), (151549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821042494695745/73786976294838206464), (-346128653633/73786976294838206464)), (94721/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909961753263753/4611686018427387904), (-389011625805/9223372036854775808)), (213131/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591175443233953/1152921504606846976), (-12141666161/36028797018963968)), (106571/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192125501475359/144115188075855872), (-339429349317/144115188075855872)), (11657/9007199254740992), by norm_num⟩
  | 4 => ⟨((1487962204129589/36028797018963968), (-127017849877/9007199254740992)), (139897/18014398509481984), by norm_num⟩
  | 3 => ⟨((742338560094891/4503599627370496), (-633216607101/9007199254740992)), (349789/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109413575535981/2251799813685248), (-315208261427/1125899906842624)), (699721/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202522405816565/2251799813685248), (-938655552535/1125899906842624)), (1049951/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153968139762571/2251799813685248), (-462404816921/281474976710656)), (2101447/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153968139762571/2251799813685248), (-462404816921/281474976710656)), (8016384133345793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060380782763045/2251799813685248), (-1769260726051/562949953421312)), (4027201/2251799813685248), by norm_num⟩
  | 2 => ⟨((471302872888989/562949953421312), (-12950887649953/2251799813685248)), (7395035/2251799813685248), by norm_num⟩
  | 3 => ⟨((1578228500067041/2251799813685248), (-21685020200427/2251799813685248)), (12467341/2251799813685248), by norm_num⟩
  | 4 => ⟨((1105930883903547/2251799813685248), (-7599236108123/562949953421312)), (2214525/281474976710656), by norm_num⟩
  | 5 => ⟨((542747689343081/2251799813685248), (-14928911273501/1125899906842624)), (35760571/4503599627370496), by norm_num⟩
  | 6 => ⟨((1043373617619655/18014398509481984), (-115145327556839/18014398509481984)), (36373927/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-633408167/8388608)), (1/16777216), by norm_num⟩, -12, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile024Terms3
