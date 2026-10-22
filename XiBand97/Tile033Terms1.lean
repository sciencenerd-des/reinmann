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
namespace Reinmann.XiBand97.Tile033Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32189/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32189/1280))
  have he : value ((69/80), (32189/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/8388608), (-463512941/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((370456729873479/9007199254740992), (651065570395455/4503599627370496)), (12328721/562949953421312), by norm_num⟩
  | 1 => ⟨((-12129197/134217728), (-42633333/134217728)), (209/4294967296), by norm_num⟩
  | 2 => ⟨((106602279/1073741824), (749400057/2147483648)), (29/536870912), by norm_num⟩
  | 3 => ⟨((-156152765/2147483648), (-1097733483/4294967296)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((343102693/8589934592), (602991747/4294967296)), (191/8589934592), by norm_num⟩
  | 5 => ⟨((-75387367/4294967296), (-1059926629/17179869184)), (85/8589934592), by norm_num⟩
  | 6 => ⟨((220857301/34359738368), (1552597893/68719476736)), (63/17179869184), by norm_num⟩
  | 7 => ⟨((-277298909/137438953472), (-243671875/34359738368)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((304643989/549755813888), (1070803665/549755813888)), (89/274877906944), by norm_num⟩
  | 9 => ⟨((-148749169/1099511627776), (-1045687169/2199023255552)), (11/137438953472), by norm_num⟩
  | 10 => ⟨((32683533/1099511627776), (919043819/8796093022208)), (157/8796093022208), by norm_num⟩
  | 11 => ⟨((-104455363/17592186044416), (-1468615031/70368744177664)), (127/35184372088832), by norm_num⟩
  | 12 => ⟨((306015855/281474976710656), (1075625681/281474976710656)), (189/281474976710656), by norm_num⟩
  | 13 => ⟨((-25860983/140737488355328), (-727197287/1125899906842624)), (129/1125899906842624), by norm_num⟩
  | 14 => ⟨((129879743/4503599627370496), (913037573/9007199254740992)), (41/2251799813685248), by norm_num⟩
  | 15 => ⟨((-304399961/72057594037927936), (-534972959/36028797018963968)), (97/36028797018963968), by norm_num⟩
  | 16 => ⟨((167208769/288230376151711744), (587727867/288230376151711744)), (215/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (421270915829/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889521865133123/316912650057057350374175801344), (1994799716415/633825300114114700748351602688)), (23099/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890051056277865/39614081257132168796771975168), (2243774485333/39614081257132168796771975168)), (103959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889845301639237/2475880078570760549798248448), (2383549283731/2475880078570760549798248448)), (110471/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885755689358653/77371252455336267181195264), (1191515337045/77371252455336267181195264)), (110487/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96865868147815/604462909807314587353088), (2233540369355/9671406556917033397649408)), (103599/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157381425930591/75557863725914323419136), (976898543795/302231454903657293676544)), (90667/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118013664260331/4722366482869645213696), (1586943980517/37778931862957161709568)), (73683/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297859090375213/4722366482869645213696), (2379513025613/4722366482869645213696)), (110553/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621887127426967/590295810358705651712), (1635181864743/295147905179352825856)), (152057/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912011325985281/36893488147419103232), (1021438924851/18446744073709551616)), (190141/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911636205778325/4611686018427387904), (1148363327011/2305843009213693952)), (214005/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594519638944961/1152921504606846976), (2294839284475/576460752303423488)), (214125/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195046382379881/144115188075855872), (4011725709273/144115188075855872)), (187495/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492332963874837/36028797018963968), (3004555669021/18014398509481984)), (140757/18014398509481984), by norm_num⟩
  | 3 => ⟨((93132633118291/562949953421312), (7496573925949/9007199254740992)), (22023/562949953421312), by norm_num⟩
  | 2 => ⟨((2229662021536811/4503599627370496), (14948781623527/4503599627370496)), (353081/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218637435979215/2251799813685248), (11156267390043/1125899906842624)), (1062821/2251799813685248), by norm_num⟩
  | 0 => ⟨((546413166391267/562949953421312), (5523022930053/281474976710656)), (1070001/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546413166391267/562949953421312), (5523022930053/281474976710656)), (4081729893210982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2120581635811809/2251799813685248), (85772525359909/2251799813685248)), (1059565/562949953421312), by norm_num⟩
  | 2 => ⟨((1993742747801473/2251799813685248), (20193584819353/281474976710656)), (1038181/281474976710656), by norm_num⟩
  | 3 => ⟨((1753669284839957/2251799813685248), (286070284159471/2251799813685248)), (7949491/1125899906842624), by norm_num⟩
  | 4 => ⟨((1329389821830065/2251799813685248), (222787419906069/1125899906842624)), (14401717/1125899906842624), by norm_num⟩
  | 5 => ⟨((348330333579785/1125899906842624), (16440811404223/70368744177664)), (709503/35184372088832), by norm_num⟩
  | 6 => ⟨((370456729873479/9007199254740992), (651065570395455/4503599627370496)), (12328721/562949953421312), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-463512941/8388608)), (1/16777216), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66638419/33554432), (-1942956581/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((131777166593519/4503599627370496), (-603890883632935/4503599627370496)), (92383013/4503599627370496), by norm_num⟩
  | 1 => ⟨((-289371623/4294967296), (663046907/2147483648)), (103/2147483648), by norm_num⟩
  | 2 => ⟨((333151393/4294967296), (-381680481/1073741824)), (15/268435456), by norm_num⟩
  | 3 => ⟨((-31962893/536870912), (1171802381/4294967296)), (93/2147483648), by norm_num⟩
  | 4 => ⟨((73597281/2147483648), (-1349087347/8589934592)), (217/8589934592), by norm_num⟩
  | 5 => ⟨((-271142403/17179869184), (621277683/8589934592)), (101/8589934592), by norm_num⟩
  | 6 => ⟨((208109485/34359738368), (-119212061/4294967296)), (157/34359738368), by norm_num⟩
  | 7 => ⟨((-136911371/68719476736), (1254838467/137438953472)), (209/137438953472), by norm_num⟩
  | 8 => ⟨((157625041/274877906944), (-722343087/274877906944)), (243/549755813888), by norm_num⟩
  | 9 => ⟨((-20163615/137438953472), (1478450155/2199023255552)), (251/2199023255552), by norm_num⟩
  | 10 => ⟨((74285503/2199023255552), (-1361702915/8796093022208)), (117/4398046511104), by norm_num⟩
  | 11 => ⟨((-248798097/35184372088832), (1140158849/35184372088832)), (99/17592186044416), by norm_num⟩
  | 12 => ⟨((381919193/281474976710656), (-1750208513/281474976710656)), (153/140737488355328), by norm_num⟩
  | 13 => ⟨((-270585059/1125899906842624), (1240001241/1125899906842624)), (219/1125899906842624), by norm_num⟩
  | 14 => ⟨((356025785/9007199254740992), (-815773821/4503599627370496)), (291/9007199254740992), by norm_num⟩
  | 15 => ⟨((-218607911/36028797018963968), (1001807275/36028797018963968)), (181/36028797018963968), by norm_num⟩
  | 16 => ⟨((251681659/288230376151711744), (-1153373249/288230376151711744)), (211/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-1766277111227/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889451700555287/316912650057057350374175801344), (-2090602916471/633825300114114700748351602688)), (92407/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472473300350345/9903520314283042199192993792), (-2351516917953/39614081257132168796771975168)), (51985/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889677598597815/2475880078570760549798248448), (-312247539755/309485009821345068724781056)), (27621/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771343695670155/154742504910672534362390528), (-2497410767169/154742504910672534362390528)), (110501/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549696708756877/9671406556917033397649408), (-1170358800969/4835703278458516698824704)), (25903/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258913894791345/604462909807314587353088), (-2047523084345/604462909807314587353088)), (11335/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471998802491355/18889465931478580854784), (-415761418895/9444732965739290427392)), (36847/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297691561615495/4722366482869645213696), (-1246788465805/2361183241434822606848)), (27643/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621656832099593/590295810358705651712), (-3427057656985/590295810358705651712)), (38021/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455933716980827/18446744073709551616), (-4281407353479/73786976294838206464)), (95089/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822948771590957/9223372036854775808), (-150414531703/288230376151711744)), (214051/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594196145426103/1152921504606846976), (-4809120158401/1152921504606846976)), (107089/576460752303423488), by norm_num⟩
  | 5 => ⟨((597381745211721/72057594037927936), (-1050830313039/36028797018963968)), (46887/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491908955983643/36028797018963968), (-6295674289695/36028797018963968)), (140803/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489592698272345/9007199254740992), (-3926663738449/4503599627370496)), (352505/9007199254740992), by norm_num⟩
  | 2 => ⟨((139287805979967/281474976710656), (-15657950276689/4503599627370496)), (706507/4503599627370496), by norm_num⟩
  | 1 => ⟨((554264024963101/562949953421312), (-23365483445903/2251799813685248)), (531757/1125899906842624), by norm_num⟩
  | 0 => ⟨((545626864625441/562949953421312), (-46247113748377/2251799813685248)), (2142091/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545626864625441/562949953421312), (-46247113748377/2251799813685248)), (8171428689009856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2114397550772373/2251799813685248), (-11205999538301/281474976710656)), (2120169/1125899906842624), by norm_num⟩
  | 2 => ⟨((1981810377791529/2251799813685248), (-168355555116335/2251799813685248)), (4150413/1125899906842624), by norm_num⟩
  | 3 => ⟨((1731605428194027/2251799813685248), (-148169825870251/1125899906842624)), (7926173/1125899906842624), by norm_num⟩
  | 4 => ⟨((323145973286347/562949953421312), (-227881424638357/1125899906842624)), (28552883/2251799813685248), by norm_num⟩
  | 5 => ⟨((162431551102633/562949953421312), (-523236314781465/2251799813685248)), (22169085/1125899906842624), by norm_num⟩
  | 6 => ⟨((131777166593519/4503599627370496), (-603890883632935/4503599627370496)), (92383013/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1942956581/33554432)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-34698381/16777216), (-2023380771/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-58282161732805/562949953421312), (653399100964681/9007199254740992)), (12896281/562949953421312), by norm_num⟩
  | 1 => ⟨((1066242371/4294967296), (-373550085/2147483648)), (119/2147483648), by norm_num⟩
  | 2 => ⟨((-639184385/2147483648), (447866991/2147483648)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((3991399/16777216), (-89494845/536870912)), (235/4294967296), by norm_num⟩
  | 4 => ⟨((-612541235/4294967296), (858397063/8589934592)), (71/2147483648), by norm_num⟩
  | 5 => ⟨((1175047785/17179869184), (-102917313/2147483648)), (275/17179869184), by norm_num⟩
  | 6 => ⟨((-939213843/34359738368), (658093169/34359738368)), (111/17179869184), by norm_num⟩
  | 7 => ⟨((643467553/68719476736), (-450868143/68719476736)), (77/34359738368), by norm_num⟩
  | 8 => ⟨((-385741951/137438953472), (270283647/137438953472)), (187/274877906944), by norm_num⟩
  | 9 => ⟨((411097245/549755813888), (-72012431/137438953472)), (101/549755813888), by norm_num⟩
  | 10 => ⟨((-49288407/274877906944), (552570457/4398046511104)), (49/1099511627776), by norm_num⟩
  | 11 => ⟨((343820911/8796093022208), (-481820395/17592186044416)), (173/17592186044416), by norm_num⟩
  | 12 => ⟨((-549631025/70368744177664), (770236565/140737488355328)), (279/140737488355328), by norm_num⟩
  | 13 => ⟨((811050853/562949953421312), (-568291267/562949953421312)), (13/35184372088832), by norm_num⟩
  | 14 => ⟨((-1111322861/4503599627370496), (194671849/1125899906842624)), (287/4503599627370496), by norm_num⟩
  | 15 => ⟨((710622889/18014398509481984), (-497922887/18014398509481984)), (185/18014398509481984), by norm_num⟩
  | 16 => ⟨((-851999633/144115188075855872), (149245867/36028797018963968)), (7/4503599627370496), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (3296137666773/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111173178741795/39614081257132168796771975168), (3900848984361/633825300114114700748351602688)), (11573/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889743790596455/39614081257132168796771975168), (4387643161301/39614081257132168796771975168)), (52091/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472379613591023/618970019642690137449562112), (145652664185/77371252455336267181195264)), (55361/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221398013392151/19342813113834066795298816), (1164944138799/38685626227668133590597632)), (55377/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549546622756933/9671406556917033397649408), (4367362717207/9671406556917033397649408)), (51933/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314695524537073/151115727451828646838272), (3820264786679/604462909807314587353088)), (90917/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943890078658557/37778931862957161709568), (3102861373509/37778931862957161709568)), (36951/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324382375043045/1180591620717411303424), (4652360922111/4722366482869645213696)), (110909/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810716372302923/295147905179352825856), (1598464753975/147573952589676412928)), (152591/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823452881527605/73786976294838206464), (7987619375859/73786976294838206464)), (190875/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822628960017091/9223372036854775808), (8979605669177/9223372036854775808)), (214923/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593873118801813/1152921504606846976), (4485763315425/576460752303423488)), (215159/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298619308375687/36028797018963968), (1960250467355/36028797018963968)), (188529/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491472374096017/36028797018963968), (11743347416613/36028797018963968)), (70831/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489034423625171/9007199254740992), (7323720227493/4503599627370496)), (355085/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113725445280693/2251799813685248), (7299940524949/1125899906842624)), (178241/1125899906842624), by norm_num⟩
  | 1 => ⟨((276904012768751/281474976710656), (1361320037311/70368744177664)), (269113/562949953421312), by norm_num⟩
  | 0 => ⟨((1089245693690043/1125899906842624), (43088625825755/1125899906842624)), (1090507/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089245693690043/1125899906842624), (43088625825755/1125899906842624)), (4159954075339889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((526067878835135/562949953421312), (83371709762981/1125899906842624)), (2193479/1125899906842624), by norm_num⟩
  | 2 => ⟨((488515366194693/562949953421312), (19477387929121/140737488355328)), (2212197/562949953421312), by norm_num⟩
  | 3 => ⟨((1652561570322117/2251799813685248), (135216329464223/562949953421312)), (4451705/562949953421312), by norm_num⟩
  | 4 => ⟨((1082877988010129/2251799813685248), (793865630131269/2251799813685248)), (8672609/562949953421312), by norm_num⟩
  | 5 => ⟨((240874919216493/2251799813685248), (1527062238983031/4503599627370496)), (115649811/4503599627370496), by norm_num⟩
  | 6 => ⟨((-58282161732805/562949953421312), (653399100964681/9007199254740992)), (12896281/562949953421312), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-2023380771/33554432)), (1/16777216), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17978733/8388608), (-4095317/65536)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((995047693973475/9007199254740992), (354533917944669/9007199254740992)), (88475003/4503599627370496), by norm_num⟩
  | 1 => ⟨((-589513929/2147483648), (-420085759/4294967296)), (53/1073741824), by norm_num⟩
  | 2 => ⟨((732443541/2147483648), (130484237/1073741824)), (133/2147483648), by norm_num⟩
  | 3 => ⟨((-1213369217/4294967296), (-432321531/4294967296)), (111/2147483648), by norm_num⟩
  | 4 => ⟨((753777309/4294967296), (537139323/8589934592)), (279/8589934592), by norm_num⟩
  | 5 => ⟨((-749226499/8589934592), (-266948215/8589934592)), (35/2147483648), by norm_num⟩
  | 6 => ⟨((1241171939/34359738368), (110556899/8589934592)), (117/17179869184), by norm_num⟩
  | 7 => ⟨((-881198973/68719476736), (-156984899/34359738368)), (21/8589934592), by norm_num⟩
  | 8 => ⟨((547424297/137438953472), (390092819/274877906944)), (211/274877906944), by norm_num⟩
  | 9 => ⟨((-1209154023/1099511627776), (-215409831/549755813888)), (235/1099511627776), by norm_num⟩
  | 10 => ⟨((1201853949/4398046511104), (428218657/4398046511104)), (59/1099511627776), by norm_num⟩
  | 11 => ⟨((-542999067/8796093022208), (-193469707/8796093022208)), (215/17592186044416), by norm_num⟩
  | 12 => ⟨((899534661/70368744177664), (160251387/35184372088832)), (45/17592186044416), by norm_num⟩
  | 13 => ⟨((-687772203/281474976710656), (-122526073/140737488355328)), (139/281474976710656), by norm_num⟩
  | 14 => ⟨((30518745/70368744177664), (347960975/2251799813685248)), (25/281474976710656), by norm_num⟩
  | 15 => ⟨((-1294271699/18014398509481984), (-461146955/18014398509481984)), (267/18014398509481984), by norm_num⟩
  | 16 => ⟨((100504511/9007199254740992), (17904799/4503599627370496)), (21/9007199254740992), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (111462793597/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889331585469919/316912650057057350374175801344), (131895484145/158456325028528675187087900672)), (23063/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944811557888291/19807040628566084398385987584), (593418842379/39614081257132168796771975168)), (103787/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889390854607177/2475880078570760549798248448), (630369713383/2475880078570760549798248448)), (220555/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771057201246487/154742504910672534362390528), (315107370637/77371252455336267181195264)), (55141/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549428385260157/9671406556917033397649408), (590661715569/9671406556917033397649408)), (51697/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258679376600265/604462909807314587353088), (129166114235/151115727451828646838272)), (180949/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235951826775021/9444732965739290427392), (104908918755/9444732965739290427392)), (294059/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297406548716825/4722366482869645213696), (629183796895/4722366482869645213696)), (13785/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621265643868387/590295810358705651712), (864689672305/590295810358705651712)), (151647/295147905179352825856), by norm_num⟩
  | 8 => ⟨((56976466821865/2305843009213693952), (1080205436569/73786976294838206464)), (379155/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822401300532465/9223372036854775808), (1214328897251/9223372036854775808)), (426601/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593650483922793/1152921504606846976), (1213202142935/1152921504606846976)), (213333/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194288068711603/144115188075855872), (1060285676597/144115188075855872)), (186703/72057594037927936), by norm_num⟩
  | 4 => ⟨((186399984815183/4503599627370496), (396974903527/9007199254740992)), (280127/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488713427438051/9007199254740992), (990228398057/4503599627370496)), (350287/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226867500411159/4503599627370496), (986922947435/1125899906842624)), (700961/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214502588252983/2251799813685248), (5888592688031/2251799813685248)), (4111/4398046511104), by norm_num⟩
  | 0 => ⟨((2177609058973075/2251799813685248), (11646060391181/2251799813685248)), (4217545/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177609058973075/2251799813685248), (11646060391181/2251799813685248)), (16088657387740325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((526450614546255/562949953421312), (5631176993411/562949953421312)), (8200803/2251799813685248), by norm_num⟩
  | 2 => ⟨((984522825581985/1125899906842624), (42128598761337/2251799813685248)), (3875565/562949953421312), by norm_num⟩
  | 3 => ⟨((430252051490293/562949953421312), (73677183625735/2251799813685248)), (27691403/2251799813685248), by norm_num⟩
  | 4 => ⟨((328230877766197/562949953421312), (112620168845721/2251799813685248)), (44140121/2251799813685248), by norm_num⟩
  | 5 => ⟨((759874316125609/2251799813685248), (262655084344547/4503599627370496)), (111774895/4503599627370496), by norm_num⟩
  | 6 => ⟨((995047693973475/9007199254740992), (354533917944669/9007199254740992)), (88475003/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-4095317/65536)), (1/8388608), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-579933/262144), (-135271473/2097152)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-24560074108187/2251799813685248), (-980949299817177/9007199254740992)), (653651981/18014398509481984), by norm_num⟩
  | 1 => ⟨((15019261/536870912), (1199762953/4294967296)), (201/2147483648), by norm_num⟩
  | 2 => ⟨((-154094575/4294967296), (-192333201/536870912)), (259/2147483648), by norm_num⟩
  | 3 => ⟨((32937065/1073741824), (1315533121/4294967296)), (445/4294967296), by norm_num⟩
  | 4 => ⟨((-168963807/8589934592), (-1687137917/8589934592)), (573/8589934592), by norm_num⟩
  | 5 => ⟨((173353443/17179869184), (1730969327/17179869184)), (295/8589934592), by norm_num⟩
  | 6 => ⟨((-148214267/34359738368), (-1479949555/34359738368)), (507/34359738368), by norm_num⟩
  | 7 => ⟨((27154435/17179869184), (1084570189/68719476736)), (373/68719476736), by norm_num⟩
  | 8 => ⟨((-139299501/274877906944), (-1390933805/274877906944)), (15/8589934592), by norm_num⟩
  | 9 => ⟨((19849787/137438953472), (1585633231/1099511627776)), (549/1099511627776), by norm_num⟩
  | 10 => ⟨((-162923835/4398046511104), (-1626827575/4398046511104)), (565/4398046511104), by norm_num⟩
  | 11 => ⟨((18995063/2199023255552), (1517356489/17592186044416)), (529/17592186044416), by norm_num⟩
  | 12 => ⟨((-64961833/35184372088832), (-162164273/8796093022208)), (227/35184372088832), by norm_num⟩
  | 13 => ⟨((51268865/140737488355328), (127982507/35184372088832)), (45/35184372088832), by norm_num⟩
  | 14 => ⟨((-9393003/140737488355328), (-750328341/1125899906842624)), (265/1125899906842624), by norm_num⟩
  | 15 => ⟨((102794995/9007199254740992), (1026428905/9007199254740992)), (91/2251799813685248), by norm_num⟩
  | 16 => ⟨((-65915989/36028797018963968), (-164546135/9007199254740992)), (469/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-2176158263331/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778553362430753/633825300114114700748351602688), (-2574785111351/633825300114114700748351602688)), (184907/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889499413384593/39614081257132168796771975168), (-2896070252513/39614081257132168796771975168)), (52013/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944629599644943/1237940039285380274899124224), (-1538189912209/1237940039285380274899124224)), (221093/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770925296953277/154742504910672534362390528), (-1537799190665/77371252455336267181195264)), (13821/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774652230319853/4835703278458516698824704), (-720635856825/2417851639229258349412352)), (207361/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258570678427173/604462909807314587353088), (-2521395700215/604462909807314587353088)), (181485/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887437484882149/75557863725914323419136), (-4095712685317/75557863725914323419136)), (147499/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324318317311741/1180591620717411303424), (-1535212073615/2361183241434822606848)), (221323/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621081682671439/590295810358705651712), (-4219623627707/590295810358705651712)), (304439/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911507967705911/36893488147419103232), (-2635608479543/36893488147419103232)), (190365/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911069989525211/4611686018427387904), (-1481391797391/2305843009213693952)), (214285/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593387362040309/1152921504606846976), (-5919881678697/1152921504606846976)), (26805/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194055816613173/144115188075855872), (-5173506248259/144115188075855872)), (375621/144115188075855872), by norm_num⟩
  | 4 => ⟨((186355933993469/4503599627370496), (-1936873467235/9007199254740992)), (564133/36028797018963968), by norm_num⟩
  | 3 => ⟨((744132948743915/4503599627370496), (-9662061287409/9007199254740992)), (706395/9007199254740992), by norm_num⟩
  | 2 => ⟨((278243935883099/562949953421312), (-19257338619213/4503599627370496)), (354121/1125899906842624), by norm_num⟩
  | 1 => ⟨((2213076574422223/2251799813685248), (-28719517084301/2251799813685248)), (66687/70368744177664), by norm_num⟩
  | 0 => ⟨((2174551384250971/2251799813685248), (-14193970018063/562949953421312)), (4305141/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174551384250971/2251799813685248), (-14193970018063/562949953421312)), (16422809609420012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2098521455358087/2251799813685248), (-109656344984883/2251799813685248)), (8532001/2251799813685248), by norm_num⟩
  | 2 => ⟨((243792085663651/281474976710656), (-204384236350319/2251799813685248)), (8366719/1125899906842624), by norm_num⟩
  | 3 => ⟨((417670372731483/562949953421312), (-354043971076243/2251799813685248)), (62547/4398046511104), by norm_num⟩
  | 4 => ⟨((1183866120987113/2251799813685248), (-262676418150585/1125899906842624)), (57589435/2251799813685248), by norm_num⟩
  | 5 => ⟨((499841674633301/2251799813685248), (-69050035074341/281474976710656)), (174852055/4503599627370496), by norm_num⟩
  | 6 => ⟨((-24560074108187/2251799813685248), (-980949299817177/9007199254740992)), (653651981/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-135271473/2097152)), (1/8388608), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2386755/1048576), (-139179813/2097152)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-427215085904615/4503599627370496), (353878229611131/9007199254740992)), (82203173/2251799813685248), by norm_num⟩
  | 1 => ⟨((537607719/2147483648), (-445320575/4294967296)), (13/134217728), by norm_num⟩
  | 2 => ⟨((-1418777591/4294967296), (36725829/268435456)), (551/4294967296), by norm_num⟩
  | 3 => ⟨((1248078467/4294967296), (-258457515/2147483648)), (487/4294967296), by norm_num⟩
  | 4 => ⟨((-102929707/536870912), (85260525/1073741824)), (323/4294967296), by norm_num⟩
  | 5 => ⟨((108654959/1073741824), (-360011861/8589934592)), (343/8589934592), by norm_num⟩
  | 6 => ⟨((-47791111/1073741824), (316697313/17179869184)), (19/1073741824), by norm_num⟩
  | 7 => ⟨((72070561/4294967296), (-477589923/68719476736)), (115/17179869184), by norm_num⟩
  | 8 => ⟨((-760793369/137438953472), (315096797/137438953472)), (305/137438953472), by norm_num⟩
  | 9 => ⟨((446172737/274877906944), (-369581561/549755813888)), (45/68719476736), by norm_num⟩
  | 10 => ⟨((-941980345/2199023255552), (390138771/2199023255552)), (191/1099511627776), by norm_num⟩
  | 11 => ⟨((451989115/4398046511104), (-374399485/8796093022208)), (369/8796093022208), by norm_num⟩
  | 12 => ⟨((-795216791/35184372088832), (164676951/17592186044416)), (163/17592186044416), by norm_num⟩
  | 13 => ⟨((1291460123/281474976710656), (-133720589/70368744177664)), (133/70368744177664), by norm_num⟩
  | 14 => ⟨((-486891043/562949953421312), (201655029/562949953421312)), (403/1125899906842624), by norm_num⟩
  | 15 => ⟨((85662225/562949953421312), (-283828897/4503599627370496)), (285/4503599627370496), by norm_num⟩
  | 16 => ⟨((-904270091/36028797018963968), (374520365/36028797018963968)), (189/18014398509481984), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (3580790678967/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55576524788291/19807040628566084398385987584), (2118134945139/316912650057057350374175801344)), (92617/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472345364208411/9903520314283042199192993792), (2382417979755/19807040628566084398385987584)), (104221/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944566726232947/1237940039285380274899124224), (316341262307/154742504910672534362390528)), (55383/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770799080318357/154742504910672534362390528), (2530067540191/77371252455336267181195264)), (110801/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774592816868785/4835703278458516698824704), (4742468956789/9671406556917033397649408)), (207825/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258466206493853/604462909807314587353088), (4148252942745/604462909807314587353088)), (90961/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943633392189471/37778931862957161709568), (1684568194175/18889465931478580854784)), (147881/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324286106959015/1180591620717411303424), (315712294923/295147905179352825856)), (27743/590295810358705651712), by norm_num⟩
  | 9 => ⟨((50653225041239/18446744073709551616), (3470960676637/295147905179352825856)), (152685/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911395424988489/36893488147419103232), (8671779991455/73786976294838206464)), (382011/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455471008737713/2305843009213693952), (9748025908775/9223372036854775808)), (430171/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796564010599293/576460752303423488), (1217296571207/144115188075855872)), (430683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149228135205195/18014398509481984), (8510222718911/144115188075855872)), (23589/9007199254740992), by norm_num⟩
  | 4 => ⟨((745246884993587/18014398509481984), (12743644354991/36028797018963968)), (567291/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487810524743131/9007199254740992), (15891636358193/9007199254740992)), (22223/281474976710656), by norm_num⟩
  | 2 => ⟨((1112500610296563/2251799813685248), (15834833714999/2251799813685248)), (11159/35184372088832), by norm_num⟩
  | 1 => ⟨((552888280599697/562949953421312), (23610510468521/1125899906842624)), (1078883/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085558377855073/1125899906842624), (46655663956567/1125899906842624)), (273545/140737488355328), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085558377855073/1125899906842624), (46655663956567/1125899906842624)), (1043491364062261537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1044728961787297/1125899906842624), (89967938667787/1125899906842624)), (2200633/562949953421312), by norm_num⟩
  | 2 => ⟨((962220857311487/1125899906842624), (83481764753071/562949953421312)), (4435655/562949953421312), by norm_num⟩
  | 3 => ⟨((797577255848929/1125899906842624), (570764024491949/2251799813685248)), (35588759/2251799813685248), by norm_num⟩
  | 4 => ⟨((246330327750653/562949953421312), (808648089630245/2251799813685248)), (17115721/562949953421312), by norm_num⟩
  | 5 => ⟨((70376227746141/1125899906842624), (1415362397619601/4503599627370496)), (218172719/4503599627370496), by norm_num⟩
  | 6 => ⟨((-427215085904615/4503599627370496), (353878229611131/9007199254740992)), (82203173/2251799813685248), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-139179813/2097152)), (1/8388608), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39186431/16777216), (-571273563/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((460558239251527/9007199254740992), (739730592616947/9007199254740992)), (225554935/9007199254740992), by norm_num⟩
  | 1 => ⟨((-74339797/536870912), (-477606673/2147483648)), (293/4294967296), by norm_num⟩
  | 2 => ⟨((805263609/4294967296), (1293382847/4294967296)), (399/4294967296), by norm_num⟩
  | 3 => ⟨((-726898093/4294967296), (-583757613/2147483648)), (181/2147483648), by norm_num⟩
  | 4 => ⟨((123029783/1073741824), (790422461/4294967296)), (247/4294967296), by norm_num⟩
  | 5 => ⟨((-266536663/4294967296), (-428100741/4294967296)), (135/4294967296), by norm_num⟩
  | 6 => ⟨((240598221/8589934592), (772878865/17179869184)), (123/8589934592), by norm_num⟩
  | 7 => ⟨((-372315463/34359738368), (-1195997009/68719476736)), (383/68719476736), by norm_num⟩
  | 8 => ⟨((252062241/68719476736), (809704985/137438953472)), (261/137438953472), by norm_num⟩
  | 9 => ⟨((-606753069/549755813888), (-974542999/549755813888)), (79/137438953472), by norm_num⟩
  | 10 => ⟨((164311777/549755813888), (527822273/1099511627776)), (43/274877906944), by norm_num⟩
  | 11 => ⟨((-323610575/4398046511104), (-1039541245/8796093022208)), (341/8796093022208), by norm_num⟩
  | 12 => ⟨((146058947/8796093022208), (469188313/17592186044416)), (155/17592186044416), by norm_num⟩
  | 13 => ⟨((-486812259/140737488355328), (-195474693/35184372088832)), (65/35184372088832), by norm_num⟩
  | 14 => ⟨((753321163/1125899906842624), (1209954929/1125899906842624)), (405/1125899906842624), by norm_num⟩
  | 15 => ⟨((-544008407/4503599627370496), (-109220623/562949953421312)), (147/2251799813685248), by norm_num⟩
  | 16 => ⟨((368300519/18014398509481984), (147887465/4503599627370496)), (25/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1320747645037/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778365399739201/633825300114114700748351602688), (1562362708511/633825300114114700748351602688)), (46177/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889288123704209/39614081257132168796771975168), (219662599587/4951760157141521099596496896)), (25977/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944517460721573/1237940039285380274899124224), (1866687283689/2475880078570760549798248448)), (55207/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885350631771285/77371252455336267181195264), (466546767009/38685626227668133590597632)), (220853/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193636836109923/1208925819614629174706176), (1749019075103/9671406556917033397649408)), (207077/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629193693764553/302231454903657293676544), (764930294881/302231454903657293676544)), (45305/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887140123172143/75557863725914323419136), (2485028069387/75557863725914323419136)), (147267/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297050672853065/4722366482869645213696), (931450255899/2361183241434822606848)), (110473/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620776302397733/590295810358705651712), (640018593123/147573952589676412928)), (303873/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911317621769679/36893488147419103232), (49968337689/1152921504606846976)), (23747/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821713119795407/9223372036854775808), (3594808465099/9223372036854775808)), (427597/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398240568446589/288230376151711744), (1795586022793/576460752303423488)), (213893/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193685852817941/144115188075855872), (3138189226265/144115188075855872)), (187263/72057594037927936), by norm_num⟩
  | 4 => ⟨((372574123312729/9007199254740992), (4699122844597/36028797018963968)), (70277/4503599627370496), by norm_num⟩
  | 3 => ⟨((743792047110465/4503599627370496), (1464911987773/2251799813685248)), (703519/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112304276247535/2251799813685248), (2919158362421/1125899906842624)), (1409289/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105556772094603/1125899906842624), (4352164620955/562949953421312)), (2119583/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170828967968773/2251799813685248), (34394330264499/2251799813685248)), (4261881/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170828967968773/2251799813685248), (34394330264499/2251799813685248)), (16257785805709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523061087578161/562949953421312), (66315138688875/2251799813685248)), (130429/35184372088832), by norm_num⟩
  | 2 => ⟨((1942041515954719/2251799813685248), (123232512427405/2251799813685248)), (8001813/1125899906842624), by norm_num⟩
  | 3 => ⟨((834074808680481/1125899906842624), (212561217737873/2251799813685248)), (14677981/1125899906842624), by norm_num⟩
  | 4 => ⟨((1215712363940165/2251799813685248), (314933780418881/2251799813685248)), (49036399/2251799813685248), by norm_num⟩
  | 5 => ⟨((1224596660332417/4503599627370496), (21253492892151/140737488355328)), (133328685/4503599627370496), by norm_num⟩
  | 6 => ⟨((460558239251527/9007199254740992), (739730592616947/9007199254740992)), (225554935/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-571273563/8388608)), (1/8388608), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile033Terms1
