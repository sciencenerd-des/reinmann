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
namespace Reinmann.XiBand97.Tile042Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35411/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35411/1280))
  have he : value ((69/80), (35411/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-2039635497/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-309682795149413/4503599627370496), (300953688513675/2251799813685248)), (60061501/2251799813685248), by norm_num⟩
  | 1 => ⟨((324460339/2147483648), (-157657347/536870912)), (127/2147483648), by norm_num⟩
  | 2 => ⟨((-712912231/4294967296), (1385634391/4294967296)), (141/2147483648), by norm_num⟩
  | 3 => ⟨((522142759/4294967296), (-253712495/1073741824)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((-143408113/2147483648), (1114926659/8589934592)), (29/1073741824), by norm_num⟩
  | 5 => ⟨((504159729/17179869184), (-979897703/17179869184)), (103/8589934592), by norm_num⟩
  | 6 => ⟨((-92312679/8589934592), (358842553/17179869184)), (153/34359738368), by norm_num⟩
  | 7 => ⟨((463615285/137438953472), (-112636811/17179869184)), (97/68719476736), by norm_num⟩
  | 8 => ⟨((-509333449/549755813888), (494976739/274877906944)), (215/549755813888), by norm_num⟩
  | 9 => ⟨((248693327/1099511627776), (-966733383/2199023255552)), (213/2199023255552), by norm_num⟩
  | 10 => ⟨((-54643509/1099511627776), (212413035/2199023255552)), (189/8796093022208), by norm_num⟩
  | 11 => ⟨((698554537/70368744177664), (-1357728411/70368744177664)), (305/70368744177664), by norm_num⟩
  | 12 => ⟨((-255813533/140737488355328), (248602853/70368744177664)), (113/140737488355328), by norm_num⟩
  | 13 => ⟨((691790501/2251799813685248), (-672290829/1125899906842624)), (77/562949953421312), by norm_num⟩
  | 14 => ⟨((-434291169/9007199254740992), (422049695/4503599627370496)), (195/9007199254740992), by norm_num⟩
  | 15 => ⟨((31807841/4503599627370496), (-494580247/36028797018963968)), (231/72057594037927936), by norm_num⟩
  | 16 => ⟨((-34944485/36028797018963968), (543351937/288230376151711744)), (1/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (1332557674315/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889520267031723/316912650057057350374175801344), (1577479936871/316912650057057350374175801344)), (92511/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945023639266289/19807040628566084398385987584), (3548730065339/39614081257132168796771975168)), (52047/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889841052737063/2475880078570760549798248448), (117806114383/77371252455336267181195264)), (3457/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771506865569857/154742504910672534362390528), (3768974491985/154742504910672534362390528)), (55325/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549849378692183/9671406556917033397649408), (3532541250695/9671406556917033397649408)), (51881/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259047179317735/604462909807314587353088), (96565669809/18889465931478580854784)), (90819/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472052808018671/18889465931478580854784), (5019779901253/75557863725914323419136)), (9227/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297853083986431/4722366482869645213696), (3763404735333/4722366482869645213696)), (55385/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621878122977649/590295810358705651712), (5172358149133/590295810358705651712)), (76191/295147905179352825856), by norm_num⟩
  | 8 => ⟨((7125040153091/288230376151711744), (1615490966199/18446744073709551616)), (47647/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911628479041723/4611686018427387904), (7264921078111/9223372036854775808)), (214563/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398625567741259/288230376151711744), (3629469359433/576460752303423488)), (107377/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195029035854831/144115188075855872), (3172422660255/72057594037927936)), (188123/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492302655682973/36028797018963968), (4751913052821/18014398509481984)), (141307/18014398509481984), by norm_num⟩
  | 3 => ⟨((372519190985653/2251799813685248), (5928141201145/4503599627370496)), (354019/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114774471660591/2251799813685248), (11821078179603/2251799813685248)), (355147/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109206143718469/1125899906842624), (17643768222053/1125899906842624)), (133887/281474976710656), by norm_num⟩
  | 0 => ⟨((1092491122383621/1125899906842624), (34937109961639/1125899906842624)), (1082441/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092491122383621/1125899906842624), (34937109961639/1125899906842624)), (4129184727195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058989563449011/1125899906842624), (67800844893695/1125899906842624)), (1083911/562949953421312), by norm_num⟩
  | 2 => ⟨((991972673714539/1125899906842624), (127543108759639/1125899906842624)), (8678147/2251799813685248), by norm_num⟩
  | 3 => ⟨((1719056081136291/2251799813685248), (449486771750299/2251799813685248)), (2157235/281474976710656), by norm_num⟩
  | 4 => ⟨((611314432877465/1125899906842624), (686289219558197/2251799813685248)), (4154949/281474976710656), by norm_num⟩
  | 5 => ⟨((454671167602511/2251799813685248), (372625046413455/1125899906842624)), (56356395/2251799813685248), by norm_num⟩
  | 6 => ⟨((-309682795149413/4503599627370496), (300953688513675/2251799813685248)), (60061501/2251799813685248), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-2039635497/33554432)), (1/16777216), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-33319209/16777216), (-1068719679/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((798266206758041/9007199254740992), (-471955728357357/4503599627370496)), (36830963/1125899906842624), by norm_num⟩
  | 1 => ⟨((-438231437/2147483648), (259093815/1073741824)), (163/2147483648), by norm_num⟩
  | 2 => ⟨((504532587/2147483648), (-149146389/536870912)), (189/2147483648), by norm_num⟩
  | 3 => ⟨((-774486143/4294967296), (28618521/134217728)), (73/1073741824), by norm_num⟩
  | 4 => ⟨((222915031/2147483648), (-527172639/4294967296)), (339/8589934592), by norm_num⟩
  | 5 => ⟨((-205312331/4294967296), (60692993/1073741824)), (157/8589934592), by norm_num⟩
  | 6 => ⟨((315166075/17179869184), (-372668749/17179869184)), (243/34359738368), by norm_num⟩
  | 7 => ⟨((-51835479/8589934592), (245171859/34359738368)), (161/68719476736), by norm_num⟩
  | 8 => ⟨((477422405/274877906944), (-141132267/68719476736)), (373/549755813888), by norm_num⟩
  | 9 => ⟨((-488580317/1099511627776), (577722763/1099511627776)), (3/17179869184), by norm_num⟩
  | 10 => ⟨((224999551/2199023255552), (-532102329/4398046511104)), (89/2199023255552), by norm_num⟩
  | 11 => ⟨((-753571799/35184372088832), (445531233/17592186044416)), (75/8796093022208), by norm_num⟩
  | 12 => ⟨((289193865/70368744177664), (-683915717/140737488355328)), (29/17592186044416), by norm_num⟩
  | 13 => ⟨((-819561209/1125899906842624), (969091775/1125899906842624)), (331/1125899906842624), by norm_num⟩
  | 14 => ⟨((539174121/4503599627370496), (-637547507/4503599627370496)), (55/1125899906842624), by norm_num⟩
  | 15 => ⟨((-331065145/18014398509481984), (97867159/4503599627370496)), (17/2251799813685248), by norm_num⟩
  | 16 => ⟨((190576417/72057594037927936), (-450694923/144115188075855872)), (315/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806918929/10141204801825835211973625643008), (-70732118697/633825300114114700748351602688)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778904779815999/633825300114114700748351602688), (-1339520488181/633825300114114700748351602688)), (184663/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236236853823717/4951760157141521099596496896), (-1506698144585/39614081257132168796771975168)), (207763/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889679430957839/2475880078570760549798248448), (-400135610843/618970019642690137449562112)), (6899/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771345641957289/154742504910672534362390528), (-800088842353/77371252455336267181195264)), (110395/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549698654374907/9671406556917033397649408), (-374944783395/2417851639229258349412352)), (207015/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258915718098011/604462909807314587353088), (-1311919420093/604462909807314587353088)), (90581/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((14749987494789/590295810358705651712), (-1065571546397/37778931862957161709568)), (294431/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324423537911891/1180591620717411303424), (-1597722363739/4722366482869645213696)), (110431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202707589353021/73786976294838206464), (-548959235129/147573952589676412928)), (75937/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911870101448937/36893488147419103232), (-1371625037321/36893488147419103232)), (379779/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911477717328971/4611686018427387904), (-192751990459/576460752303423488)), (106845/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594203633615485/1152921504606846976), (-1540689170497/576460752303423488)), (213771/576460752303423488), by norm_num⟩
  | 5 => ⟨((149346371115583/18014398509481984), (-1346611870769/72057594037927936)), (187141/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491922021595823/36028797018963968), (-4033878211141/36028797018963968)), (140447/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489612253239135/9007199254740992), (-1257984630169/2251799813685248)), (702875/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228653631351363/4503599627370496), (-5016357025119/2251799813685248)), (1407673/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217153117246939/2251799813685248), (-7485694874485/1125899906842624)), (132271/140737488355328), by norm_num⟩
  | 0 => ⟨((2182796249661419/2251799813685248), (-14816703818027/1125899906842624)), (2126029/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182796249661419/2251799813685248), (-14816703818027/1125899906842624)), (8110157017234420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2115517240802869/2251799813685248), (-57450658499529/2251799813685248)), (1044429/281474976710656), by norm_num⟩
  | 2 => ⟨((1986016958875749/2251799813685248), (-53973651570885/1125899906842624)), (4031461/562949953421312), by norm_num⟩
  | 3 => ⟨((218303749559917/281474976710656), (-47603071419035/562949953421312)), (29991069/2251799813685248), by norm_num⟩
  | 4 => ⟨((1338378694122967/2251799813685248), (-295356385929149/2251799813685248)), (12898121/562949953421312), by norm_num⟩
  | 5 => ⟨((1513475686263961/4503599627370496), (-702191538871825/4503599627370496)), (74863185/2251799813685248), by norm_num⟩
  | 6 => ⟨((798266206758041/9007199254740992), (-471955728357357/4503599627370496)), (36830963/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33319209/16777216), (-1068719679/16777216)), (1/8388608), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-139119607/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1064061157690341/9007199254740992), (405324184025359/9007199254740992)), (200847825/9007199254740992), by norm_num⟩
  | 1 => ⟨((304163363/1073741824), (-463449929/4294967296)), (29/536870912), by norm_num⟩
  | 2 => ⟨((-1458703781/4294967296), (555652197/4294967296)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((582969817/2147483648), (-222065963/2147483648)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-174737571/1073741824), (532490923/8589934592)), (275/8589934592), by norm_num⟩
  | 5 => ⟨((670403833/8589934592), (-510742987/17179869184)), (133/8589934592), by norm_num⟩
  | 6 => ⟨((-1071705455/34359738368), (408236065/34359738368)), (215/34359738368), by norm_num⟩
  | 7 => ⟨((367119635/34359738368), (-559375617/137438953472)), (297/137438953472), by norm_num⟩
  | 8 => ⟨((-880314437/274877906944), (335331037/274877906944)), (45/68719476736), by norm_num⟩
  | 9 => ⟨((469089295/549755813888), (-357372759/1099511627776)), (97/549755813888), by norm_num⟩
  | 10 => ⟨((-449930801/2199023255552), (85694245/1099511627776)), (47/1099511627776), by norm_num⟩
  | 11 => ⟨((98080631/2199023255552), (-298888473/17592186044416)), (83/8796093022208), by norm_num⟩
  | 12 => ⟨((-1254331101/140737488355328), (477802171/140737488355328)), (267/140737488355328), by norm_num⟩
  | 13 => ⟨((925462959/562949953421312), (-176264549/281474976710656)), (199/562949953421312), by norm_num⟩
  | 14 => ⟨((-158511661/562949953421312), (241522245/2251799813685248)), (275/4503599627370496), by norm_num⟩
  | 15 => ⟨((405433987/9007199254740992), (-19304835/1125899906842624)), (89/9007199254740992), by norm_num⟩
  | 16 => ⟨((-972188241/144115188075855872), (370327781/144115188075855872)), (215/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (1809093325379/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222346148810341/79228162514264337593543950336), (4281981260709/633825300114114700748351602688)), (46311/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889741818315625/39614081257132168796771975168), (602041639095/4951760157141521099596496896)), (52113/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944758118080983/1237940039285380274899124224), (5116271499405/2475880078570760549798248448)), (27693/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771181751045787/154742504910672534362390528), (1278763452473/38685626227668133590597632)), (110807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549544267507333/9671406556917033397649408), (2397034659097/4835703278458516698824704)), (103919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629389945498027/302231454903657293676544), (4193517211757/604462909807314587353088)), (90967/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887776296588833/75557863725914323419136), (6812040663513/75557863725914323419136)), (36973/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297526365006415/4722366482869645213696), (2553454595317/2361183241434822606848)), (110981/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621428044789307/590295810358705651712), (7018553760073/590295810358705651712)), (76349/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823446424042989/73786976294838206464), (4384011971511/36893488147419103232)), (95511/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822620895303289/9223372036854775808), (9856922711659/9223372036854775808)), (215107/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199233006976821/144115188075855872), (4924022815143/576460752303423488)), (107683/576460752303423488), by norm_num⟩
  | 5 => ⟨((149308522847323/18014398509481984), (8607057616727/144115188075855872)), (2949/2251799813685248), by norm_num⟩
  | 4 => ⟨((1491456562902357/36028797018963968), (12890632847141/36028797018963968)), (141843/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489010761936079/9007199254740992), (2009799651093/1125899906842624)), (355629/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113695964493345/2251799813685248), (8013053212201/1125899906842624)), (89291/562949953421312), by norm_num⟩
  | 1 => ⟨((1107557378057405/1125899906842624), (11954304199371/562949953421312)), (539591/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089071114506965/1125899906842624), (23648036093991/562949953421312)), (136827/140737488355328), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089071114506965/1125899906842624), (23648036093991/562949953421312)), (521953583300542787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((131432528639345/140737488355328), (91497984388353/1125899906842624)), (1104793/562949953421312), by norm_num⟩
  | 2 => ⟨((974506459761433/1125899906842624), (85448529699509/562949953421312)), (4486127/1125899906842624), by norm_num⟩
  | 3 => ⟨((408765037465355/562949953421312), (2311210783015/8796093022208)), (4563839/562949953421312), by norm_num⟩
  | 4 => ⟨((1031773933652399/2251799813685248), (859237991161953/2251799813685248)), (36104233/2251799813685248), by norm_num⟩
  | 5 => ⟨((144891887247541/2251799813685248), (1574810259236787/4503599627370496)), (121278163/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1064061157690341/9007199254740992), (405324184025359/9007199254740992)), (200847825/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-139119607/2097152)), (1/16777216), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-576671117/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((984651945809895/9007199254740992), (382458831598793/9007199254740992)), (5654635/281474976710656), by norm_num⟩
  | 1 => ⟨((-291677495/1073741824), (-453173873/4294967296)), (217/4294967296), by norm_num⟩
  | 2 => ⟨((724791347/2147483648), (563047385/4294967296)), (17/268435456), by norm_num⟩
  | 3 => ⟨((-600346279/2147483648), (-466373397/4294967296)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((1491804461/8589934592), (289723589/4294967296)), (285/8589934592), by norm_num⟩
  | 5 => ⟨((-741398965/8589934592), (-287974429/8589934592)), (143/8589934592), by norm_num⟩
  | 6 => ⟨((307051203/8589934592), (119264929/8589934592)), (239/34359738368), by norm_num⟩
  | 7 => ⟨((-435996329/34359738368), (-169349837/34359738368)), (43/17179869184), by norm_num⟩
  | 8 => ⟨((1083410177/274877906944), (52602317/34359738368)), (215/274877906944), by norm_num⟩
  | 9 => ⟨((-1196521401/1099511627776), (-464753235/1099511627776)), (15/68719476736), by norm_num⟩
  | 10 => ⟨((594648797/2199023255552), (230973681/2199023255552)), (241/4398046511104), by norm_num⟩
  | 11 => ⟨((-537326091/8796093022208), (-417416753/17592186044416)), (55/4398046511104), by norm_num⟩
  | 12 => ⟨((55633549/4398046511104), (172873611/35184372088832)), (23/8796093022208), by norm_num⟩
  | 13 => ⟨((-85073339/35184372088832), (-132176857/140737488355328)), (71/140737488355328), by norm_num⟩
  | 14 => ⟨((483198413/1125899906842624), (93842043/562949953421312)), (51/562949953421312), by norm_num⟩
  | 15 => ⟨((-1280749813/18014398509481984), (-248734631/9007199254740992)), (273/18014398509481984), by norm_num⟩
  | 16 => ⟨((198908983/18014398509481984), (309041169/72057594037927936)), (43/18014398509481984), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (482597057355/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222332893170341/79228162514264337593543950336), (285531927169/316912650057057350374175801344)), (2883/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889623085564363/39614081257132168796771975168), (642326855769/39614081257132168796771975168)), (6487/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((944695410313901/1237940039285380274899124224), (682323118869/2475880078570760549798248448)), (110283/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771057165155239/154742504910672534362390528), (341077686503/77371252455336267181195264)), (6893/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549428349182221/9671406556917033397649408), (639342490029/9671406556917033397649408)), (12925/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((157334917848917/75557863725914323419136), (559246571671/604462909807314587353088)), (5655/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((943807277531401/37778931862957161709568), (908441866335/75557863725914323419136)), (294079/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648703250347097/2361183241434822606848), (681039451825/4722366482869645213696)), (220575/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810632785940375/295147905179352825856), (935955089721/590295810358705651712)), (303319/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911623419695937/36893488147419103232), (292308270009/18446744073709551616)), (379189/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227800147126301/1152921504606846976), (1314410624727/9223372036854775808)), (213321/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593650345115285/1152921504606846976), (1313190988549/1152921504606846976)), (426713/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194287930097369/144115188075855872), (1147671537635/144115188075855872)), (93363/36028797018963968), by norm_num⟩
  | 4 => ⟨((745599818190391/18014398509481984), (107423120665/2251799813685248)), (35021/2251799813685248), by norm_num⟩
  | 3 => ⟨((1488713065093887/9007199254740992), (535920123931/2251799813685248)), (700697/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226866597577569/4503599627370496), (2136524568649/2251799813685248)), (701115/2251799813685248), by norm_num⟩
  | 1 => ⟨((553625197909405/562949953421312), (6373912437957/2251799813685248)), (2105449/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177603714186125/2251799813685248), (12605887792181/2251799813685248)), (2109699/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177603714186125/2251799813685248), (12605887792181/2251799813685248)), (8047863010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2105781783448081/2251799813685248), (190476995821/17592186044416)), (8207983/2251799813685248), by norm_num⟩
  | 2 => ⟨((492242078613113/562949953421312), (45600130302521/2251799813685248)), (15529215/2251799813685248), by norm_num⟩
  | 3 => ⟨((26886526695539/35184372088832), (79745287440651/2251799813685248)), (27786367/2251799813685248), by norm_num⟩
  | 4 => ⟨((1312096631627003/2251799813685248), (121876485060085/2251799813685248)), (22217287/1125899906842624), by norm_num⟩
  | 5 => ⟨((757946458092607/2251799813685248), (284063840044759/4503599627370496)), (14148235/562949953421312), by norm_num⟩
  | 6 => ⟨((984651945809895/9007199254740992), (382458831598793/9007199254740992)), (5654635/281474976710656), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-576671117/8388608)), (1/8388608), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-595246591/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-265892134266265/9007199254740992), (-949322946941827/9007199254740992)), (340171875/9007199254740992), by norm_num⟩
  | 1 => ⟨((325202875/4294967296), (580540963/2147483648)), (209/2147483648), by norm_num⟩
  | 2 => ⟨((-417064453/4294967296), (-744529085/2147483648)), (539/4294967296), by norm_num⟩
  | 3 => ⟨((356583067/4294967296), (1273119599/4294967296)), (463/4294967296), by norm_num⟩
  | 4 => ⟨((-228654377/4294967296), (-1632743649/8589934592)), (149/2147483648), by norm_num⟩
  | 5 => ⟨((234594759/8589934592), (837580955/8589934592)), (307/8589934592), by norm_num⟩
  | 6 => ⟨((-200574559/17179869184), (-1432235155/34359738368)), (527/34359738368), by norm_num⟩
  | 7 => ⟨((36747399/8589934592), (32800095/2147483648)), (97/17179869184), by norm_num⟩
  | 8 => ⟨((-188510435/137438953472), (-673044661/137438953472)), (125/68719476736), by norm_num⟩
  | 9 => ⟨((214897653/549755813888), (767255765/549755813888)), (143/274877906944), by norm_num⟩
  | 10 => ⟨((-220480639/2199023255552), (-1574377745/4398046511104)), (295/2199023255552), by norm_num⟩
  | 11 => ⟨((205644245/8796093022208), (367109017/4398046511104)), (553/17592186044416), by norm_num⟩
  | 12 => ⟨((-87911179/17592186044416), (-627744025/35184372088832)), (475/70368744177664), by norm_num⟩
  | 13 => ⟨((138761675/140737488355328), (247712559/70368744177664)), (377/281474976710656), by norm_num⟩
  | 14 => ⟨((-101690477/562949953421312), (-90767167/140737488355328)), (555/2251799813685248), by norm_num⟩
  | 15 => ⟨((69554913/2251799813685248), (993336263/9007199254740992)), (381/9007199254740992), by norm_num⟩
  | 16 => ⟨((-356809659/72057594037927936), (-1273928605/72057594037927936)), (245/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-2401865877073/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778552587773889/633825300114114700748351602688), (-2841837656735/633825300114114700748351602688)), (184959/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944749249250159/19807040628566084398385987584), (-3196444577953/39614081257132168796771975168)), (208115/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889258170341753/2475880078570760549798248448), (-424431914675/309485009821345068724781056)), (55291/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221365525508301/19342813113834066795298816), (-3394592619447/154742504910672534362390528)), (221211/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549303368169515/9671406556917033397649408), (-1590757101643/4835703278458516698824704)), (207435/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629284827339465/302231454903657293676544), (-2782908819333/604462909807314587353088)), (45389/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943717847103745/37778931862957161709568), (-282531856201/4722366482869645213696)), (295121/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297271815152895/4722366482869645213696), (-3388880354937/4722366482869645213696)), (221423/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202634937872561/73786976294838206464), (-4657270939641/590295810358705651712)), (76147/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227876617586481/9223372036854775808), (-2908965612637/36893488147419103232)), (380935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822136239180601/9223372036854775808), (-6540146678885/9223372036854775808)), (428827/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796691579768345/576460752303423488), (-816733600641/144115188075855872)), (214585/576460752303423488), by norm_num⟩
  | 5 => ⟨((298512905041483/36028797018963968), (-2855039434113/72057594037927936)), (187955/72057594037927936), by norm_num⟩
  | 4 => ⟨((745420070887675/18014398509481984), (-8551021301129/36028797018963968)), (17645/1125899906842624), by norm_num⟩
  | 3 => ⟨((744127464704175/4503599627370496), (-666508882049/562949953421312)), (176789/2251799813685248), by norm_num⟩
  | 2 => ⟨((2225924161806801/4503599627370496), (-5313630382173/1125899906842624)), (1418387/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213022207984341/2251799813685248), (-31697868009199/2251799813685248)), (534449/562949953421312), by norm_num⟩
  | 0 => ⟨((2174389700127301/2251799813685248), (-62663029659431/2251799813685248)), (2158303/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174389700127301/2251799813685248), (-62663029659431/2251799813685248)), (8233272556785201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524474232125715/562949953421312), (-30254431464591/562949953421312)), (4288337/1125899906842624), by norm_num⟩
  | 2 => ⟨((1948008968644023/2251799813685248), (-56373287232217/562949953421312)), (16902843/2251799813685248), by norm_num⟩
  | 3 => ⟨((207827742887617/281474976710656), (-390143629830335/2251799813685248)), (2039389/140737488355328), by norm_num⟩
  | 4 => ⟨((290001320045035/562949953421312), (-576127021571583/2251799813685248)), (29746073/1125899906842624), by norm_num⟩
  | 5 => ⟨((450168748971463/2251799813685248), (-1187157726927335/4503599627370496)), (183473217/4503599627370496), by norm_num⟩
  | 6 => ⟨((-265892134266265/9007199254740992), (-949322946941827/9007199254740992)), (340171875/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-595246591/8388608)), (1/8388608), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-612444793/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-675112078607885/9007199254740992), (632063605350225/9007199254740992)), (337630067/9007199254740992), by norm_num⟩
  | 1 => ⟨((849561443/4294967296), (-397694609/2147483648)), (427/4294967296), by norm_num⟩
  | 2 => ⟨((-280255169/1073741824), (131192359/536870912)), (283/2147483648), by norm_num⟩
  | 3 => ⟨((123268243/536870912), (-923264417/4294967296)), (501/4294967296), by norm_num⟩
  | 4 => ⟨((-40663995/268435456), (152284233/1073741824)), (333/4294967296), by norm_num⟩
  | 5 => ⟨((343406765/4294967296), (-321509457/4294967296)), (353/8589934592), by norm_num⟩
  | 6 => ⟨((-604180093/17179869184), (565654593/17179869184)), (313/17179869184), by norm_num⟩
  | 7 => ⟨((911123373/68719476736), (-853025657/68719476736)), (237/34359738368), by norm_num⟩
  | 8 => ⟨((-37570419/8589934592), (562795903/137438953472)), (157/68719476736), by norm_num⟩
  | 9 => ⟨((176267537/137438953472), (-660111401/549755813888)), (185/274877906944), by norm_num⟩
  | 10 => ⟨((-744288217/2199023255552), (174207183/549755813888)), (393/2199023255552), by norm_num⟩
  | 11 => ⟨((357130777/4398046511104), (-668716717/8796093022208)), (379/8796093022208), by norm_num⟩
  | 12 => ⟨((-314162865/17592186044416), (73532573/4398046511104)), (335/35184372088832), by norm_num⟩
  | 13 => ⟨((63776447/17592186044416), (-477677971/140737488355328)), (547/281474976710656), by norm_num⟩
  | 14 => ⟨((-769415771/1125899906842624), (720354029/1125899906842624)), (207/562949953421312), by norm_num⟩
  | 15 => ⟨((67684411/562949953421312), (-1013896309/9007199254740992)), (585/9007199254740992), by norm_num⟩
  | 16 => ⟨((-178623041/9007199254740992), (668932621/36028797018963968)), (97/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (778022266063/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111153196562109/39614081257132168796771975168), (3681770419085/633825300114114700748351602688)), (185125/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889384233875851/39614081257132168796771975168), (2070578101269/19807040628566084398385987584)), (26039/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472284143924543/618970019642690137449562112), (4398955285873/2475880078570760549798248448)), (110693/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442700599398441/38685626227668133590597632), (2198902211891/77371252455336267181195264)), (110723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549188949709469/9671406556917033397649408), (1030429781939/2417851639229258349412352)), (207671/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258469313832905/604462909807314587353088), (28166265799/4722366482869645213696)), (11361/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887272219453915/75557863725914323419136), (2928146141103/37778931862957161709568)), (295507/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297148841240021/4722366482869645213696), (4390215231443/4722366482869645213696)), (221737/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620909816887077/590295810358705651712), (6033290691015/590295810358705651712)), (305059/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822799939010453/73786976294838206464), (1884183153247/18446744073709551616)), (381583/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910947692595469/4611686018427387904), (4236058307469/4611686018427387904)), (429637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49785649219751/36028797018963968), (528983583359/72057594037927936)), (215041/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193837816505971/144115188075855872), (3698175304541/72057594037927936)), (188411/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490516013358857/36028797018963968), (2768926158607/9007199254740992)), (141559/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487843804616887/9007199254740992), (13811733695637/9007199254740992)), (709553/9007199254740992), by norm_num⟩
  | 2 => ⟨((139067757661067/281474976710656), (13762468353151/2251799813685248)), (356097/1125899906842624), by norm_num⟩
  | 1 => ⟨((552929508759565/562949953421312), (20520820329577/1125899906842624)), (33591/35184372088832), by norm_num⟩
  | 0 => ⟨((1085803524706987/1125899906842624), (40551799521687/1125899906842624)), (2176403/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085803524706987/1125899906842624), (40551799521687/1125899906842624)), (8302318577293014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((16338664391181/17592186044416), (156430555100893/2251799813685248)), (4354567/1125899906842624), by norm_num⟩
  | 2 => ⟨((1931464009709147/2251799813685248), (290568361870059/2251799813685248)), (4346793/562949953421312), by norm_num⟩
  | 3 => ⟨((1619203992167811/2251799813685248), (249232782550807/1125899906842624)), (34314649/2251799813685248), by norm_num⟩
  | 4 => ⟨((1053980746528229/2251799813685248), (716864286128353/2251799813685248)), (64541341/2251799813685248), by norm_num⟩
  | 5 => ⟨((265112824727027/2251799813685248), (671073113037035/2251799813685248)), (203024647/4503599627370496), by norm_num⟩
  | 6 => ⟨((-675112078607885/9007199254740992), (632063605350225/9007199254740992)), (337630067/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-612444793/8388608)), (1/8388608), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1227453/16384)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((193184869008675/2251799813685248), (201363442296209/4503599627370496)), (81362455/4503599627370496), by norm_num⟩
  | 1 => ⟨((-997837683/4294967296), (-65005101/536870912)), (53/1073741824), by norm_num⟩
  | 2 => ⟨((1351097269/4294967296), (704148307/4294967296)), (289/4294967296), by norm_num⟩
  | 3 => ⟨((-1219613077/4294967296), (-158905747/1073741824)), (263/4294967296), by norm_num⟩
  | 4 => ⟨((825693359/4294967296), (107581185/1073741824)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((-894407627/8589934592), (-466136399/8589934592)), (197/8589934592), by norm_num⟩
  | 6 => ⟨((403683459/8589934592), (210386795/8589934592)), (45/4294967296), by norm_num⟩
  | 7 => ⟨((-1249365797/68719476736), (-325564573/34359738368)), (281/68719476736), by norm_num⟩
  | 8 => ⟨((211459081/34359738368), (110205651/34359738368)), (3/2147483648), by norm_num⟩
  | 9 => ⟨((-1018029879/549755813888), (-530564329/549755813888)), (233/549755813888), by norm_num⟩
  | 10 => ⟨((1102750407/2199023255552), (574717935/2199023255552)), (127/1099511627776), by norm_num⟩
  | 11 => ⟨((-1085928531/8796093022208), (-141487729/2199023255552)), (63/2199023255552), by norm_num⟩
  | 12 => ⟨((980249659/35184372088832), (510874497/35184372088832)), (229/35184372088832), by norm_num⟩
  | 13 => ⟨((-816789319/140737488355328), (-425684241/140737488355328)), (193/140737488355328), by norm_num⟩
  | 14 => ⟨((19749165/17592186044416), (82341021/140737488355328)), (301/1125899906842624), by norm_num⟩
  | 15 => ⟨((-912754863/4503599627370496), (-237849193/2251799813685248)), (219/4503599627370496), by norm_num⟩
  | 16 => ⟨((1235892995/36028797018963968), (644107555/36028797018963968)), (299/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (625824190401/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778366413866539/633825300114114700748351602688), (185077819529/158456325028528675187087900672)), (92273/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472322330260225/9903520314283042199192993792), (832681383863/39614081257132168796771975168)), (25953/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472259067010911/618970019642690137449562112), (221128313753/618970019642690137449562112)), (220611/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770702693794255/154742504910672534362390528), (442138151119/77371252455336267181195264)), (220623/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549096118556145/9671406556917033397649408), (828757359639/9671406556917033397649408)), (101/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((314597181810123/151115727451828646838272), (724911115697/604462909807314587353088)), (181005/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887142466446543/75557863725914323419136), (294377268399/18889465931478580854784)), (294157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648526287809971/2361183241434822606848), (882719463663/4722366482869645213696)), (220639/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620779154548129/590295810358705651712), (303267401063/147573952589676412928)), (151707/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455659790499697/18446744073709551616), (757666605829/36893488147419103232)), (379319/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821718013003027/9223372036854775808), (212921346667/1152921504606846976)), (213403/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99560485747523/72057594037927936), (1701648599327/1152921504606846976)), (426897/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193691342646901/144115188075855872), (743503698729/72057594037927936)), (373637/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490306081704477/36028797018963968), (1113323315917/18014398509481984)), (140165/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487598439480043/9007199254740992), (173534905199/562949953421312)), (701183/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224644284996479/4503599627370496), (21612966673/17592186044416)), (175431/562949953421312), by norm_num⟩
  | 1 => ⟨((2211184618561557/2251799813685248), (4124533361965/1125899906842624)), (2107893/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085520123533315/1125899906842624), (16297967467717/2251799813685248)), (2113385/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085520123533315/1125899906842624), (16297967467717/2251799813685248)), (8061923985007857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2093059117420439/2251799813685248), (31426899587391/2251799813685248)), (1026443/281474976710656), by norm_num⟩
  | 2 => ⟨((972535123322327/1125899906842624), (29211459346377/1125899906842624)), (15494549/2251799813685248), by norm_num⟩
  | 3 => ⟨((839303077471979/1125899906842624), (100929647636341/2251799813685248)), (13785961/1125899906842624), by norm_num⟩
  | 4 => ⟨((1246794591855391/2251799813685248), (18809523687345/281474976710656)), (43578673/2251799813685248), by norm_num⟩
  | 5 => ⟨((680279686215439/2251799813685248), (333267456778083/4503599627370496)), (108164513/4503599627370496), by norm_num⟩
  | 6 => ⟨((193184869008675/2251799813685248), (201363442296209/4503599627370496)), (81362455/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1227453/16384)), (1/8388608), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile042Terms1
