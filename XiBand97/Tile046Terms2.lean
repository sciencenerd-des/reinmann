/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile046Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨46,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36843/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36843/1280))
  have he : value ((69/80), (36843/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-20060163/8388608), (-669453427/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-247932345913593/9007199254740992), (1572064476373085/18014398509481984)), (143504069/18014398509481984), by norm_num⟩
  | 1 => ⟨((655569483/8589934592), (-2078384513/8589934592)), (381/17179869184), by norm_num⟩
  | 2 => ⟨((-1817624555/17179869184), (2881252731/8589934592)), (531/17179869184), by norm_num⟩
  | 3 => ⟨((1679841781/17179869184), (-2662842943/8589934592)), (493/17179869184), by norm_num⟩
  | 4 => ⟨((-582188797/8589934592), (3691484157/17179869184)), (43/2147483648), by norm_num⟩
  | 5 => ⟨((645668037/17179869184), (-4093986937/34359738368)), (383/34359738368), by norm_num⟩
  | 6 => ⟨((-1193447945/68719476736), (3783647337/68719476736)), (89/17179869184), by norm_num⟩
  | 7 => ⟨((472705759/68719476736), (-5994570249/274877906944)), (283/137438953472), by norm_num⟩
  | 8 => ⟨((-40956833/17179869184), (4155119467/549755813888)), (197/274877906944), by norm_num⟩
  | 9 => ⟨((1615025113/2199023255552), (-5120194389/2199023255552)), (61/274877906944), by norm_num⟩
  | 10 => ⟨((-895560083/4398046511104), (709809661/1099511627776)), (543/8796093022208), by norm_num⟩
  | 11 => ⟨((451458143/8796093022208), (-715640095/4398046511104)), (275/17592186044416), by norm_num⟩
  | 12 => ⟨((-1668943675/140737488355328), (5291135085/140737488355328)), (511/140737488355328), by norm_num⟩
  | 13 => ⟨((88986431/35184372088832), (-2256944841/281474976710656)), (219/281474976710656), by norm_num⟩
  | 14 => ⟨((-1127875543/2251799813685248), (3575759893/2251799813685248)), (349/2251799813685248), by norm_num⟩
  | 15 => ⟨((1667805339/18014398509481984), (-2643763081/9007199254740992)), (259/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1156034569/72057594037927936), (916258463/18014398509481984)), (361/72057594037927936), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (1222072196943/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444569114742933/158456325028528675187087900672), (1445502898215/316912650057057350374175801344)), (46243/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889187909353861/39614081257132168796771975168), (1625849911933/19807040628566084398385987584)), (813/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1888928235774851/2475880078570760549798248448), (1727043865469/1237940039285380274899124224)), (55295/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885297172106189/77371252455336267181195264), (3453139275637/154742504910672534362390528)), (55307/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548994203936611/9671406556917033397649408), (1618155315467/4835703278458516698824704)), (51863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258299215352997/604462909807314587353088), (707691173117/151115727451828646838272)), (45393/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943498189565601/37778931862957161709568), (2299052498325/37778931862957161709568)), (73787/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296942459065305/4722366482869645213696), (3446927774151/4722366482869645213696)), (27681/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620626849957113/590295810358705651712), (4736844173069/590295810358705651712)), (76155/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822447441790793/73786976294838206464), (5917035242703/73786976294838206464)), (23811/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455375122320787/2305843009213693952), (6651140921835/9223372036854775808)), (26805/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592747955053187/1152921504606846976), (6644241867763/1152921504606846976)), (107307/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596748214886043/72057594037927936), (5805957899261/144115188075855872)), (93993/144115188075855872), by norm_num⟩
  | 4 => ⟨((93125536442861/2251799813685248), (2173362154503/9007199254740992)), (141185/36028797018963968), by norm_num⟩
  | 3 => ⟨((371804406939977/2251799813685248), (10839749621395/9007199254740992)), (176827/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223855997147619/4503599627370496), (21598488624753/4503599627370496)), (177345/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209936052111805/2251799813685248), (2012238157591/140737488355328)), (267319/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084140859122391/1125899906842624), (63587549797151/2251799813685248)), (539863/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084140859122391/1125899906842624), (63587549797151/2251799813685248)), (2059413914207076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2086065646083197/2251799813685248), (30614560160989/562949953421312)), (535085/562949953421312), by norm_num⟩
  | 2 => ⟨((962935033725219/1125899906842624), (226890443222013/2251799813685248)), (2099207/1125899906842624), by norm_num⟩
  | 3 => ⟨((812127308397431/1125899906842624), (194049893128251/1125899906842624)), (8027517/2251799813685248), by norm_num⟩
  | 4 => ⟨((552354077162827/1125899906842624), (559883579146911/2251799813685248)), (14347821/2251799813685248), by norm_num⟩
  | 5 => ⟨((805498320519893/4503599627370496), (549345418360603/2251799813685248)), (42425201/4503599627370496), by norm_num⟩
  | 6 => ⟨((-247932345913593/9007199254740992), (1572064476373085/18014398509481984)), (143504069/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-669453427/8388608)), (1/33554432), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-163990341/67108864), (-2736366007/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((193869963229703/2251799813685248), (204893668067057/18014398509481984)), (54945277/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1047658857/4294967296), (-553615069/17179869184)), (75/8589934592), by norm_num⟩
  | 2 => ⟨((1484120527/4294967296), (784254801/17179869184)), (215/17179869184), by norm_num⟩
  | 3 => ⟨((-5606440109/17179869184), (-370326861/8589934592)), (205/17179869184), by norm_num⟩
  | 4 => ⟨((3971060233/17179869184), (262303751/8589934592)), (147/17179869184), by norm_num⟩
  | 5 => ⟨((-4500344337/34359738368), (-297264995/17179869184)), (21/4294967296), by norm_num⟩
  | 6 => ⟨((2125072605/34359738368), (561476767/68719476736)), (5/2147483648), by norm_num⟩
  | 7 => ⟨((-6880896071/274877906944), (-909019125/274877906944)), (261/274877906944), by norm_num⟩
  | 8 => ⟨((2436880821/274877906944), (643861279/549755813888)), (187/549755813888), by norm_num⟩
  | 9 => ⟨((-6137069565/2199023255552), (-810753941/2199023255552)), (237/2199023255552), by norm_num⟩
  | 10 => ⟨((3477525477/4398046511104), (459407777/4398046511104)), (271/8796093022208), by norm_num⟩
  | 11 => ⟨((-447844163/2199023255552), (-946618359/35184372088832)), (141/17592186044416), by norm_num⟩
  | 12 => ⟨((6767136313/140737488355328), (893990589/140737488355328)), (269/140737488355328), by norm_num⟩
  | 13 => ⟨((-2949652447/281474976710656), (-779343405/562949953421312)), (237/562949953421312), by norm_num⟩
  | 14 => ⟨((596928191/281474976710656), (157717581/562949953421312)), (97/1125899906842624), by norm_num⟩
  | 15 => ⟨((-450993311/1125899906842624), (-29789837/562949953421312)), (295/18014398509481984), by norm_num⟩
  | 16 => ⟨((1277760267/18014398509481984), (337603855/36028797018963968)), (211/72057594037927936), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644697451/10141204801825835211973625643008), (85547119635/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889100177153601/316912650057057350374175801344), (101178909801/316912650057057350374175801344)), (46111/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889102557886759/39614081257132168796771975168), (227604430423/39614081257132168796771975168)), (51875/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888837900564205/2475880078570760549798248448), (30221182103/309485009821345068724781056)), (27559/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442626100796531/38685626227668133590597632), (120850853273/77371252455336267181195264)), (55119/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548910302748691/9671406556917033397649408), (226523392069/9671406556917033397649408)), (51675/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314556555000939/151115727451828646838272), (12383502529/37778931862957161709568)), (45217/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943439272542997/37778931862957161709568), (321836265699/75557863725914323419136)), (36739/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296854768295269/4722366482869645213696), (60314828345/1180591620717411303424)), (55111/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810253693280877/295147905179352825856), (41442513941/73786976294838206464)), (75779/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911149888672613/36893488147419103232), (414138183073/73786976294838206464)), (94727/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910668326055831/4611686018427387904), (116377808077/2305843009213693952)), (106573/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796293484449317/576460752303423488), (116254741055/288230376151711744)), (26645/288230376151711744), by norm_num⟩
  | 5 => ⟨((596679383265189/72057594037927936), (406338494557/144115188075855872)), (93265/144115188075855872), by norm_num⟩
  | 4 => ⟨((186226058521141/4503599627370496), (152100824325/9007199254740992)), (139911/36028797018963968), by norm_num⟩
  | 3 => ⟨((371744651399625/2251799813685248), (758575282917/9007199254740992)), (43729/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223411144076367/4503599627370496), (755689886671/2251799813685248)), (349911/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209351146593221/2251799813685248), (2252697562009/2251799813685248)), (262535/1125899906842624), by norm_num⟩
  | 0 => ⟨((541859449147909/562949953421312), (1112058709653/562949953421312)), (1050985/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541859449147909/562949953421312), (1112058709653/562949953421312)), (4009189614302825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2086227553066789/2251799813685248), (8563170010699/2251799813685248)), (1013687/1125899906842624), by norm_num⟩
  | 2 => ⟨((1932797066969987/2251799813685248), (15867059859711/2251799813685248)), (943007/562949953421312), by norm_num⟩
  | 3 => ⟨((1658874255072359/2251799813685248), (6809621035561/562949953421312)), (6528481/2251799813685248), by norm_num⟩
  | 4 => ⟨((1221743532619393/2251799813685248), (20066268687009/1125899906842624)), (2444213/562949953421312), by norm_num⟩
  | 5 => ⟨((1324315447474011/4503599627370496), (1360902168299/70368744177664)), (21915227/4503599627370496), by norm_num⟩
  | 6 => ⟨((193869963229703/2251799813685248), (204893668067057/18014398509481984)), (54945277/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-163990341/67108864), (-2736366007/33554432)), (1/33554432), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-5583141165/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((42358331368509/9007199254740992), (-743384241052785/9007199254740992)), (118473857/18014398509481984), by norm_num⟩
  | 1 => ⟨((-58379805/4294967296), (512279705/2147483648)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((337478679/17179869184), (-2961357583/8589934592)), (119/4294967296), by norm_num⟩
  | 3 => ⟨((-325146281/17179869184), (2853141441/8589934592)), (115/4294967296), by norm_num⟩
  | 4 => ⟨((234948407/17179869184), (-4123319721/17179869184)), (167/8589934592), by norm_num⟩
  | 5 => ⟨((-8488603/1073741824), (1191792687/8589934592)), (97/8589934592), by norm_num⟩
  | 6 => ⟨((65427249/17179869184), (-287060327/4294967296)), (375/68719476736), by norm_num⟩
  | 7 => ⟨((-432249309/274877906944), (3792964855/137438953472)), (621/274877906944), by norm_num⟩
  | 8 => ⟨((312340299/549755813888), (-342596203/34359738368)), (225/274877906944), by norm_num⟩
  | 9 => ⟨((-50154421/274877906944), (3520819163/1099511627776)), (581/2199023255552), by norm_num⟩
  | 10 => ⟨((231943875/4398046511104), (-2035295255/2199023255552)), (169/2199023255552), by norm_num⟩
  | 11 => ⟨((-121891641/8796093022208), (2139185427/8796093022208)), (357/17592186044416), by norm_num⟩
  | 12 => ⟨((234874771/70368744177664), (-4122027429/70368744177664)), (345/70368744177664), by norm_num⟩
  | 13 => ⟨((-52221185/70368744177664), (458238141/35184372088832)), (77/70368744177664), by norm_num⟩
  | 14 => ⟨((172501301/1125899906842624), (-1513689807/562949953421312)), (511/2251799813685248), by norm_num⟩
  | 15 => ⟨((-265916207/9007199254740992), (4666801353/9007199254740992)), (99/2251799813685248), by norm_num⟩
  | 16 => ⟨((384298347/72057594037927936), (-843049427/9007199254740992)), (575/72057594037927936), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-985997217811/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778121512016735/633825300114114700748351602688), (-291517710431/79228162514264337593543950336)), (5777/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((29515839356799/618970019642690137449562112), (-2623090040265/39614081257132168796771975168)), (1625/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((236092914963791/309485009821345068724781056), (-2786324313257/2475880078570760549798248448)), (27629/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770409609544379/154742504910672534362390528), (-1392763579815/77371252455336267181195264)), (13817/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548821207805697/9671406556917033397649408), (-40790390937/151115727451828646838272)), (3239/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258148036231115/604462909807314587353088), (-2283415519263/604462909807314587353088)), (11339/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886751073710749/75557863725914323419136), (-927240986653/18889465931478580854784)), (36861/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296758795300007/4722366482869645213696), (-2780335649089/4722366482869645213696)), (55309/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620374824134637/590295810358705651712), (-1910354203335/295147905179352825856)), (76077/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227766647050877/9223372036854775808), (-596563507781/9223372036854775808)), (95137/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455286998441135/2305843009213693952), (-5364431187173/9223372036854775808)), (107085/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592396773672173/1152921504606846976), (-669829514123/144115188075855872)), (26789/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193190621502019/144115188075855872), (-4682294565093/144115188075855872)), (93841/144115188075855872), by norm_num⟩
  | 4 => ⟨((372388203538011/9007199254740992), (-7010436322869/36028797018963968)), (140921/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486653051035751/9007199254740992), (-8740327404317/9007199254740992)), (176429/9007199254740992), by norm_num⟩
  | 2 => ⟨((555685545162621/1125899906842624), (-17412667226649/4503599627370496)), (353697/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104151719047223/1125899906842624), (-25949613169369/2251799813685248)), (532649/2251799813685248), by norm_num⟩
  | 0 => ⟨((541291887149967/562949953421312), (-51225154006065/2251799813685248)), (1073753/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541291887149967/562949953421312), (-51225154006065/2251799813685248)), (4096042641646575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2080702941989817/2251799813685248), (-98508793234553/2251799813685248)), (528435/562949953421312), by norm_num⟩
  | 2 => ⟨((1918296965923961/2251799813685248), (-182047742121051/2251799813685248)), (2045603/1125899906842624), by norm_num⟩
  | 3 => ⟨((1619469833374555/2251799813685248), (-77542779167521/562949953421312)), (1908017/562949953421312), by norm_num⟩
  | 4 => ⟨((1121980916882245/2251799813685248), (-223071679630893/1125899906842624)), (13080339/2251799813685248), by norm_num⟩
  | 5 => ⟨((941289074094105/4503599627370496), (-889180880544173/4503599627370496)), (36435917/4503599627370496), by norm_num⟩
  | 6 => ⟨((42358331368509/9007199254740992), (-743384241052785/9007199254740992)), (118473857/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-5583141165/67108864)), (1/33554432), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-42607059/16777216), (-5687579263/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1417701431330459/18014398509481984), (-101490643618173/18014398509481984)), (117912399/18014398509481984), by norm_num⟩
  | 1 => ⟨((15550611/67108864), (569978727/34359738368)), (665/34359738368), by norm_num⟩
  | 2 => ⟨((-5860841623/17179869184), (-419566895/17179869184)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((2876148421/8589934592), (411796373/17179869184)), (485/17179869184), by norm_num⟩
  | 4 => ⟨((-132322555/536870912), (-303127323/17179869184)), (179/8589934592), by norm_num⟩
  | 5 => ⟨((311692551/2147483648), (178507981/17179869184)), (423/34359738368), by norm_num⟩
  | 6 => ⟨((-2447359191/34359738368), (-350403905/68719476736)), (417/68719476736), by norm_num⟩
  | 7 => ⟨((4117771313/137438953472), (147391845/68719476736)), (11/4294967296), by norm_num⟩
  | 8 => ⟨((-1515565795/137438953472), (-216993147/274877906944)), (521/549755813888), by norm_num⟩
  | 9 => ⟨((7933317337/2199023255552), (567931627/2199023255552)), (171/549755813888), by norm_num⟩
  | 10 => ⟨((-145994805/137438953472), (-83612001/1099511627776)), (101/1099511627776), by norm_num⟩
  | 11 => ⟨((5002156155/17592186044416), (179047589/8796093022208)), (217/8796093022208), by norm_num⟩
  | 12 => ⟨((-4909514521/70368744177664), (-351463133/70368744177664)), (107/17592186044416), by norm_num⟩
  | 13 => ⟨((4447927977/281474976710656), (39802375/35184372088832)), (195/140737488355328), by norm_num⟩
  | 14 => ⟨((-7483801435/2251799813685248), (-535751609/2251799813685248)), (329/1125899906842624), by norm_num⟩
  | 15 => ⟨((1469039777/2251799813685248), (420663445/9007199254740992)), (519/9007199254740992), by norm_num⟩
  | 16 => ⟨((-4325497981/36028797018963968), (-309654461/36028797018963968)), (3/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-3999182427051/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889020300714643/316912650057057350374175801344), (-1182298182359/158456325028528675187087900672)), (23167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888922212721321/39614081257132168796771975168), (-5319139889817/39614081257132168796771975168)), (13035/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888645451216077/2475880078570760549798248448), (-5650118743069/2475880078570760549798248448)), (6927/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885155509068547/77371252455336267181195264), (-1412117029609/38685626227668133590597632)), (13859/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387182002720139/2417851639229258349412352), (-5293685427019/9671406556917033397649408)), (6499/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258065722131665/604462909807314587353088), (-289388857043/37778931862957161709568)), (22757/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886615877035253/75557863725914323419136), (-3760412093483/37778931862957161709568)), (36999/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648328071264419/2361183241434822606848), (-1409435913195/1180591620717411303424)), (55533/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810115819758435/295147905179352825856), (-7747228068919/590295810358705651712)), (76413/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455487786213225/18446744073709551616), (-4838516843619/36893488147419103232)), (95599/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820939021240603/9223372036854775808), (-10877040498059/9223372036854775808)), (6729/576460752303423488), by norm_num⟩
  | 6 => ⟨((1592182579052913/1152921504606846976), (-10865019288945/1152921504606846976)), (53903/576460752303423488), by norm_num⟩
  | 5 => ⟨((596498671200683/72057594037927936), (-9493377364685/144115188075855872)), (23623/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489251217942553/36028797018963968), (-7106530208449/18014398509481984)), (35515/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486255710009005/9007199254740992), (-17719118387371/9007199254740992)), (44535/2251799813685248), by norm_num⟩
  | 2 => ⟨((138867926268783/281474976710656), (-8824206658801/1125899906842624)), (89495/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103434977245227/1125899906842624), (-3287028483951/140737488355328)), (33827/140737488355328), by norm_num⟩
  | 0 => ⟨((1080853147207537/1125899906842624), (-25944558785187/562949953421312)), (549793/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080853147207537/1125899906842624), (-25944558785187/562949953421312)), (2097293858054732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1035217285499895/1125899906842624), (-99626113637471/1125899906842624)), (1106269/1125899906842624), by norm_num⟩
  | 2 => ⟨((471511481272231/562949953421312), (-183203985181789/1125899906842624)), (1115057/562949953421312), by norm_num⟩
  | 3 => ⟨((760039682478859/1125899906842624), (-613786585489899/2251799813685248)), (1115381/281474976710656), by norm_num⟩
  | 4 => ⟨((858827366220409/2251799813685248), (-828674305256395/2251799813685248)), (16911441/2251799813685248), by norm_num⟩
  | 5 => ⟨((2824592825019/281474976710656), (-316053037535847/1125899906842624)), (50693823/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1417701431330459/18014398509481984), (-101490643618173/18014398509481984)), (117912399/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-5687579263/67108864)), (1/33554432), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-43349291/16777216), (-1446664787/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-224503359967435/18014398509481984), (670579674599369/9007199254740992)), (115251469/18014398509481984), by norm_num⟩
  | 1 => ⟨((160348883/4294967296), (-1915814565/8589934592)), (331/17179869184), by norm_num⟩
  | 2 => ⟨((-120090581/2147483648), (2869633761/8589934592)), (249/8589934592), by norm_num⟩
  | 3 => ⟨((959357945/17179869184), (-5731102981/17179869184)), (125/4294967296), by norm_num⟩
  | 4 => ⟨((-718494889/17179869184), (4292212541/17179869184)), (377/17179869184), by norm_num⟩
  | 5 => ⟨((860967331/34359738368), (-5143327853/34359738368)), (227/17179869184), by norm_num⟩
  | 6 => ⟨((-214935635/17179869184), (5136011081/68719476736)), (455/68719476736), by norm_num⟩
  | 7 => ⟨((367936925/68719476736), (-4396032615/137438953472)), (391/137438953472), by norm_num⟩
  | 8 => ⟨((-1102240521/549755813888), (3292334195/274877906944)), (147/137438953472), by norm_num⟩
  | 9 => ⟨((733781667/1099511627776), (-4383534135/1099511627776)), (393/1099511627776), by norm_num⟩
  | 10 => ⟨((-879285369/4398046511104), (328297367/274877906944)), (473/4398046511104), by norm_num⟩
  | 11 => ⟨((957855839/17592186044416), (-5722129557/17592186044416)), (517/17592186044416), by norm_num⟩
  | 12 => ⟨((-956493217/70368744177664), (1428497349/17592186044416)), (259/35184372088832), by norm_num⟩
  | 13 => ⟨((6887975/2199023255552), (-1316737111/70368744177664)), (479/281474976710656), by norm_num⟩
  | 14 => ⟨((-188658551/281474976710656), (2254052491/562949953421312)), (103/281474976710656), by norm_num⟩
  | 15 => ⟨((18839017/140737488355328), (-1800676745/2251799813685248)), (661/9007199254740992), by norm_num⟩
  | 16 => ⟨((-225746605/9007199254740992), (5394345439/36028797018963968)), (497/36028797018963968), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (1131092581645/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888990304999689/316912650057057350374175801344), (83591522343/19807040628566084398385987584)), (46233/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236106898592333/4951760157141521099596496896), (1504308998143/19807040628566084398385987584)), (13005/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((59017964291761/77371252455336267181195264), (1597906917773/1237940039285380274899124224)), (55281/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442560280019573/38685626227668133590597632), (3194866063367/154742504910672534362390528)), (13823/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548663220196699/9671406556917033397649408), (2994180265047/9671406556917033397649408)), (6481/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258009768395943/604462909807314587353088), (654725360851/151115727451828646838272)), (45379/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943263167415097/37778931862957161709568), (4253828863597/75557863725914323419136)), (36881/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296590194318655/4722366482869645213696), (1594361111109/2361183241434822606848)), (55341/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810071460964329/295147905179352825856), (2190907127411/295147905179352825856)), (76125/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821843185262049/73786976294838206464), (2736626134275/36893488147419103232)), (95203/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910410799231767/4611686018427387904), (6151891726481/9223372036854775808)), (3349/288230376151711744), by norm_num⟩
  | 6 => ⟨((796035092629091/576460752303423488), (1536250458993/288230376151711744)), (107249/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192904640712757/144115188075855872), (1342283586729/36028797018963968)), (93935/144115188075855872), by norm_num⟩
  | 4 => ⟨((186140426802341/4503599627370496), (4019119574149/18014398509481984)), (35271/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486115558820797/9007199254740992), (626299347315/562949953421312)), (176675/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221664998117511/4503599627370496), (9980374890107/2251799813685248)), (354311/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206682271936297/2251799813685248), (29739745835061/2251799813685248)), (66735/281474976710656), by norm_num⟩
  | 0 => ⟨((2161904260275041/2251799813685248), (7334766612093/281474976710656)), (1077457/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161904260275041/2251799813685248), (7334766612093/281474976710656)), (4110172280318450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2074068431363651/2251799813685248), (56335605289373/1125899906842624)), (132815/140737488355328), by norm_num⟩
  | 2 => ⟨((952363755920781/1125899906842624), (207556461781969/2251799813685248)), (4127285/2251799813685248), by norm_num⟩
  | 3 => ⟨((1592018610069833/2251799813685248), (10972847714247/70368744177664)), (3871569/1125899906842624), by norm_num⟩
  | 4 => ⟨((535400654158377/1125899906842624), (248249105063443/1125899906842624)), (13363601/2251799813685248), by norm_num⟩
  | 5 => ⟨((799453809138191/4503599627370496), (944401770973961/4503599627370496)), (37205379/4503599627370496), by norm_num⟩
  | 6 => ⟨((-224503359967435/18014398509481984), (670579674599369/9007199254740992)), (115251469/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1446664787/16777216)), (1/33554432), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-88110603/33554432), (-2940451951/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1232460994918101/18014398509481984), (425314537737255/18014398509481984)), (3411315/1125899906842624), by norm_num⟩
  | 1 => ⟨((-447303671/2147483648), (-308723367/4294967296)), (5/536870912), by norm_num⟩
  | 2 => ⟨((5447304251/17179869184), (469957609/4294967296)), (123/8589934592), by norm_num⟩
  | 3 => ⟨((-345509167/1073741824), (-1907728647/17179869184)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((4207641645/17179869184), (363007667/4294967296)), (97/8589934592), by norm_num⟩
  | 5 => ⟨((-5124103759/34359738368), (-442073995/8589934592)), (119/17179869184), by norm_num⟩
  | 6 => ⟨((5200149623/68719476736), (1794538929/68719476736)), (61/17179869184), by norm_num⟩
  | 7 => ⟨((-4523420631/137438953472), (-780502005/68719476736)), (107/68719476736), by norm_num⟩
  | 8 => ⟨((1721456951/137438953472), (1188127933/274877906944)), (165/274877906944), by norm_num⟩
  | 9 => ⟨((-4658679389/1099511627776), (-401920239/274877906944)), (225/1099511627776), by norm_num⟩
  | 10 => ⟨((1418345393/1099511627776), (1957848297/4398046511104)), (69/1099511627776), by norm_num⟩
  | 11 => ⟨((-1570248863/4398046511104), (-2167532025/17592186044416)), (77/4398046511104), by norm_num⟩
  | 12 => ⟨((199194079/2199023255552), (1099849981/35184372088832)), (315/70368744177664), by norm_num⟩
  | 13 => ⟨((-1492802075/70368744177664), (-515156607/70368744177664)), (297/281474976710656), by norm_num⟩
  | 14 => ⟨((5194136471/1125899906842624), (1792463827/1125899906842624)), (261/1125899906842624), by norm_num⟩
  | 15 => ⟨((-4216977341/4503599627370496), (-1455252357/4503599627370496)), (107/2251799813685248), by norm_num⟩
  | 16 => ⟨((1604835267/9007199254740992), (1107637113/18014398509481984)), (165/18014398509481984), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (432854323083/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777919491138639/633825300114114700748351602688), (7996789429/9903520314283042199192993792)), (23063/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944393324715311/19807040628566084398385987584), (71954822935/4951760157141521099596496896)), (25947/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888502325844405/2475880078570760549798248448), (611452263399/2475880078570760549798248448)), (27569/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770168916197065/154742504910672534362390528), (611268158789/154742504910672534362390528)), (55141/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774297938439335/4835703278458516698824704), (572868365767/9671406556917033397649408)), (51697/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9827743675891/4722366482869645213696), (501064374803/604462909807314587353088)), (45237/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943215898369635/37778931862957161709568), (813863335811/75557863725914323419136)), (36757/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296519859711811/4722366482869645213696), (610077199249/4722366482869645213696)), (55139/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620047135217073/590295810358705651712), (209584001659/147573952589676412928)), (75823/590295810358705651712), by norm_num⟩
  | 8 => ⟨((7116112636143/288230376151711744), (1047140405793/73786976294838206464)), (94787/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910345176237939/4611686018427387904), (1176961995061/9223372036854775808)), (13331/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591941306994523/1152921504606846976), (587812389835/576460752303423488)), (13333/144115188075855872), by norm_num⟩
  | 5 => ⟨((596397264491487/72057594037927936), (1027169356227/144115188075855872)), (93349/144115188075855872), by norm_num⟩
  | 4 => ⟨((186120442876793/4503599627370496), (1537754478183/36028797018963968)), (140059/36028797018963968), by norm_num⟩
  | 3 => ⟨((185740618630393/1125899906842624), (958477659695/4503599627370496)), (175137/9007199254740992), by norm_num⟩
  | 2 => ⟨((8676997312707/17592186044416), (1909121490245/2251799813685248)), (1369/17592186044416), by norm_num⟩
  | 1 => ⟨((2206220036412857/2251799813685248), (5688354731057/2251799813685248)), (526179/2251799813685248), by norm_num⟩
  | 0 => ⟨((135078108732055/140737488355328), (11221623249953/2251799813685248)), (527161/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((135078108732055/140737488355328), (11221623249953/2251799813685248)), (2010959629539107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2074284971600727/2251799813685248), (1346296981015/140737488355328)), (254295/281474976710656), by norm_num⟩
  | 2 => ⟨((955278997999407/1125899906842624), (19842641983067/1125899906842624)), (3786895/2251799813685248), by norm_num⟩
  | 3 => ⟨((202541146871545/281474976710656), (67342608471837/2251799813685248)), (1639881/562949953421312), by norm_num⟩
  | 4 => ⟨((72745465438973/140737488355328), (48457768120639/1125899906842624)), (1229053/281474976710656), by norm_num⟩
  | 5 => ⟨((298724263274567/1125899906842624), (200377763580361/4503599627370496)), (11010875/2251799813685248), by norm_num⟩
  | 6 => ⟨((1232460994918101/18014398509481984), (425314537737255/18014398509481984)), (3411315/1125899906842624), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-2940451951/33554432)), (1/33554432), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨46,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile046Terms2
