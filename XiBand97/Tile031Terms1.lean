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
namespace Reinmann.XiBand97.Tile031Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63483/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63483/2560))
  have he : value ((69/80), (63483/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1828276245/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-319160604068311/4503599627370496), (1193871740083101/9007199254740992)), (22567665/562949953421312), by norm_num⟩
  | 1 => ⟨((334390413/2147483648), (-625420649/2147483648)), (381/4294967296), by norm_num⟩
  | 2 => ⟨((-367365417/2147483648), (687094811/2147483648)), (421/4294967296), by norm_num⟩
  | 3 => ⟨((269061441/2147483648), (-1006467737/4294967296)), (311/4294967296), by norm_num⟩
  | 4 => ⟨((-591188411/8589934592), (17276841/134217728)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((519589483/17179869184), (-121475519/2147483648)), (305/17179869184), by norm_num⟩
  | 6 => ⟨((-190275797/17179869184), (711757323/34359738368)), (225/34359738368), by norm_num⟩
  | 7 => ⟨((119451045/34359738368), (-893651819/137438953472)), (285/137438953472), by norm_num⟩
  | 8 => ⟨((-65615193/68719476736), (490888435/274877906944)), (315/549755813888), by norm_num⟩
  | 9 => ⟨((512609119/2199023255552), (-239687141/549755813888)), (155/1099511627776), by norm_num⟩
  | 10 => ⟨((-225263471/4398046511104), (210658591/2199023255552)), (275/8796093022208), by norm_num⟩
  | 11 => ⟨((179983431/17592186044416), (-673257067/35184372088832)), (221/35184372088832), by norm_num⟩
  | 12 => ⟨((-263642679/140737488355328), (986197983/281474976710656)), (163/140737488355328), by norm_num⟩
  | 13 => ⟨((178240669/562949953421312), (-1333475967/2251799813685248)), (111/562949953421312), by norm_num⟩
  | 14 => ⟨((-111895651/2251799813685248), (837127477/9007199254740992)), (281/9007199254740992), by norm_num⟩
  | 15 => ⟨((262250533/36028797018963968), (-245247609/18014398509481984)), (83/18014398509481984), by norm_num⟩
  | 16 => ⟨((-576223317/576460752303423488), (269432037/144115188075855872)), (367/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (2685711280829/10141204801825835211973625643008)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889520225721511/316912650057057350374175801344), (3179341309871/633825300114114700748351602688)), (138769/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890047180879539/39614081257132168796771975168), (3576154379451/39614081257132168796771975168)), (78073/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889840942905031/2475880078570760549798248448), (1899464166377/1237940039285380274899124224)), (165939/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885753374453619/77371252455336267181195264), (3798100794053/154742504910672534362390528)), (165979/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549849262067711/9671406556917033397649408), (1779920194997/4835703278458516698824704)), (155647/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259047070022815/604462909807314587353088), (194623838221/37778931862957161709568)), (136233/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472052760222399/18889465931478580854784), (2529286085935/37778931862957161709568)), (13841/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297852928724483/4722366482869645213696), (3792487831135/4722366482869645213696)), (166161/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621877890217567/590295810358705651712), (5212329355363/590295810358705651712)), (114291/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824009959361963/73786976294838206464), (813987599309/9223372036854775808)), (285895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455814139655075/2305843009213693952), (7321062887795/9223372036854775808)), (160931/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594501822013591/1152921504606846976), (7315033977669/1152921504606846976)), (322149/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597514293729381/72057594037927936), (1598469073649/36028797018963968)), (282205/144115188075855872), by norm_num⟩
  | 4 => ⟨((373075468059609/9007199254740992), (9577267793319/36028797018963968)), (423955/36028797018963968), by norm_num⟩
  | 3 => ⟨((372518897817611/2251799813685248), (5973950558583/4503599627370496)), (531079/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114773010180301/2251799813685248), (5956210861191/1125899906842624)), (532785/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109203233814859/1125899906842624), (4445023834113/281474976710656)), (200863/281474976710656), by norm_num⟩
  | 0 => ⟨((1092482457797997/1125899906842624), (35207009858039/1125899906842624)), (1624053/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092482457797997/1125899906842624), (35207009858039/1125899906842624)), (6195270542625045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058955933655533/1125899906842624), (68324085343059/1125899906842624)), (1626635/562949953421312), by norm_num⟩
  | 2 => ⟨((61990384424909/70368744177664), (257046634948279/2251799813685248)), (1628629/281474976710656), by norm_num⟩
  | 3 => ⟨((214770544397631/281474976710656), (226441723549059/1125899906842624)), (6482517/562949953421312), by norm_num⟩
  | 4 => ⟨((1219906546782937/2251799813685248), (691116671319055/2251799813685248)), (6250047/281474976710656), by norm_num⟩
  | 5 => ⟨((224382674553767/1125899906842624), (748821228964533/2251799813685248)), (5304195/140737488355328), by norm_num⟩
  | 6 => ⟨((-319160604068311/4503599627370496), (1193871740083101/9007199254740992)), (22567665/562949953421312), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1828276245/33554432)), (3/33554432), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-478986271/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((263320508544205/2251799813685248), (-647143446510743/9007199254740992)), (60356519/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1156459575/4294967296), (355268205/2147483648)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((665711645/2147483648), (-102254409/536870912)), (5/134217728), by norm_num⟩
  | 3 => ⟨((-255476285/1073741824), (313932637/2147483648)), (125/4294967296), by norm_num⟩
  | 4 => ⟨((1176511771/8589934592), (-361428305/4294967296)), (73/4294967296), by norm_num⟩
  | 5 => ⟨((-541803693/8589934592), (332887771/8589934592)), (137/17179869184), by norm_num⟩
  | 6 => ⟨((831699405/34359738368), (-511001613/34359738368)), (107/34359738368), by norm_num⟩
  | 7 => ⟨((-547159615/68719476736), (336178485/68719476736)), (143/137438953472), by norm_num⟩
  | 8 => ⟨((1259881573/549755813888), (-48379973/34359738368)), (167/549755813888), by norm_num⟩
  | 9 => ⟨((-1289326457/2199023255552), (198042675/549755813888)), (87/1099511627776), by norm_num⟩
  | 10 => ⟨((74219597/549755813888), (-364808089/4398046511104)), (81/4398046511104), by norm_num⟩
  | 11 => ⟨((-62144341/2199023255552), (19090947/1099511627776)), (69/17592186044416), by norm_num⟩
  | 12 => ⟨((763160711/140737488355328), (-234445493/70368744177664)), (27/35184372088832), by norm_num⟩
  | 13 => ⟨((-540689993/562949953421312), (166101753/281474976710656)), (155/1125899906842624), by norm_num⟩
  | 14 => ⟨((711419839/4503599627370496), (-109275263/1125899906842624)), (13/562949953421312), by norm_num⟩
  | 15 => ⟨((-873655849/36028797018963968), (536779929/36028797018963968)), (65/18014398509481984), by norm_num⟩
  | 16 => ⟨((1005833467/288230376151711744), (-617990731/288230376151711744)), (19/36028797018963968), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-717667774261/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905353834111/633825300114114700748351602688), (-849446744449/633825300114114700748351602688)), (23071/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236236938612381/4951760157141521099596496896), (-119432686809/4951760157141521099596496896)), (103825/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944840096931339/1237940039285380274899124224), (-1014972199351/2475880078570760549798248448)), (6895/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771346452300739/154742504910672534362390528), (-507370467909/77371252455336267181195264)), (110327/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387424866111187/2417851639229258349412352), (-475536991271/4835703278458516698824704)), (6465/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314729119311865/151115727451828646838272), (-415972085877/302231454903657293676544)), (90517/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943999863630963/37778931862957161709568), (-168931127791/9444732965739290427392)), (147103/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648847615021599/2361183241434822606848), (-1013184215791/4722366482869645213696)), (110341/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621662331460423/590295810358705651712), (-348118619245/147573952589676412928)), (151737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911871212108289/36893488147419103232), (-869806468025/36893488147419103232)), (189701/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822958208971519/9223372036854775808), (-977858878767/4611686018427387904)), (213455/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594206751507841/1152921504606846976), (-1954035649165/1152921504606846976)), (213507/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194774082805009/144115188075855872), (-426972681301/36028797018963968)), (46719/36028797018963968), by norm_num⟩
  | 4 => ⟨((745963730932333/18014398509481984), (-159878744209/2251799813685248)), (280431/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489620395616991/9007199254740992), (-3190977253535/9007199254740992)), (175371/4503599627370496), by norm_num⟩
  | 2 => ⟨((557168481076463/1125899906842624), (-6362204286079/4503599627370496)), (702097/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108596757315987/1125899906842624), (-4747039955845/1125899906842624)), (527343/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182916502575117/2251799813685248), (-9396072731479/1125899906842624)), (2115573/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182916502575117/2251799813685248), (-9396072731479/1125899906842624)), (8070270546920012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2115983527277123/2251799813685248), (-18217287434067/1125899906842624)), (4137025/2251799813685248), by norm_num⟩
  | 2 => ⟨((1987769419936531/2251799813685248), (-68474079956641/2251799813685248)), (7908881/2251799813685248), by norm_num⟩
  | 3 => ⟨((1752615193954601/2251799813685248), (-60445285308619/1125899906842624)), (7222039/1125899906842624), by norm_num⟩
  | 4 => ⟨((1357600915248885/2251799813685248), (-188182492583889/2251799813685248)), (12017527/1125899906842624), by norm_num⟩
  | 5 => ⟨((1605531347487887/4503599627370496), (-56727228284915/562949953421312)), (65996965/4503599627370496), by norm_num⟩
  | 6 => ⟨((263320508544205/2251799813685248), (-647143446510743/9007199254740992)), (60356519/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-478986271/8388608)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-498812799/8388608)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-1109398588614559/9007199254740992), (-128207461796417/4503599627370496)), (293308261/9007199254740992), by norm_num⟩
  | 1 => ⟨((1268492523/4294967296), (293186251/4294967296)), (337/4294967296), by norm_num⟩
  | 2 => ⟨((-95053507/268435456), (-351514963/4294967296)), (407/4294967296), by norm_num⟩
  | 3 => ⟨((607808947/2147483648), (70241339/1073741824)), (327/4294967296), by norm_num⟩
  | 4 => ⟨((-1457462201/8589934592), (-336862749/8589934592)), (395/8589934592), by norm_num⟩
  | 5 => ⟨((1397936689/17179869184), (323104637/17179869184)), (381/17179869184), by norm_num⟩
  | 6 => ⟨((-1117368593/34359738368), (-258257027/34359738368)), (307/34359738368), by norm_num⟩
  | 7 => ⟨((1531047353/137438953472), (88467615/34359738368)), (423/137438953472), by norm_num⟩
  | 8 => ⟨((-917822803/274877906944), (-53034019/68719476736)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((978152427/1099511627776), (113040021/549755813888)), (275/1099511627776), by norm_num⟩
  | 10 => ⟨((-58637677/274877906944), (-108423253/2199023255552)), (133/2199023255552), by norm_num⟩
  | 11 => ⟨((1636154281/35184372088832), (189081895/17592186044416)), (467/35184372088832), by norm_num⟩
  | 12 => ⟨((-1307775539/140737488355328), (-302265721/140737488355328)), (47/17592186044416), by norm_num⟩
  | 13 => ⟨((482447505/281474976710656), (55753965/140737488355328)), (279/562949953421312), by norm_num⟩
  | 14 => ⟨((-1322124105/4503599627370496), (-305582101/4503599627370496)), (385/4503599627370496), by norm_num⟩
  | 15 => ⟨((845417371/18014398509481984), (390802067/36028797018963968)), (495/36028797018963968), by norm_num⟩
  | 16 => ⟨((-1013611159/144115188075855872), (-234275607/144115188075855872)), (299/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-3796398639185/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778768199858681/633825300114114700748351602688), (-4492888123327/633825300114114700748351602688)), (138963/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889740647951893/39614081257132168796771975168), (-5053556391289/39614081257132168796771975168)), (19547/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472378729967245/618970019642690137449562112), (-1342066897123/618970019642690137449562112)), (20775/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771180352928785/154742504910672534362390528), (-1341747376993/38685626227668133590597632)), (166255/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549542869890163/9671406556917033397649408), (-5030194852337/9671406556917033397649408)), (155923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258778581260943/604462909807314587353088), (-2200031425867/302231454903657293676544)), (136491/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943887002807085/37778931862957161709568), (-7147556907447/75557863725914323419136)), (221909/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297524504584719/4722366482869645213696), (-2679220481879/2361183241434822606848)), (166529/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621425255897989/590295810358705651712), (-7364238579699/590295810358705651712)), (229135/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823442592146155/73786976294838206464), (-4599936389919/36893488147419103232)), (286655/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455654027418501/2305843009213693952), (-5171199400647/4611686018427387904)), (80703/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796929338905931/576460752303423488), (-10333079078659/1152921504606846976)), (323219/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149307851507551/18014398509481984), (-2257740866511/36028797018963968)), (283275/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491447180526721/36028797018963968), (-13525493675801/36028797018963968)), (212915/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488996721112343/9007199254740992), (-8435112182021/4503599627370496)), (533895/9007199254740992), by norm_num⟩
  | 2 => ⟨((556839235353537/1125899906842624), (-8407652677793/1125899906842624)), (268155/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107522562009601/1125899906842624), (-12542909647041/562949953421312)), (810519/1125899906842624), by norm_num⟩
  | 0 => ⟨((1088967522539861/1125899906842624), (-49624044084001/1125899906842624)), (1645339/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1088967522539861/1125899906842624), (-49624044084001/1125899906842624)), (6276470188621139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1051059434505099/1125899906842624), (-47996249059213/562949953421312)), (3327773/1125899906842624), by norm_num⟩
  | 2 => ⟨((973009561959481/1125899906842624), (-89611714305957/562949953421312)), (847573/140737488355328), by norm_num⟩
  | 3 => ⟨((50771973864115/70368744177664), (-619543917560445/2251799813685248)), (27756687/2251799813685248), by norm_num⟩
  | 4 => ⟨((250446963633703/562949953421312), (-894018159841901/2251799813685248)), (27663589/1125899906842624), by norm_num⟩
  | 5 => ⟨((181464119611941/4503599627370496), (-795467278059173/2251799813685248)), (46580339/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1109398588614559/9007199254740992), (-128207461796417/4503599627370496)), (293308261/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-498812799/8388608)), (3/33554432), by norm_num⟩, -9, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-2067652003/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((46486510789421/1125899906842624), (494345650428699/4503599627370496)), (224027863/9007199254740992), by norm_num⟩
  | 1 => ⟨((-110163345/1073741824), (-1171496195/4294967296)), (67/1073741824), by norm_num⟩
  | 2 => ⟨((547491257/4294967296), (727764671/2147483648)), (335/4294967296), by norm_num⟩
  | 3 => ⟨((-226744111/2147483648), (-301404545/1073741824)), (35/536870912), by norm_num⟩
  | 4 => ⟨((563437949/8589934592), (374481079/2147483648)), (175/4294967296), by norm_num⟩
  | 5 => ⟨((-280018141/8589934592), (-1488880837/17179869184)), (175/8589934592), by norm_num⟩
  | 6 => ⟨((231939647/17179869184), (1233243297/34359738368)), (73/8589934592), by norm_num⟩
  | 7 => ⟨((-164670963/34359738368), (-109446231/8589934592)), (209/68719476736), by norm_num⟩
  | 8 => ⟨((409191971/274877906944), (1087854669/274877906944)), (131/137438953472), by norm_num⟩
  | 9 => ⟨((-225956411/549755813888), (-1201429911/1099511627776)), (291/1099511627776), by norm_num⟩
  | 10 => ⟨((449184471/4398046511104), (597088235/2199023255552)), (73/1099511627776), by norm_num⟩
  | 11 => ⟨((-202942087/8796093022208), (-539530373/8796093022208)), (133/8796093022208), by norm_num⟩
  | 12 => ⟨((336194761/70368744177664), (111723551/8796093022208)), (111/35184372088832), by norm_num⟩
  | 13 => ⟨((-128525015/140737488355328), (-683378695/281474976710656)), (171/281474976710656), by norm_num⟩
  | 14 => ⟨((364997331/2251799813685248), (970361293/2251799813685248)), (245/2251799813685248), by norm_num⟩
  | 15 => ⟨((-483724957/18014398509481984), (-80375241/1125899906842624)), (327/18014398509481984), by norm_num⟩
  | 16 => ⟨((300502841/72057594037927936), (798899883/72057594037927936)), (205/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (788745352829/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778661454366091/633825300114114700748351602688), (116666677307/39614081257132168796771975168)), (138575/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236202636015453/4951760157141521099596496896), (2099606005491/39614081257132168796771975168)), (155915/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944694287064361/1237940039285380274899124224), (557585890689/618970019642690137449562112)), (165681/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771054779032899/154742504910672534362390528), (2229794949123/154742504910672534362390528)), (20713/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549425963940233/9671406556917033397649408), (1044925016855/4835703278458516698824704)), (38843/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629338553780981/302231454903657293676544), (114252265041/37778931862957161709568)), (135975/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887610645280509/75557863725914323419136), (2969467039139/75557863725914323419136)), (221005/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297403325747453/4722366482869645213696), (556536329291/1180591620717411303424)), (82897/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621260812523699/590295810358705651712), (3059398762677/590295810358705651712)), (3563/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1823240300249957/73786976294838206464), (955480804761/18446744073709551616)), (285139/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822393010538021/9223372036854775808), (4296468597833/9223372036854775808)), (80229/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398410292018675/288230376151711744), (4292478076569/1152921504606846976)), (321085/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194278765843177/144115188075855872), (3751433457167/144115188075855872)), (70285/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491183627665033/36028797018963968), (2809095823585/18014398509481984)), (105523/9007199254740992), by norm_num⟩
  | 3 => ⟨((46521534668057/281474976710656), (3421429319/4398046511104)), (132071/2251799813685248), by norm_num⟩
  | 2 => ⟨((2226806908586871/4503599627370496), (6983658961195/2251799813685248)), (66161/281474976710656), by norm_num⟩
  | 1 => ⟨((2214382012750251/2251799813685248), (2604273265737/281474976710656)), (199113/281474976710656), by norm_num⟩
  | 0 => ⟨((1088625180198417/1125899906842624), (20601654036091/1125899906842624)), (1603023/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088625180198417/1125899906842624), (20601654036091/1125899906842624)), (6115047459128951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2104415050775211/2251799813685248), (79678412623085/2251799813685248)), (6317139/2251799813685248), by norm_num⟩
  | 2 => ⟨((490964386533743/562949953421312), (148926605044417/2251799813685248)), (3063599/562949953421312), by norm_num⟩
  | 3 => ⟨((425721383459223/562949953421312), (259766108300799/2251799813685248)), (11497867/1125899906842624), by norm_num⟩
  | 4 => ⟨((628905974038133/1125899906842624), (392887454131719/2251799813685248)), (5010727/281474976710656), by norm_num⟩
  | 5 => ⟨((1268079281677099/4503599627370496), (438918709427709/2251799813685248)), (58770441/2251799813685248), by norm_num⟩
  | 6 => ⟨((46486510789421/1125899906842624), (494345650428699/4503599627370496)), (224027863/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-2067652003/33554432)), (3/33554432), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1067127145/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((705087727247333/9007199254740992), (-689031190542345/9007199254740992)), (55802243/4503599627370496), by norm_num⟩
  | 1 => ⟨((-431183413/2147483648), (842728667/4294967296)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((552981809/2147483648), (-16887159/67108864)), (91/2147483648), by norm_num⟩
  | 3 => ⟨((-14774691/67108864), (115505887/536870912)), (79/2147483648), by norm_num⟩
  | 4 => ⟨((606341347/4294967296), (-592533501/4294967296)), (103/4294967296), by norm_num⟩
  | 5 => ⟨((-622093939/8589934592), (607927369/8589934592)), (27/2147483648), by norm_num⟩
  | 6 => ⟨((1063759633/34359738368), (-1039535277/34359738368)), (187/34359738368), by norm_num⟩
  | 7 => ⟨((-389784227/34359738368), (190453953/17179869184)), (139/68719476736), by norm_num⟩
  | 8 => ⟨((999776803/274877906944), (-977009489/274877906944)), (181/274877906944), by norm_num⟩
  | 9 => ⟨((-284930763/274877906944), (278442207/274877906944)), (105/549755813888), by norm_num⟩
  | 10 => ⟨((292333191/1099511627776), (-8927377/34359738368)), (109/2199023255552), by norm_num⟩
  | 11 => ⟨((-545323513/8796093022208), (266452595/4398046511104)), (13/1099511627776), by norm_num⟩
  | 12 => ⟨((233121199/17592186044416), (-911249883/70368744177664)), (45/17592186044416), by norm_num⟩
  | 13 => ⟨((-735931163/281474976710656), (719172247/281474976710656)), (9/17592186044416), by norm_num⟩
  | 14 => ⟨((539321761/1125899906842624), (-1054080225/2251799813685248)), (107/1125899906842624), by norm_num⟩
  | 15 => ⟨((-368888801/4503599627370496), (720976639/9007199254740992)), (37/2251799813685248), by norm_num⟩
  | 16 => ⟨((946181093/72057594037927936), (-231158571/18014398509481984)), (3/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-504033422289/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222319518862357/79228162514264337593543950336), (-596361842427/316912650057057350374175801344)), (46159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889502706617689/39614081257132168796771975168), (-1341555454069/39614081257132168796771975168)), (103865/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944631451558323/1237940039285380274899124224), (-1425081052597/2475880078570760549798248448)), (110365/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770929230936321/154742504910672534362390528), (-712359686195/77371252455336267181195264)), (110375/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549308393123963/9671406556917033397649408), (-1335290251101/9671406556917033397649408)), (1617/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1258574363539339/604462909807314587353088), (-583997474761/302231454903657293676544)), (45281/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887443930646221/75557863725914323419136), (-1897272053173/75557863725914323419136)), (73591/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81079906465529/295147905179352825856), (-711162282739/2361183241434822606848)), (27601/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810544764379281/295147905179352825856), (-1954673939939/590295810358705651712)), (151833/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455756678828183/18446744073709551616), (-610452473747/18446744073709551616)), (94917/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911076720616597/4611686018427387904), (-1372465244419/4611686018427387904)), (53405/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796701244779365/576460752303423488), (-2742300811587/1152921504606846976)), (213693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597035461179671/72057594037927936), (-599139521957/36028797018963968)), (187063/144115188075855872), by norm_num⟩
  | 4 => ⟨((46589808065081/1125899906842624), (-3588935039239/36028797018963968)), (280757/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488305379014517/9007199254740992), (-2237929226837/4503599627370496)), (351233/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226049849764453/4503599627370496), (-8920859008623/4503599627370496)), (351663/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213272279454839/2251799813685248), (-13304399169205/2251799813685248)), (1057149/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175133418358717/2251799813685248), (-26302768768991/2251799813685248)), (2122987/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175133418358717/2251799813685248), (-26302768768991/2251799813685248)), (8098552712447356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1050385012749891/1125899906842624), (-50814491587653/2251799813685248)), (2075505/1125899906842624), by norm_num⟩
  | 2 => ⟨((1958723222498479/2251799813685248), (-94812656204681/2251799813685248)), (7932543/2251799813685248), by norm_num⟩
  | 3 => ⟨((1699799067091163/2251799813685248), (-164945169962459/2251799813685248)), (1808527/281474976710656), by norm_num⟩
  | 4 => ⟨((1271032150369519/2251799813685248), (-249021821850609/2251799813685248)), (11981315/1125899906842624), by norm_num⟩
  | 5 => ⟨((344948705047791/1125899906842624), (-281121563108857/2251799813685248)), (64702895/4503599627370496), by norm_num⟩
  | 6 => ⟨((705087727247333/9007199254740992), (-689031190542345/9007199254740992)), (55802243/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1067127145/16777216)), (1/16777216), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1097959187/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-797946053313957/9007199254740992), (-467507022290859/9007199254740992)), (334283985/9007199254740992), by norm_num⟩
  | 1 => ⟨((502067895/2147483648), (147077779/1073741824)), (211/2147483648), by norm_num⟩
  | 2 => ⟨((-662492979/2147483648), (-776293381/4294967296)), (559/4294967296), by norm_num⟩
  | 3 => ⟨((1165571301/4294967296), (341447123/2147483648)), (247/2147483648), by norm_num⟩
  | 4 => ⟨((-769002371/4294967296), (-225274633/2147483648)), (41/536870912), by norm_num⟩
  | 5 => ⟨((811776537/8589934592), (475610137/8589934592)), (87/2147483648), by norm_num⟩
  | 6 => ⟨((-714108273/17179869184), (-418387473/17179869184)), (77/4294967296), by norm_num⟩
  | 7 => ⟨((1076898669/68719476736), (630942015/68719476736)), (467/68719476736), by norm_num⟩
  | 8 => ⟨((-710499331/137438953472), (-416273037/137438953472)), (155/68719476736), by norm_num⟩
  | 9 => ⟨((416677437/274877906944), (244126313/274877906944)), (365/549755813888), by norm_num⟩
  | 10 => ⟨((-879708515/2199023255552), (-128852667/549755813888)), (387/2199023255552), by norm_num⟩
  | 11 => ⟨((211054655/2199023255552), (123654391/2199023255552)), (373/8796093022208), by norm_num⟩
  | 12 => ⟨((-92830889/4398046511104), (-108777009/8796093022208)), (165/17592186044416), by norm_num⟩
  | 13 => ⟨((603042555/140737488355328), (706630801/281474976710656)), (269/140737488355328), by norm_num⟩
  | 14 => ⟨((-113675991/140737488355328), (-266405599/562949953421312)), (51/140737488355328), by norm_num⟩
  | 15 => ⟨((1279989151/9007199254740992), (187482573/2251799813685248)), (577/9007199254740992), by norm_num⟩
  | 16 => ⟨((-844491187/36028797018963968), (-247388629/18014398509481984)), (383/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-850479786311/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778449729601391/633825300114114700748351602688), (-2012327574579/316912650057057350374175801344)), (23149/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889382562535999/39614081257132168796771975168), (-4526820101839/39614081257132168796771975168)), (26049/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889134696005699/2475880078570760549798248448), (-4808627470655/2475880078570760549798248448)), (55369/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885400200558933/77371252455336267181195264), (-4807368898375/154742504910672534362390528)), (110771/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549186954017931/9671406556917033397649408), (-1126392843315/2417851639229258349412352)), (103883/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258467443705237/604462909807314587353088), (-3941038279281/604462909807314587353088)), (90933/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471817237099067/18889465931478580854784), (-6401681573759/75557863725914323419136)), (18479/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297146185066787/4722366482869645213696), (-4799069384715/4722366482869645213696)), (221865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620905835358043/590295810358705651712), (-3297579959541/295147905179352825856)), (76313/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822794468843517/73786976294838206464), (-1029826405303/9223372036854775808)), (381847/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910944277065917/4611686018427387904), (-9261100361795/9223372036854775808)), (429967/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593133099227743/1152921504606846976), (-9251933806813/1152921504606846976)), (430453/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596915076057127/72057594037927936), (-4042568328833/72057594037927936)), (377195/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490502626327069/36028797018963968), (-756694470587/2251799813685248)), (70861/4503599627370496), by norm_num⟩
  | 3 => ⟨((1487823775315179/9007199254740992), (-943618126281/562949953421312)), (177633/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112517114203489/2251799813685248), (-3760992332839/562949953421312)), (178355/562949953421312), by norm_num⟩
  | 1 => ⟨((1105809391421415/1125899906842624), (-22431427024699/1125899906842624)), (1077367/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085655982894761/1125899906842624), (-11081599375131/281474976710656)), (1091897/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085655982894761/1125899906842624), (-11081599375131/281474976710656)), (4165256502391624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((261276352482257/281474976710656), (-85484008576869/1125899906842624)), (2191713/562949953421312), by norm_num⟩
  | 2 => ⟨((481809171289061/562949953421312), (-317398728903503/2251799813685248)), (17606735/2251799813685248), by norm_num⟩
  | 3 => ⟨((1604716043380735/2251799813685248), (-271650468415171/1125899906842624)), (35101435/2251799813685248), by norm_num⟩
  | 4 => ⟨((1012495719231585/2251799813685248), (-193588196521029/562949953421312)), (66967303/2251799813685248), by norm_num⟩
  | 5 => ⟨((47242803463249/562949953421312), (-696357532601527/2251799813685248)), (53139905/1125899906842624), by norm_num⟩
  | 6 => ⟨((-797946053313957/9007199254740992), (-467507022290859/9007199254740992)), (334283985/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1097959187/16777216)), (1/8388608), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1126663133/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-165599765962367/4503599627370496), (201497846056837/2251799813685248)), (153823143/9007199254740992), by norm_num⟩
  | 1 => ⟨((106919403/1073741824), (-520387919/2147483648)), (201/4294967296), by norm_num⟩
  | 2 => ⟨((-289543111/2147483648), (11009661/33554432)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((31905/262144), (-1272094493/4294967296)), (125/2147483648), by norm_num⟩
  | 4 => ⟨((-353895799/4294967296), (861223937/4294967296)), (171/4294967296), by norm_num⟩
  | 5 => ⟨((95836759/2147483648), (-466447531/4294967296)), (187/8589934592), by norm_num⟩
  | 6 => ⟨((-173020503/8589934592), (842108887/17179869184)), (171/17179869184), by norm_num⟩
  | 7 => ⟨((267741833/34359738368), (-1303127509/68719476736)), (267/68719476736), by norm_num⟩
  | 8 => ⟨((-181264581/68719476736), (441116839/68719476736)), (91/68719476736), by norm_num⟩
  | 9 => ⟨((109083019/137438953472), (-8295601/4294967296)), (221/549755813888), by norm_num⟩
  | 10 => ⟨((-236321833/1099511627776), (575101541/1099511627776)), (121/1099511627776), by norm_num⟩
  | 11 => ⟨((58179217/1099511627776), (-1132657341/8796093022208)), (15/549755813888), by norm_num⟩
  | 12 => ⟨((-420139307/35184372088832), (255607745/8796093022208)), (219/35184372088832), by norm_num⟩
  | 13 => ⟨((683749/274877906944), (-851936745/140737488355328)), (23/17592186044416), by norm_num⟩
  | 14 => ⟨((-135433261/281474976710656), (1318335699/1125899906842624)), (287/1125899906842624), by norm_num⟩
  | 15 => ⟨((391210741/4503599627370496), (-952031801/4503599627370496)), (209/4503599627370496), by norm_num⟩
  | 16 => ⟨((-529709163/36028797018963968), (1289074955/36028797018963968)), (285/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (319250992401/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889180908628063/316912650057057350374175801344), (3021233296499/633825300114114700748351602688)), (92497/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889283894019957/39614081257132168796771975168), (3398189762863/39614081257132168796771975168)), (104079/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889030164485327/2475880078570760549798248448), (451214458417/309485009821345068724781056)), (110607/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442674052770663/38685626227668133590597632), (3608747363909/154742504910672534362390528)), (110631/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774544819226119/4835703278458516698824704), (422771514185/1208925819614629174706176)), (103743/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258382654912599/604462909807314587353088), (1479186188219/302231454903657293676544)), (45401/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887131845409165/75557863725914323419136), (4805427868049/75557863725914323419136)), (147603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324260987803679/1180591620717411303424), (3602385236885/4722366482869645213696)), (110745/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405191556753285/147573952589676412928), (1237635440005/147573952589676412928)), (152345/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822621401371201/73786976294838206464), (1546018124897/18446744073709551616)), (95269/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910847917149981/4611686018427387904), (1737860297511/2305843009213693952)), (214501/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398235712812989/288230376151711744), (3472198054867/576460752303423488)), (53671/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193666459810075/144115188075855872), (6068428281383/144115188075855872)), (94027/72057594037927936), by norm_num⟩
  | 4 => ⟨((46570706932187/1125899906842624), (1135853035615/4503599627370496)), (70623/9007199254740992), by norm_num⟩
  | 3 => ⟨((743766709772891/4503599627370496), (5665445098369/4503599627370496)), (88459/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112241164186535/2251799813685248), (22579026104241/4503599627370496)), (709841/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105431239762821/1125899906842624), (33662234493119/2251799813685248)), (1070197/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085041331560795/1125899906842624), (66502731867325/2251799813685248)), (2162221/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085041331560795/1125899906842624), (66502731867325/2251799813685248)), (8248218544966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((522341742241203/562949953421312), (64089367357803/1125899906842624)), (4295225/2251799813685248), by norm_num⟩
  | 2 => ⟨((965677436452575/1125899906842624), (237865207032053/2251799813685248)), (4229887/1125899906842624), by norm_num⟩
  | 3 => ⟨((407846177761025/562949953421312), (102007763723921/562949953421312)), (8149531/1125899906842624), by norm_num⟩
  | 4 => ⟨((553985020894467/1125899906842624), (591220960711083/2251799813685248)), (29523553/2251799813685248), by norm_num⟩
  | 5 => ⟨((779869847915681/4503599627370496), (1163611629354393/4503599627370496)), (22278249/1125899906842624), by norm_num⟩
  | 6 => ⟨((-165599765962367/4503599627370496), (201497846056837/2251799813685248)), (153823143/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1126663133/16777216)), (1/16777216), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile031Terms1
