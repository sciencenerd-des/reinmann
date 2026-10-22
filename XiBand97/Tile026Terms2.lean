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
namespace Reinmann.XiBand97.Tile026Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30041/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30041/1280))
  have he : value ((69/80), (30041/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-1091716223/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-510986052621849/9007199254740992), (-646691875350781/9007199254740992)), (75041599/4503599627370496), by norm_num⟩
  | 1 => ⟨((675561031/4294967296), (854974079/4294967296)), (201/4294967296), by norm_num⟩
  | 2 => ⟨((-58532903/268435456), (-1185245745/4294967296)), (281/4294967296), by norm_num⟩
  | 3 => ⟨((865534223/4294967296), (547699831/2147483648)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-299971303/2147483648), (-759273187/4294967296)), (23/536870912), by norm_num⟩
  | 5 => ⟨((665357641/8589934592), (421030455/4294967296)), (103/4294967296), by norm_num⟩
  | 6 => ⟨((-614921031/17179869184), (-97278691/2147483648)), (193/17179869184), by norm_num⟩
  | 7 => ⟨((243560445/17179869184), (616488689/34359738368)), (155/34359738368), by norm_num⟩
  | 8 => ⟨((-675292943/137438953472), (-854634793/137438953472)), (217/137438953472), by norm_num⟩
  | 9 => ⟨((832137599/549755813888), (263283421/137438953472)), (269/549755813888), by norm_num⟩
  | 10 => ⟨((-922870129/2199023255552), (-583981315/1099511627776)), (75/549755813888), by norm_num⟩
  | 11 => ⟨((930450659/8796093022208), (588778185/4398046511104)), (305/8796093022208), by norm_num⟩
  | 12 => ⟨((-859919001/35184372088832), (-544146585/17592186044416)), (71/8796093022208), by norm_num⟩
  | 13 => ⟨((733600531/140737488355328), (464213749/70368744177664)), (245/140737488355328), by norm_num⟩
  | 14 => ⟨((-581135017/562949953421312), (-367735373/281474976710656)), (49/140737488355328), by norm_num⟩
  | 15 => ⟨((859332477/4503599627370496), (543775439/2251799813685248)), (73/1125899906842624), by norm_num⟩
  | 16 => ⟨((-148910971/4503599627370496), (-753832825/18014398509481984)), (51/4503599627370496), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-1458602388911/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778274557561801/633825300114114700748351602688), (-3450555516749/633825300114114700748351602688)), (92541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889185664750715/39614081257132168796771975168), (-485132144923/4951760157141521099596496896)), (52065/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888925711382145/2475880078570760549798248448), (-2061308096687/1237940039285380274899124224)), (110663/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770591663028025/154742504910672534362390528), (-1030370888959/38685626227668133590597632)), (110691/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387247880964399/2417851639229258349412352), (-3862687719343/9671406556917033397649408)), (103803/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258296703952909/604462909807314587353088), (-3378648992163/604462909807314587353088)), (45429/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886991986528053/75557863725914323419136), (-2744025090471/37778931862957161709568)), (147701/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296938892274531/4722366482869645213696), (-4114065756143/4722366482869645213696)), (55413/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405155375904409/147573952589676412928), (-5653637512451/590295810358705651712)), (76233/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822440096821003/73786976294838206464), (-882780623807/9223372036854775808)), (190703/73786976294838206464), by norm_num⟩
  | 7 => ⟨((7115200458729/36028797018963968), (-7938426987557/9223372036854775808)), (53677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592737649587703/1152921504606846976), (-1982546170507/288230376151711744)), (53729/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193486140370241/144115188075855872), (-1732411805217/36028797018963968)), (188287/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489990612730397/36028797018963968), (-5187981309401/18014398509481984)), (282901/36028797018963968), by norm_num⟩
  | 3 => ⟨((743595372154637/4503599627370496), (-6468805050307/4503599627370496)), (354449/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223789040300203/4503599627370496), (-25778375405679/4503599627370496)), (44461/281474976710656), by norm_num⟩
  | 1 => ⟨((2209802891718963/2251799813685248), (-38426097319841/2251799813685248)), (536637/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167885989344299/2251799813685248), (-75890206011315/2251799813685248)), (2171487/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2167885989344299/2251799813685248), (-75890206011315/2251799813685248)), (8283565529830168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084541579095709/2251799813685248), (-36531070244457/562949953421312)), (1081875/562949953421312), by norm_num⟩
  | 2 => ⟨((960112276235391/1125899906842624), (-270541046821779/2251799813685248)), (8573771/2251799813685248), by norm_num⟩
  | 3 => ⟨((1604969434641475/2251799813685248), (-461408298731605/2251799813685248)), (16682765/2251799813685248), by norm_num⟩
  | 4 => ⟨((1049395800476463/2251799813685248), (-657737168156335/2251799813685248)), (15309041/1125899906842624), by norm_num⟩
  | 5 => ⟨((296923980373319/2251799813685248), (-613044390434449/2251799813685248)), (92848641/4503599627370496), by norm_num⟩
  | 6 => ⟨((-510986052621849/9007199254740992), (-646691875350781/9007199254740992)), (75041599/4503599627370496), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1091716223/16777216)), (1/16777216), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-557793687/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1357068611451215/18014398509481984), (389172931066509/9007199254740992)), (283249153/9007199254740992), by norm_num⟩
  | 1 => ⟨((458343613/2147483648), (-525765391/4294967296)), (3/33554432), by norm_num⟩
  | 2 => ⟨((-1298585241/4294967296), (744802761/4294967296)), (273/2147483648), by norm_num⟩
  | 3 => ⟨((613194839/2147483648), (-21981095/134217728)), (259/2147483648), by norm_num⟩
  | 4 => ⟨((-217163975/1073741824), (498217053/4294967296)), (369/4294967296), by norm_num⟩
  | 5 => ⟨((984434995/8589934592), (-564622081/8589934592)), (105/2147483648), by norm_num⟩
  | 6 => ⟨((-232426197/4294967296), (533231605/17179869184)), (199/8589934592), by norm_num⟩
  | 7 => ⟨((752586289/34359738368), (-53955675/4294967296)), (81/8589934592), by norm_num⟩
  | 8 => ⟨((-533059379/68719476736), (305735877/68719476736)), (461/137438953472), by norm_num⟩
  | 9 => ⟨((1342463063/549755813888), (-769968859/549755813888)), (583/549755813888), by norm_num⟩
  | 10 => ⟨((-760696853/1099511627776), (436297209/1099511627776)), (83/274877906944), by norm_num⟩
  | 11 => ⟨((391857541/2199023255552), (-112374825/1099511627776)), (43/549755813888), by norm_num⟩
  | 12 => ⟨((-740144009/17592186044416), (212254569/8796093022208)), (327/17592186044416), by norm_num⟩
  | 13 => ⟨((1290452851/140737488355328), (-370069217/70368744177664)), (143/35184372088832), by norm_num⟩
  | 14 => ⟨((-261152017/140737488355328), (599134311/562949953421312)), (465/562949953421312), by norm_num⟩
  | 15 => ⟨((789226005/2251799813685248), (-452660087/2251799813685248)), (353/2251799813685248), by norm_num⟩
  | 16 => ⟨((-139752853/2251799813685248), (641241299/18014398509481984)), (503/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (106685898405/316912650057057350374175801344)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444547909634239/158456325028528675187087900672), (4037770225563/633825300114114700748351602688)), (185195/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889092270305565/39614081257132168796771975168), (1135377273905/9903520314283042199192993792)), (52099/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944413165346505/1237940039285380274899124224), (2412074311627/1237940039285380274899124224)), (27685/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885246057398873/77371252455336267181195264), (4822793487785/154742504910672534362390528)), (221547/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387224504883229/2417851639229258349412352), (141247793691/302231454903657293676544)), (207771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258214709982853/604462909807314587353088), (988374775685/151115727451828646838272)), (90935/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886858413532595/75557863725914323419136), (6421738490071/75557863725914323419136)), (295671/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648419210849957/2361183241434822606848), (2406972154509/2361183241434822606848)), (110935/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620482884669309/590295810358705651712), (3307670320649/295147905179352825856)), (76315/147573952589676412928), by norm_num⟩
  | 8 => ⟨((113891632279691/4611686018427387904), (8263429249925/73786976294838206464)), (381859/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227661827479785/1152921504606846976), (9288460661897/9223372036854775808)), (214991/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796269871390403/576460752303423488), (9278595504415/1152921504606846976)), (215235/576460752303423488), by norm_num⟩
  | 5 => ⟨((74581975972921/9007199254740992), (506730097717/9007199254740992)), (377211/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489726122850437/36028797018963968), (12139365344233/36028797018963968)), (283459/18014398509481984), by norm_num⟩
  | 3 => ⟨((743427712390385/4503599627370496), (15135481457401/9007199254740992)), (710577/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111552184749783/2251799813685248), (7538746362553/1125899906842624)), (713477/2251799813685248), by norm_num⟩
  | 1 => ⟨((552185279864125/562949953421312), (2808951788831/140737488355328)), (538743/562949953421312), by norm_num⟩
  | 0 => ⟨((1082812626283777/1125899906842624), (44366813375783/1125899906842624)), (2184173/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082812626283777/1125899906842624), (44366813375783/1125899906842624)), (8331958775046920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039625958219447/1125899906842624), (170675724970955/2251799813685248)), (4373311/1125899906842624), by norm_num⟩
  | 2 => ⟨((1906989379261349/2251799813685248), (78798707167195/562949953421312)), (17478701/2251799813685248), by norm_num⟩
  | 3 => ⟨((785429657445223/1125899906842624), (533860236612917/2251799813685248)), (34497645/2251799813685248), by norm_num⟩
  | 4 => ⟨((484632830520067/1125899906842624), (744843587281901/2251799813685248)), (64488743/2251799813685248), by norm_num⟩
  | 5 => ⟨((341667984710445/4503599627370496), (641221575391079/2251799813685248)), (196359823/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1357068611451215/18014398509481984), (389172931066509/9007199254740992)), (283249153/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-557793687/8388608)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1138093693/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((213936008444909/9007199254740992), (1426388038826645/18014398509481984)), (435604673/18014398509481984), by norm_num⟩
  | 1 => ⟨((-294854449/4294967296), (-245737535/1073741824)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((213059743/2147483648), (710272831/2147483648)), (439/4294967296), by norm_num⟩
  | 3 => ⟨((-410547909/4294967296), (-1368635021/4294967296)), (425/4294967296), by norm_num⟩
  | 4 => ⟨((74164755/1073741824), (988966003/4294967296)), (309/4294967296), by norm_num⟩
  | 5 => ⟨((-342981941/8589934592), (-571695881/4294967296)), (359/8589934592), by norm_num⟩
  | 6 => ⟨((330448439/17179869184), (550804543/8589934592)), (87/4294967296), by norm_num⟩
  | 7 => ⟨((-34111387/4294967296), (-909731369/34359738368)), (289/34359738368), by norm_num⟩
  | 8 => ⟨((394378359/137438953472), (82170683/8589934592)), (105/34359738368), by norm_num⟩
  | 9 => ⟨((-253311127/274877906944), (-52778627/17179869184)), (271/274877906944), by norm_num⟩
  | 10 => ⟨((292865331/1099511627776), (976319059/1099511627776)), (315/1099511627776), by norm_num⟩
  | 11 => ⟨((-153907215/2199023255552), (-513077279/2199023255552)), (333/4398046511104), by norm_num⟩
  | 12 => ⟨((296566045/17592186044416), (988656051/17592186044416)), (323/17592186044416), by norm_num⟩
  | 13 => ⟨((-32968697/8796093022208), (-439628235/35184372088832)), (289/70368744177664), by norm_num⟩
  | 14 => ⟨((435619615/562949953421312), (181527005/70368744177664)), (15/17592186044416), by norm_num⟩
  | 15 => ⟨((-167880351/1125899906842624), (-1119318461/2251799813685248)), (93/562949953421312), by norm_num⟩
  | 16 => ⟨((485236625/18014398509481984), (808811617/9007199254740992)), (135/4503599627370496), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (1666519774983/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778122345238149/633825300114114700748351602688), (985438945245/316912650057057350374175801344)), (46197/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944507351101317/19807040628566084398385987584), (138547344425/2475880078570760549798248448)), (25989/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888744425648151/2475880078570760549798248448), (588676481707/618970019642690137449562112)), (220935/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770410784158311/154742504910672534362390528), (588508102531/38685626227668133590597632)), (27621/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548822381918851/9671406556917033397649408), (2206190021987/9671406556917033397649408)), (25899/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629074568214967/302231454903657293676544), (1929701186885/604462909807314587353088)), (11333/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943376498996949/37778931862957161709568), (3134424244353/75557863725914323419136)), (147361/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296760357781707/4722366482869645213696), (2349646116773/4722366482869645213696)), (221099/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620377166110077/590295810358705651712), (807214979295/147573952589676412928)), (304103/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911068196892327/36893488147419103232), (4033221605899/73786976294838206464)), (380267/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455288002807537/2305843009213693952), (283340887365/576460752303423488)), (427991/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796200643735809/576460752303423488), (4528558806629/1152921504606846976)), (214115/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193195127995721/144115188075855872), (1978494079273/72057594037927936)), (187485/72057594037927936), by norm_num⟩
  | 4 => ⟨((372390171024239/9007199254740992), (5924496919303/36028797018963968)), (562993/36028797018963968), by norm_num⟩
  | 3 => ⟨((743332411583519/4503599627370496), (3693216705735/4503599627370496)), (704687/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222771496478655/4503599627370496), (7357724816523/2251799813685248)), (353053/1125899906842624), by norm_num⟩
  | 1 => ⟨((552090431826409/562949953421312), (5482535351433/562949953421312)), (1062721/1125899906842624), by norm_num⟩
  | 0 => ⟨((2165340711633407/2251799813685248), (21645600519497/1125899906842624)), (2139761/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165340711633407/2251799813685248), (21645600519497/1125899906842624)), (8162540440085982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1040684487334447/1125899906842624), (83258022756319/2251799813685248)), (8394965/2251799813685248), by norm_num⟩
  | 2 => ⟨((480189766878353/562949953421312), (153913029394629/2251799813685248)), (16139951/2251799813685248), by norm_num⟩
  | 3 => ⟨((813932515790219/1125899906842624), (65643012540793/562949953421312)), (14870375/1125899906842624), by norm_num⟩
  | 4 => ⟨((573097231785333/1125899906842624), (189817876408599/1125899906842624)), (6242009/281474976710656), by norm_num⟩
  | 5 => ⟨((1038847624370979/4503599627370496), (772957516752645/4503599627370496)), (135347679/4503599627370496), by norm_num⟩
  | 6 => ⟨((213936008444909/9007199254740992), (1426388038826645/18014398509481984)), (435604673/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1138093693/16777216)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1159382845/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((710626079624351/9007199254740992), (14832362233135/18014398509481984)), (44546017/9007199254740992), by norm_num⟩
  | 1 => ⟨((-997731747/4294967296), (-10412451/4294967296)), (127/8589934592), by norm_num⟩
  | 2 => ⟨((1468880123/4294967296), (15329413/4294967296)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((-1441675963/4294967296), (-15045507/4294967296)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((1061231725/4294967296), (22150289/8589934592)), (71/4294967296), by norm_num⟩
  | 5 => ⟨((-1249892823/8589934592), (-13044035/8589934592)), (85/8589934592), by norm_num⟩
  | 6 => ⟨((1226744383/17179869184), (12802455/17179869184)), (85/17179869184), by norm_num⟩
  | 7 => ⟨((-2064042273/68719476736), (-21540599/68719476736)), (73/34359738368), by norm_num⟩
  | 8 => ⟨((1519361631/137438953472), (15856245/137438953472)), (109/137438953472), by norm_num⟩
  | 9 => ⟨((-1988296715/549755813888), (-20750109/549755813888)), (145/549755813888), by norm_num⟩
  | 10 => ⟨((585441835/549755813888), (6109743/549755813888)), (87/1099511627776), by norm_num⟩
  | 11 => ⟨((-1253671097/4398046511104), (-6541733/2199023255552)), (95/4398046511104), by norm_num⟩
  | 12 => ⟨((615226341/8796093022208), (3210289/4398046511104)), (95/17592186044416), by norm_num⟩
  | 13 => ⟨((-1114767027/70368744177664), (-5816923/35184372088832)), (11/8796093022208), by norm_num⟩
  | 14 => ⟨((937818139/281474976710656), (19574371/562949953421312)), (75/281474976710656), by norm_num⟩
  | 15 => ⟨((-1472719085/2251799813685248), (-7684739/1125899906842624)), (15/281474976710656), by norm_num⟩
  | 16 => ⟨((542041435/4503599627370496), (11313623/9007199254740992)), (45/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (6796860903/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889026295760403/316912650057057350374175801344), (16075118229/633825300114114700748351602688)), (46101/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888936361746661/39614081257132168796771975168), (18080544687/39614081257132168796771975168)), (6483/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888661363628767/2475880078570760549798248448), (9602802475/1237940039285380274899124224)), (110211/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770327918495991/154742504910672534362390528), (19200012187/154742504910672534362390528)), (110211/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548744903840493/9671406556917033397649408), (17994071421/9671406556917033397649408)), (103323/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258081551423307/604462909807314587353088), (15738875083/604462909807314587353088)), (11301/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886643562585985/75557863725914323419136), (12782272439/37778931862957161709568)), (146913/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324169655579603/1180591620717411303424), (9581838963/2361183241434822606848)), (55093/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202533166681915/73786976294838206464), (13167127515/295147905179352825856)), (151505/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455499358052217/18446744073709551616), (32894133657/73786976294838206464)), (94691/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227624602221241/1152921504606846976), (36973362613/9223372036854775808)), (3329/144115188075855872), by norm_num⟩
  | 6 => ⟨((398061878515471/288230376151711744), (18466367167/576460752303423488)), (106529/576460752303423488), by norm_num⟩
  | 5 => ⟨((37283192810007/4503599627370496), (1008453001/4503599627370496)), (46607/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489364424572223/36028797018963968), (48314601569/36028797018963968)), (279647/36028797018963968), by norm_num⟩
  | 3 => ⟨((743212518853685/4503599627370496), (60234090745/9007199254740992)), (2731/70368744177664), by norm_num⟩
  | 2 => ⟨((1111154227664669/2251799813685248), (119992047359/4503599627370496)), (174791/1125899906842624), by norm_num⟩
  | 1 => ⟨((2207708186459525/2251799813685248), (178802445655/2251799813685248)), (262207/562949953421312), by norm_num⟩
  | 0 => ⟨((33815560963831/35184372088832), (352890542885/2251799813685248)), (2098045/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((33815560963831/35184372088832), (352890542885/2251799813685248)), (8003406533248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2080000072774629/2251799813685248), (169580853061/562949953421312)), (126047/70368744177664), by norm_num⟩
  | 2 => ⟨((1921307487604467/2251799813685248), (156642781727/281474976710656)), (7453971/2251799813685248), by norm_num⟩
  | 3 => ⟨((204915023369583/281474976710656), (1069220976331/1125899906842624)), (6364115/1125899906842624), by norm_num⟩
  | 4 => ⟨((4661837066429/8796093022208), (3113590329237/2251799813685248)), (18556591/2251799813685248), by norm_num⟩
  | 5 => ⟨((39531327108205/140737488355328), (1650170225561/1125899906842624)), (19720915/2251799813685248), by norm_num⟩
  | 6 => ⟨((710626079624351/9007199254740992), (14832362233135/18014398509481984)), (44546017/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1159382845/16777216)), (1/16777216), by norm_num⟩, -11, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-589789877/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((250551575745785/9007199254740992), (-1264122537630385/18014398509481984)), (96072537/9007199254740992), by norm_num⟩
  | 1 => ⟨((-357907029/4294967296), (451442323/2147483648)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((536096819/4294967296), (-1352400337/4294967296)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((-535334181/4294967296), (675238223/2147483648)), (53/1073741824), by norm_num⟩
  | 4 => ⟨((400929471/4294967296), (-1011416469/4294967296)), (161/4294967296), by norm_num⟩
  | 5 => ⟨((-240215471/4294967296), (1211973183/8589934592)), (195/8589934592), by norm_num⟩
  | 6 => ⟨((479747493/17179869184), (-302562265/4294967296)), (197/17179869184), by norm_num⟩
  | 7 => ⟨((-410627157/34359738368), (258970155/8589934592)), (171/34359738368), by norm_num⟩
  | 8 => ⟨((307532257/68719476736), (-775805251/68719476736)), (65/34359738368), by norm_num⟩
  | 9 => ⟨((-102364923/68719476736), (1032935479/274877906944)), (175/274877906944), by norm_num⟩
  | 10 => ⟨((245326323/549755813888), (-1237759261/1099511627776)), (53/274877906944), by norm_num⟩
  | 11 => ⟨((-133623997/1099511627776), (1348361951/4398046511104)), (233/4398046511104), by norm_num⟩
  | 12 => ⟨((533735627/17592186044416), (-1346443805/17592186044416)), (235/17592186044416), by norm_num⟩
  | 13 => ⟨((-491978167/70368744177664), (1241103127/70368744177664)), (219/70368744177664), by norm_num⟩
  | 14 => ⟨((210547839/140737488355328), (-1062289341/281474976710656)), (189/281474976710656), by norm_num⟩
  | 15 => ⟨((-168198655/562949953421312), (848622523/1125899906842624)), (153/1125899906842624), by norm_num⟩
  | 16 => ⟨((503878139/9007199254740992), (-317780735/2251799813685248)), (231/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1554528722889/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888991317434707/316912650057057350374175801344), (-459539473889/158456325028528675187087900672)), (46191/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944428788972003/19807040628566084398385987584), (-258433112909/4951760157141521099596496896)), (103941/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888577544303151/2475880078570760549798248448), (-2196102585421/2475880078570760549798248448)), (110451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770243973851283/154742504910672534362390528), (-1097725820581/77371252455336267181195264)), (55233/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548666072700045/9671406556917033397649408), (-32149133425/151115727451828646838272)), (51789/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629006220634733/302231454903657293676544), (-224957547887/75557863725914323419136)), (90647/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886531009663553/75557863725914323419136), (-2923152938017/75557863725914323419136)), (147331/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648296995047711/2361183241434822606848), (-1095616011783/2361183241434822606848)), (110525/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620148611177489/590295810358705651712), (-3011104564033/590295810358705651712)), (152015/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821851000808337/73786976294838206464), (-117535109067/2305843009213693952)), (190083/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910415678575007/4611686018427387904), (-4227475983445/9223372036854775808)), (213933/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592081149020279/1152921504606846976), (-527843236471/144115188075855872)), (53511/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192915586048705/144115188075855872), (-922396986547/36028797018963968)), (93707/72057594037927936), by norm_num⟩
  | 4 => ⟨((744571263681993/18014398509481984), (-2761884545241/18014398509481984)), (281373/36028797018963968), by norm_num⟩
  | 3 => ⟨((743072072809303/4503599627370496), (-3443088091085/4503599627370496)), (352157/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221736176684025/4503599627370496), (-13716895616169/4503599627370496)), (88205/562949953421312), by norm_num⟩
  | 1 => ⟨((1103411883374037/1125899906842624), (-10218610531281/1125899906842624)), (265447/562949953421312), by norm_num⟩
  | 0 => ⟨((33786319590425/35184372088832), (-40325059572285/2251799813685248)), (2136965/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((33786319590425/35184372088832), (-40325059572285/2251799813685248)), (8151874550826262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((518920565741499/562949953421312), (-77445483282881/2251799813685248)), (4180643/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910675641663459/2251799813685248), (-71388324583801/1125899906842624)), (3997451/1125899906842624), by norm_num⟩
  | 3 => ⟨((806087693505329/1125899906842624), (-242294953667669/2251799813685248)), (14581359/2251799813685248), by norm_num⟩
  | 4 => ⟨((1128165398394175/2251799813685248), (-346941995754605/2251799813685248)), (24016965/2251799813685248), by norm_num⟩
  | 5 => ⟨((511763261863729/2251799813685248), (-695280197611517/4503599627370496)), (31466033/2251799813685248), by norm_num⟩
  | 6 => ⟨((250551575745785/9007199254740992), (-1264122537630385/18014398509481984)), (96072537/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-589789877/8388608)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-1198791047/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-905435777386709/18014398509481984), (-117262959819093/2251799813685248)), (239197059/9007199254740992), by norm_num⟩
  | 1 => ⟨((328614657/2147483648), (680941987/4294967296)), (349/4294967296), by norm_num⟩
  | 2 => ⟨((-1000474697/4294967296), (-1036571579/4294967296)), (267/2147483648), by norm_num⟩
  | 3 => ⟨((1015322555/4294967296), (131494393/536870912)), (17/134217728), by norm_num⟩
  | 4 => ⟨((-772793075/4294967296), (-200168815/1073741824)), (13/134217728), by norm_num⟩
  | 5 => ⟨((941114343/8589934592), (487534759/4294967296)), (509/8589934592), by norm_num⟩
  | 6 => ⟨((-955081245/17179869184), (-494770171/8589934592)), (519/17179869184), by norm_num⟩
  | 7 => ⟨((415395183/17179869184), (430382539/17179869184)), (227/17179869184), by norm_num⟩
  | 8 => ⟨((-316169989/34359738368), (-81894331/8589934592)), (87/17179869184), by norm_num⟩
  | 9 => ⟨((213908139/68719476736), (886503567/274877906944)), (473/274877906944), by norm_num⟩
  | 10 => ⟨((-520998503/549755813888), (-1079592001/1099511627776)), (579/1099511627776), by norm_num⟩
  | 11 => ⟨((576796957/2199023255552), (597607649/2199023255552)), (161/1099511627776), by norm_num⟩
  | 12 => ⟨((-585357093/8796093022208), (-75809579/1099511627776)), (329/8796093022208), by norm_num⟩
  | 13 => ⟨((548348555/35184372088832), (568132835/35184372088832)), (155/17592186044416), by norm_num⟩
  | 14 => ⟨((-476988423/140737488355328), (-494198047/140737488355328)), (271/140737488355328), by norm_num⟩
  | 15 => ⟨((387253855/562949953421312), (200612939/281474976710656)), (221/562949953421312), by norm_num⟩
  | 16 => ⟨((-589501525/4503599627370496), (-305385297/2251799813685248)), (169/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-95191445661/316912650057057350374175801344)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888956337608257/316912650057057350374175801344), (-225103264395/39614081257132168796771975168)), (185109/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888778607960979/39614081257132168796771975168), (-4050926547353/39614081257132168796771975168)), (104147/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888493282238825/2475880078570760549798248448), (-2151477721167/1237940039285380274899124224)), (221365/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770159311232843/154742504910672534362390528), (-2150828780627/77371252455336267181195264)), (13839/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774293138130801/4835703278458516698824704), (-2015712687203/4835703278458516698824704)), (207649/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78621387159489/37778931862957161709568), (-3526119073529/604462909807314587353088)), (45439/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943208031516155/37778931862957161709568), (-5727360480229/75557863725914323419136)), (18467/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648253542359665/2361183241434822606848), (-2146630600145/2361183241434822606848)), (55427/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620027987844717/590295810358705651712), (-2949782424105/295147905179352825856)), (305017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910849265879411/36893488147419103232), (-7368955313341/73786976294838206464)), (95381/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820657510387561/9223372036854775808), (-8282516409459/9223372036854775808)), (429563/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24873506408731/18014398509481984), (-2068269080739/288230376151711744)), (429999/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596378847602177/72057594037927936), (-7228332421575/144115188075855872)), (376741/144115188075855872), by norm_num⟩
  | 4 => ⟨((372224806387383/9007199254740992), (-10821306739365/36028797018963968)), (283047/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485828755570327/9007199254740992), (-3372401986099/2251799813685248)), (709341/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221071815357649/4503599627370496), (-6717095154655/1125899906842624)), (1423861/4503599627370496), by norm_num⟩
  | 1 => ⟨((137858999616231/140737488355328), (-5003290763795/281474976710656)), (1074391/1125899906842624), by norm_num⟩
  | 0 => ⟨((67494884244485/70368744177664), (-39476363593821/1125899906842624)), (543719/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((67494884244485/70368744177664), (-39476363593821/1125899906842624)), (2074123383642101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2068860323778975/2251799813685248), (-9466037167123/140737488355328)), (8649239/2251799813685248), by norm_num⟩
  | 2 => ⟨((945298048557277/1125899906842624), (-278304081554067/2251799813685248)), (8528313/1125899906842624), by norm_num⟩
  | 3 => ⟨((1552935753597109/2251799813685248), (-467324499451011/2251799813685248)), (8214345/562949953421312), by norm_num⟩
  | 4 => ⟨((486992061568677/1125899906842624), (-322286607947463/1125899906842624)), (14739423/562949953421312), by norm_num⟩
  | 5 => ⟨((473550480139651/4503599627370496), (-1115204068613529/4503599627370496)), (21188919/562949953421312), by norm_num⟩
  | 6 => ⟨((-905435777386709/18014398509481984), (-117262959819093/2251799813685248)), (239197059/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1198791047/16777216)), (1/8388608), by norm_num⟩, -11, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile026Terms2
