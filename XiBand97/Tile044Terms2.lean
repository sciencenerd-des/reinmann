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
namespace Reinmann.XiBand97.Tile044Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨44,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36127/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36127/1280))
  have he : value ((69/80), (36127/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-328221697/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1581610760494265/18014398509481984), (-464516859504443/18014398509481984)), (36015729/1125899906842624), by norm_num⟩
  | 1 => ⟨((261375675/1073741824), (307062675/4294967296)), (383/4294967296), by norm_num⟩
  | 2 => ⟨((-724687249/2147483648), (-425679255/4294967296)), (533/4294967296), by norm_num⟩
  | 3 => ⟨((1339506463/4294967296), (393411167/4294967296)), (495/4294967296), by norm_num⟩
  | 4 => ⟨((-116059391/536870912), (-272691841/4294967296)), (345/4294967296), by norm_num⟩
  | 5 => ⟨((257427967/2147483648), (302424929/8589934592)), (385/8589934592), by norm_num⟩
  | 6 => ⟨((-475827919/8589934592), (-279499983/17179869184)), (179/8589934592), by norm_num⟩
  | 7 => ⟨((1507742997/68719476736), (27676375/4294967296)), (285/34359738368), by norm_num⟩
  | 8 => ⟨((-1045087807/137438953472), (-306940821/137438953472)), (397/137438953472), by norm_num⟩
  | 9 => ⟨((643910815/274877906944), (94557851/137438953472)), (491/549755813888), by norm_num⟩
  | 10 => ⟨((-1428239891/2199023255552), (-209736025/1099511627776)), (273/1099511627776), by norm_num⟩
  | 11 => ⟨((1439971569/8796093022208), (422917627/8796093022208)), (553/8796093022208), by norm_num⟩
  | 12 => ⟨((-1330816311/35184372088832), (-390858881/35184372088832)), (513/35184372088832), by norm_num⟩
  | 13 => ⟨((567662507/70368744177664), (166721681/70368744177664)), (439/140737488355328), by norm_num⟩
  | 14 => ⟨((-224842095/140737488355328), (-132071615/281474976710656)), (349/562949953421312), by norm_num⟩
  | 15 => ⟨((1329908601/4503599627370496), (12206009/140737488355328)), (259/2251799813685248), by norm_num⟩
  | 16 => ⟨((-921822397/18014398509481984), (-270737943/18014398509481984)), (361/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-930040927253/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778270562032249/633825300114114700748351602688), (-4400318930963/633825300114114700748351602688)), (185267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29518452313309/618970019642690137449562112), (-309331547421/2475880078570760549798248448)), (6515/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1888920406764811/2475880078570760549798248448), (-5257350792085/2475880078570760549798248448)), (221575/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770586028939523/154742504910672534362390528), (-656988095207/19342813113834066795298816)), (13853/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548985892094381/9671406556917033397649408), (-4925874605479/9671406556917033397649408)), (203/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1258291426644761/604462909807314587353088), (-1077151126667/151115727451828646838272)), (181965/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886982756176843/75557863725914323419136), (-6998603461825/75557863725914323419136)), (147919/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296931397241801/4722366482869645213696), (-5246434305955/4722366482869645213696)), (222005/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405152567290827/147573952589676412928), (-901219535881/73786976294838206464)), (305463/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822424662593579/73786976294838206464), (-9006061376641/73786976294838206464)), (191069/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821472044359501/9223372036854775808), (-1265423579187/1152921504606846976)), (430331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796357997229581/576460752303423488), (-632053520879/72057594037927936)), (430863/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193464519064237/144115188075855872), (-8836908326715/144115188075855872)), (377605/144115188075855872), by norm_num⟩
  | 4 => ⟨((372488212866675/9007199254740992), (-6615850128717/18014398509481984)), (283803/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487134254260037/9007199254740992), (-16498260792151/9007199254740992)), (355805/4503599627370496), by norm_num⟩
  | 2 => ⟨((138978021609431/281474976710656), (-4109075722793/562949953421312)), (357385/1125899906842624), by norm_num⟩
  | 1 => ⟨((276190386348325/281474976710656), (-24499871330349/1125899906842624)), (1080077/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083527251237913/1125899906842624), (-48383286016457/1125899906842624)), (2191969/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083527251237913/1125899906842624), (-48383286016457/1125899906842624)), (8361698154929732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((520335046964887/562949953421312), (-46562406289103/562949953421312)), (2203671/562949953421312), by norm_num⟩
  | 2 => ⟨((954189628361205/1125899906842624), (-172150662530431/1125899906842624)), (8876495/1125899906842624), by norm_num⟩
  | 3 => ⟨((782344852245867/1125899906842624), (-583584298049001/2251799813685248)), (35519869/2251799813685248), by norm_num⟩
  | 4 => ⟨((1828123796799/4398046511104), (-405510444272531/1125899906842624)), (67773709/2251799813685248), by norm_num⟩
  | 5 => ⟨((193924845176875/4503599627370496), (-1348459214614465/4503599627370496)), (210324285/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1581610760494265/18014398509481984), (-464516859504443/18014398509481984)), (36015729/1125899906842624), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-328221697/4194304)), (1/8388608), by norm_num⟩, -12, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-670796995/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-226636437527011/18014398509481984), (96745748906743/1125899906842624)), (526583565/18014398509481984), by norm_num⟩
  | 1 => ⟨((76545403/2147483648), (-522806829/2147483648)), (357/4294967296), by norm_num⟩
  | 2 => ⟨((-216869457/4294967296), (370305821/1073741824)), (127/1073741824), by norm_num⟩
  | 3 => ⟨((3200195/67108864), (-699436929/2147483648)), (481/4294967296), by norm_num⟩
  | 4 => ⟨((-145069363/4294967296), (247706755/1073741824)), (171/2147483648), by norm_num⟩
  | 5 => ⟨((82202491/4294967296), (-561444867/4294967296)), (389/8589934592), by norm_num⟩
  | 6 => ⟨((-38816199/4294967296), (1060462059/17179869184)), (369/17179869184), by norm_num⟩
  | 7 => ⟨((251370453/68719476736), (-1716865861/68719476736)), (75/8589934592), by norm_num⟩
  | 8 => ⟨((-89023265/68719476736), (1216061817/137438953472)), (427/137438953472), by norm_num⟩
  | 9 => ⟨((224197247/549755813888), (-382818063/137438953472)), (135/137438953472), by norm_num⟩
  | 10 => ⟨((-254079453/2199023255552), (1735368391/2199023255552)), (307/1099511627776), by norm_num⟩
  | 11 => ⟨((4090121/137438953472), (-893939797/4398046511104)), (635/8796093022208), by norm_num⟩
  | 12 => ⟨((-123607311/17592186044416), (1688481441/35184372088832)), (301/17592186044416), by norm_num⟩
  | 13 => ⟨((215511313/140737488355328), (-1471947123/140737488355328)), (527/140737488355328), by norm_num⟩
  | 14 => ⟨((-174454151/562949953421312), (297881445/140737488355328)), (107/140737488355328), by norm_num⟩
  | 15 => ⟨((131804221/2251799813685248), (-1800451595/4503599627370496)), (649/4503599627370496), by norm_num⟩
  | 16 => ⟨((-186714739/18014398509481984), (1275265871/18014398509481984)), (461/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (1117755287025/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778196629665717/633825300114114700748351602688), (1321999640091/316912650057057350374175801344)), (184921/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889098161538877/39614081257132168796771975168), (1486932128935/19807040628566084398385987584)), (208069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((14756507470477/19342813113834066795298816), (3158942822617/2475880078570760549798248448)), (27639/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770499151784661/154742504910672534362390528), (3158056684403/154742504910672534362390528)), (55289/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774452526777349/4835703278458516698824704), (184983557149/604462909807314587353088)), (51845/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258221301228965/604462909807314587353088), (1294414452103/302231454903657293676544)), (709/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1886869941917255/75557863725914323419136), (2102541746747/37778931862957161709568)), (295031/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648423891306327/2361183241434822606848), (1576135141227/2361183241434822606848)), (110675/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620496915719251/590295810358705651712), (2165933329291/295147905179352825856)), (304479/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911142696205173/36893488147419103232), (2705539080309/36893488147419103232)), (380785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821318689637781/9223372036854775808), (6082303329191/9223372036854775808)), (428639/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796283393397479/576460752303423488), (6075859444585/1152921504606846976)), (428959/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596669308243393/72057594037927936), (5309135362127/144115188075855872)), (375699/144115188075855872), by norm_num⟩
  | 4 => ⟨((744886638809535/18014398509481984), (7949239018815/36028797018963968)), (564269/36028797018963968), by norm_num⟩
  | 3 => ⟨((743462981775687/4503599627370496), (1238910008067/1125899906842624)), (353301/4503599627370496), by norm_num⟩
  | 2 => ⟨((555820010234913/1125899906842624), (19746927112075/4503599627370496)), (1417003/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209090441280761/2251799813685248), (29431912999397/2251799813685248)), (2135033/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166663150550271/2251799813685248), (58113536481125/2251799813685248)), (4308345/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166663150550271/2251799813685248), (58113536481125/2251799813685248)), (16435031899459075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((260405698384041/281474976710656), (111832728004135/2251799813685248)), (8513285/2251799813685248), by norm_num⟩
  | 2 => ⟨((1921754141155799/2251799813685248), (206923400285385/2251799813685248)), (8298841/1125899906842624), by norm_num⟩
  | 3 => ⟨((810534236498083/1125899906842624), (353189390090305/2251799813685248)), (31380333/2251799813685248), by norm_num⟩
  | 4 => ⟨((138951086685033/281474976710656), (508521389683503/2251799813685248)), (55025203/2251799813685248), by norm_num⟩
  | 5 => ⟨((433910633492855/2251799813685248), (1004133305558325/4503599627370496)), (9897415/281474976710656), by norm_num⟩
  | 6 => ⟨((-226636437527011/18014398509481984), (96745748906743/1125899906842624)), (526583565/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-670796995/8388608)), (1/8388608), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-342164965/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1481299300778717/18014398509481984), (153002227622997/18014398509481984)), (203935639/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1020790497/4294967296), (-105436639/4294967296)), (71/2147483648), by norm_num⟩
  | 2 => ⟨((368808003/1073741824), (76187771/2147483648)), (207/4294967296), by norm_num⟩
  | 3 => ⟨((-710661491/2147483648), (-146807321/4294967296)), (201/4294967296), by norm_num⟩
  | 4 => ⟨((4011867/16777216), (53040967/2147483648)), (147/4294967296), by norm_num⟩
  | 5 => ⟨((-1187408597/8589934592), (-61323245/4294967296)), (43/2147483648), by norm_num⟩
  | 6 => ⟨((1144017425/17179869184), (59082325/8589934592)), (21/2147483648), by norm_num⟩
  | 7 => ⟨((-1889506089/68719476736), (-195165581/68719476736)), (35/8589934592), by norm_num⟩
  | 8 => ⟨((1365343759/137438953472), (141025271/137438953472)), (51/34359738368), by norm_num⟩
  | 9 => ⟨((-438483449/137438953472), (-181162427/549755813888)), (33/68719476736), by norm_num⟩
  | 10 => ⟨((506952071/549755813888), (104725353/1099511627776)), (77/549755813888), by norm_num⟩
  | 11 => ⟨((-1065658145/4398046511104), (-110070983/4398046511104)), (41/1099511627776), by norm_num⟩
  | 12 => ⟨((1026716069/17592186044416), (106048687/17592186044416)), (5/549755813888), by norm_num⟩
  | 13 => ⟨((-913104963/70368744177664), (-47156943/35184372088832)), (287/140737488355328), by norm_num⟩
  | 14 => ⟨((1508121599/562949953421312), (155772681/562949953421312)), (239/562949953421312), by norm_num⟩
  | 15 => ⟨((-581204277/1125899906842624), (-120064255/2251799813685248)), (93/1125899906842624), by norm_num⟩
  | 16 => ⟨((419974107/4503599627370496), (86757583/9007199254740992)), (271/18014398509481984), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (67035143853/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778124413883789/633825300114114700748351602688), (158555673793/633825300114114700748351602688)), (184431/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889017143610871/39614081257132168796771975168), (178336715963/39614081257132168796771975168)), (1621/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((944373585679227/1237940039285380274899124224), (11839662583/154742504910672534362390528)), (110229/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770413700362707/154742504910672534362390528), (189380447901/154742504910672534362390528)), (220461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548825296872139/9671406556917033397649408), (177486653795/9671406556917033397649408)), (206685/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258151867869985/604462909807314587353088), (77621665305/302231454903657293676544)), (180853/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943378887679063/37778931862957161709568), (252162668113/75557863725914323419136)), (146945/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296764236901817/4722366482869645213696), (94513888651/2361183241434822606848)), (220423/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620382980438757/590295810358705651712), (129880089099/295147905179352825856)), (303089/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911072190710603/36893488147419103232), (162235435413/36893488147419103232)), (378873/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910580992593935/4611686018427387904), (182357324593/4611686018427387904)), (426249/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398103123408001/288230376151711744), (364321215751/1152921504606846976)), (426269/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193206316003123/144115188075855872), (318339024117/144115188075855872)), (373009/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489580222333201/36028797018963968), (119156471799/9007199254740992)), (559561/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486694049136487/9007199254740992), (37140058501/562949953421312)), (699537/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111422138655897/2251799813685248), (1183870426321/4503599627370496)), (1399333/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208506439719993/2251799813685248), (1764321782029/2251799813685248)), (2099667/2251799813685248), by norm_num⟩
  | 0 => ⟨((541442655921709/562949953421312), (3482975682171/2251799813685248)), (4202115/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541442655921709/562949953421312), (3482975682171/2251799813685248)), (16029796608931731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1041511380096619/1125899906842624), (6699819734967/2251799813685248)), (4048075/1125899906842624), by norm_num⟩
  | 2 => ⟨((1926875961854513/2251799813685248), (12395308776839/2251799813685248)), (939177/140737488355328), by norm_num⟩
  | 3 => ⟨((1648768823111749/2251799813685248), (5303362753807/562949953421312)), (25882501/2251799813685248), by norm_num⟩
  | 4 => ⟨((603514709665315/1125899906842624), (121347642575/8796093022208)), (9597505/562949953421312), by norm_num⟩
  | 5 => ⟨((80821737365019/281474976710656), (66606923862511/4503599627370496)), (21107769/1125899906842624), by norm_num⟩
  | 6 => ⟨((1481299300778717/18014398509481984), (153002227622997/18014398509481984)), (203935639/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-342164965/4194304)), (1/8388608), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1394261977/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((104594827857011/9007199254740992), (-1405851125503919/18014398509481984)), (109785255/4503599627370496), by norm_num⟩
  | 1 => ⟨((-36713253/1073741824), (986920083/4294967296)), (155/2147483648), by norm_num⟩
  | 2 => ⟨((108099933/2147483648), (-1452962981/4294967296)), (459/4294967296), by norm_num⟩
  | 3 => ⟨((-212195771/4294967296), (356513403/1073741824)), (113/1073741824), by norm_num⟩
  | 4 => ⟨((156199375/4294967296), (-131216495/536870912)), (167/2147483648), by norm_num⟩
  | 5 => ⟨((-183967811/8589934592), (154543585/1073741824)), (395/8589934592), by norm_num⟩
  | 6 => ⟨((180560665/17179869184), (-606725541/8589934592)), (195/8589934592), by norm_num⟩
  | 7 => ⟨((-18987495/4294967296), (63802369/2147483648)), (165/17179869184), by norm_num⟩
  | 8 => ⟨((111815041/68719476736), (-751448729/68719476736)), (61/17179869184), by norm_num⟩
  | 9 => ⟨((-146325585/274877906944), (245843881/68719476736)), (321/274877906944), by norm_num⟩
  | 10 => ⟨((86169351/549755813888), (-579097845/549755813888)), (95/274877906944), by norm_num⟩
  | 11 => ⟨((-46130981/1099511627776), (1240086013/4398046511104)), (409/4398046511104), by norm_num⟩
  | 12 => ⟨((90553239/8796093022208), (-608559599/8796093022208)), (403/17592186044416), by norm_num⟩
  | 13 => ⟨((-164079069/70368744177664), (1102687141/70368744177664)), (367/70368744177664), by norm_num⟩
  | 14 => ⟨((34508629/70368744177664), (-463827857/140737488355328)), (155/140737488355328), by norm_num⟩
  | 15 => ⟨((-13547807/140737488355328), (1456760343/2251799813685248)), (489/2251799813685248), by norm_num⟩
  | 16 => ⟨((39890691/2251799813685248), (-268083871/2251799813685248)), (181/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-926860860219/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778050015491453/633825300114114700748351602688), (-1096049935531/316912650057057350374175801344)), (361/1237940039285380274899124224), by norm_num⟩
  | 16 => ⟨((944466660938953/19807040628566084398385987584), (-1232784156373/19807040628566084398385987584)), (51991/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888657944884207/2475880078570760549798248448), (-1309493832871/1237940039285380274899124224)), (110497/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885162143745725/77371252455336267181195264), (-327278059751/19342813113834066795298816)), (110515/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548741274422935/9671406556917033397649408), (-2453774843351/9671406556917033397649408)), (103627/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157259768816211/75557863725914323419136), (-2146242700629/604462909807314587353088)), (90693/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886637614390975/75557863725914323419136), (-3486125774203/75557863725914323419136)), (36853/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324168448141565/1180591620717411303424), (-1306633108597/2361183241434822606848)), (221181/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620258094346651/590295810358705651712), (-3591084127515/590295810358705651712)), (304227/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821987487396329/73786976294838206464), (-560702748387/9223372036854775808)), (380437/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820984400184127/9223372036854775808), (-5041882711435/9223372036854775808)), (107051/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49757298835091/36028797018963968), (-5036335558969/1152921504606846976)), (214235/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193048241606075/144115188075855872), (-1100140113735/36028797018963968)), (187605/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489340101741819/36028797018963968), (-6588392812063/36028797018963968)), (281707/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486388656684583/9007199254740992), (-8213748693711/9007199254740992)), (352659/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222217863082631/4503599627370496), (-16362435949609/4503599627370496)), (1413793/4503599627370496), by norm_num⟩
  | 1 => ⟨((551882019756989/562949953421312), (-12190789205265/1125899906842624)), (1064305/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163660937702561/2251799813685248), (-12029578293609/562949953421312)), (4289053/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163660937702561/2251799813685248), (-12029578293609/562949953421312)), (16361438759810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2077943719881313/2251799813685248), (-46234889074477/1125899906842624)), (8425651/2251799813685248), by norm_num⟩
  | 2 => ⟨((1913713384703929/2251799813685248), (-170660814176881/2251799813685248)), (8121125/1125899906842624), by norm_num⟩
  | 3 => ⟨((1613453284443379/2251799813685248), (-145037708214509/1125899906842624)), (939663/70368744177664), by norm_num⟩
  | 4 => ⟨((1118699690156725/2251799813685248), (-51961005872867/281474976710656)), (1588663/70368744177664), by norm_num⟩
  | 5 => ⟨((239517837641815/1125899906842624), (-826059379764503/4503599627370496)), (1082523/35184372088832), by norm_num⟩
  | 6 => ⟨((104594827857011/9007199254740992), (-1405851125503919/18014398509481984)), (109785255/4503599627370496), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1394261977/16777216)), (1/8388608), by norm_num⟩, -13, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1418550573/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-655132375290481/9007199254740992), (-363753270727609/18014398509481984)), (59421579/2251799813685248), by norm_num⟩
  | 1 => ⟨((935841179/4294967296), (259806493/4294967296)), (341/4294967296), by norm_num⟩
  | 2 => ⟨((-350441203/1073741824), (-97288837/1073741824)), (513/4294967296), by norm_num⟩
  | 3 => ⟨((174971337/536870912), (388601745/4294967296)), (257/2147483648), by norm_num⟩
  | 4 => ⟨((-1048334563/4294967296), (-291036697/4294967296)), (387/4294967296), by norm_num⟩
  | 5 => ⟨((628105937/4294967296), (174373605/4294967296)), (233/4294967296), by norm_num⟩
  | 6 => ⟨((-627212409/8589934592), (-348251091/17179869184)), (467/17179869184), by norm_num⟩
  | 7 => ⟨((1073691689/34359738368), (298076295/34359738368)), (401/34359738368), by norm_num⟩
  | 8 => ⟨((-804123211/68719476736), (-446478389/137438953472)), (603/137438953472), by norm_num⟩
  | 9 => ⟨((1070639047/274877906944), (297228827/274877906944)), (403/274877906944), by norm_num⟩
  | 10 => ⟨((-1282939179/1099511627776), (-89041799/274877906944)), (485/1099511627776), by norm_num⟩
  | 11 => ⟨((349394755/1099511627776), (24249581/274877906944)), (265/2199023255552), by norm_num⟩
  | 12 => ⟨((-1395590859/17592186044416), (-193720673/8796093022208)), (133/4398046511104), by norm_num⟩
  | 13 => ⟨((1286405101/70368744177664), (178564699/35184372088832)), (123/17592186044416), by norm_num⟩
  | 14 => ⟨((-1101064365/281474976710656), (-305675447/281474976710656)), (423/281474976710656), by norm_num⟩
  | 15 => ⟨((439799207/562949953421312), (244192481/1125899906842624)), (85/281474976710656), by norm_num⟩
  | 16 => ⟨((-658760339/4503599627370496), (-11430239/281474976710656)), (511/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1869764859483/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777973962745881/633825300114114700748351602688), (-4421819923537/633825300114114700748351602688)), (185271/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236105918180425/4951760157141521099596496896), (-4973409973433/39614081257132168796771975168)), (104243/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888566036591503/2475880078570760549798248448), (-5282852779683/2475880078570760549798248448)), (221581/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770231751748795/154742504910672534362390528), (-5281283322655/154742504910672534362390528)), (110827/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774326928020757/4835703278458516698824704), (-4949535958917/9671406556917033397649408)), (207879/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314500248483493/151115727451828646838272), (-2164588624115/302231454903657293676544)), (181971/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943255494192487/37778931862957161709568), (-7031788871929/75557863725914323419136)), (295849/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40518054176161/147573952589676412928), (-5271108952989/4722366482869645213696)), (111007/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620124245432495/590295810358705651712), (-7243335926615/590295810358705651712)), (76369/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910908764334793/36893488147419103232), (-9047514655327/73786976294838206464)), (382157/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910394781540555/4611686018427387904), (-10169308009187/9223372036854775808)), (215177/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592034194027389/1152921504606846976), (-10157883031581/1152921504606846976)), (430889/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192868710135481/144115188075855872), (-8875304863019/144115188075855872)), (377631/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489060672201529/36028797018963968), (-3321824376135/9007199254740992)), (567653/36028797018963968), by norm_num⟩
  | 3 => ⟨((92876357352363/562949953421312), (-16564275311505/9007199254740992)), (711681/9007199254740992), by norm_num⟩
  | 2 => ⟨((138839459104141/281474976710656), (-16497121677261/2251799813685248)), (714861/2251799813685248), by norm_num⟩
  | 1 => ⟨((551554452645819/562949953421312), (-3072275701449/140737488355328)), (1080263/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080262519113687/1125899906842624), (-48488949947977/1125899906842624)), (2192551/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080262519113687/1125899906842624), (-48488949947977/1125899906842624)), (8363918308738326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((129298342247929/140737488355328), (-46523491921117/562949953421312)), (4396209/1125899906842624), by norm_num⟩
  | 2 => ⟨((1885244285151565/2251799813685248), (-341936491906003/2251799813685248)), (17608793/2251799813685248), by norm_num⟩
  | 3 => ⟨((1526434734255689/2251799813685248), (-572549845090867/2251799813685248)), (4354069/281474976710656), by norm_num⟩
  | 4 => ⟨((889150829776435/2251799813685248), (-388116192801841/1125899906842624)), (64937381/2251799813685248), by norm_num⟩
  | 5 => ⟨((167024155956721/4503599627370496), (-153252448455733/562949953421312)), (192105225/4503599627370496), by norm_num⟩
  | 6 => ⟨((-655132375290481/9007199254740992), (-363753270727609/18014398509481984)), (59421579/2251799813685248), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1418550573/16777216)), (1/8388608), by norm_num⟩, -13, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-720826939/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-584099450080993/18014398509481984), (145703052639455/2251799813685248)), (233734289/9007199254740992), by norm_num⟩
  | 1 => ⟨((423980685/4294967296), (-846092631/4294967296)), (341/4294967296), by norm_num⟩
  | 2 => ⟨((-322704677/2147483648), (80498375/268435456)), (521/4294967296), by norm_num⟩
  | 3 => ⟨((654987753/4294967296), (-1307088581/4294967296)), (531/4294967296), by norm_num⟩
  | 4 => ⟨((-124632807/1073741824), (124358141/536870912)), (203/2147483648), by norm_num⟩
  | 5 => ⟨((151778951/2147483648), (-605777841/4294967296)), (31/536870912), by norm_num⟩
  | 6 => ⟨((-77015737/2147483648), (1229536153/17179869184)), (505/17179869184), by norm_num⟩
  | 7 => ⟨((535945461/34359738368), (-66845543/2147483648)), (221/17179869184), by norm_num⟩
  | 8 => ⟨((-407924495/68719476736), (407025511/34359738368)), (169/34359738368), by norm_num⟩
  | 9 => ⟨((551971235/274877906944), (-1101509601/274877906944)), (459/274877906944), by norm_num⟩
  | 10 => ⟨((-168048881/274877906944), (670714139/549755813888)), (561/1099511627776), by norm_num⟩
  | 11 => ⟨((372093519/2199023255552), (-371273499/1099511627776)), (39/274877906944), by norm_num⟩
  | 12 => ⟨((-377615689/8796093022208), (753566999/8796093022208)), (159/4398046511104), by norm_num⟩
  | 13 => ⟨((707482731/70368744177664), (-1411847161/70368744177664)), (299/35184372088832), by norm_num⟩
  | 14 => ⟨((-615413443/281474976710656), (1228114389/281474976710656)), (261/140737488355328), by norm_num⟩
  | 15 => ⟨((499637343/1125899906842624), (-249268121/281474976710656)), (213/562949953421312), by norm_num⟩
  | 16 => ⟨((-380289275/4503599627370496), (189725597/1125899906842624)), (163/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (2651240680213/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((27779911904503/9903520314283042199192993792), (783687714359/158456325028528675187087900672)), (185017/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472195149476979/9903520314283042199192993792), (3525786702905/39614081257132168796771975168)), (208185/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944247760084619/1237940039285380274899124224), (3745144343293/2475880078570760549798248448)), (110621/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110635105504823/9671406556917033397649408), (3744015204829/154742504910672534362390528)), (110647/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548588652030075/9671406556917033397649408), (1754407465679/4835703278458516698824704)), (103759/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314486105173037/151115727451828646838272), (3069014176347/604462909807314587353088)), (90817/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943209978246849/37778931862957161709568), (4984901043685/75557863725914323419136)), (295257/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648255123008209/2361183241434822606848), (3736710586945/4722366482869645213696)), (221533/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202504090755887/73786976294838206464), (1283696335945/147573952589676412928)), (304755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910852520354267/36893488147419103232), (3206848568007/36893488147419103232)), (95291/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910332818732127/4611686018427387904), (3604417722871/4611686018427387904)), (429113/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795956770302603/576460752303423488), (28127443455/4503599627370496)), (429493/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596383405012603/72057594037927936), (3145660649311/72057594037927936)), (188117/72057594037927936), by norm_num⟩
  | 4 => ⟨((744457570688983/18014398509481984), (9418555173541/36028797018963968)), (565207/36028797018963968), by norm_num⟩
  | 3 => ⟨((46432892475639/281474976710656), (11741003975665/9007199254740992)), (88501/1125899906842624), by norm_num⟩
  | 2 => ⟨((2221131079714729/4503599627370496), (11692832585199/2251799813685248)), (1420527/4503599627370496), by norm_num⟩
  | 1 => ⟨((551465447622287/562949953421312), (17419217397343/1125899906842624)), (2142099/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080093020402351/1125899906842624), (34360686109045/1125899906842624)), (4329643/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080093020402351/1125899906842624), (34360686109045/1125899906842624)), (16516277321822356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1035101138999285/1125899906842624), (131850929259569/2251799813685248)), (4285627/1125899906842624), by norm_num⟩
  | 2 => ⟨((1895529424215717/2251799813685248), (121217744335217/1125899906842624)), (8381899/1125899906842624), by norm_num⟩
  | 3 => ⟨((1569525323885965/2251799813685248), (25509794401797/140737488355328)), (31832681/2251799813685248), by norm_num⟩
  | 4 => ⟨((509996010323049/1125899906842624), (568978014154379/2251799813685248)), (13978801/562949953421312), by norm_num⟩
  | 5 => ⟨((636511058607647/4503599627370496), (1030914081853015/4503599627370496)), (157825017/4503599627370496), by norm_num⟩
  | 6 => ⟨((-584099450080993/18014398509481984), (145703052639455/2251799813685248)), (233734289/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-720826939/8388608)), (1/8388608), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile044Terms2
