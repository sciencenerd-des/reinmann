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
namespace Reinmann.XiBand97.Tile035Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (6581/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (6581/256))
  have he : value ((69/80), (6581/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-10415181/131072)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-757090336156359/18014398509481984), (249447939960619/4503599627370496)), (457591877/18014398509481984), by norm_num⟩
  | 1 => ⟨((278973385/2147483648), (-735334561/4294967296)), (339/4294967296), by norm_num⟩
  | 2 => ⟨((-53894911/268435456), (1136475173/4294967296)), (263/2147483648), by norm_num⟩
  | 3 => ⟨((27765243/134217728), (-73185271/268435456)), (17/134217728), by norm_num⟩
  | 4 => ⟨((-686588359/4294967296), (904875119/4294967296)), (423/4294967296), by norm_num⟩
  | 5 => ⟨((424454753/4294967296), (-1118802963/8589934592)), (525/8589934592), by norm_num⟩
  | 6 => ⟨((-437335887/8589934592), (1152755819/17179869184)), (543/17179869184), by norm_num⟩
  | 7 => ⟨((772470739/34359738368), (-509031025/17179869184)), (481/34359738368), by norm_num⟩
  | 8 => ⟨((-298467481/34359738368), (393359127/34359738368)), (373/68719476736), by norm_num⟩
  | 9 => ⟨((820067249/274877906944), (-1080790899/274877906944)), (515/274877906944), by norm_num⟩
  | 10 => ⟨((-63371567/68719476736), (334077055/274877906944)), (5/8589934592), by norm_num⟩
  | 11 => ⟨((569844957/2199023255552), (-375507767/1099511627776)), (361/2199023255552), by norm_num⟩
  | 12 => ⟨((-293569159/4398046511104), (386903483/4398046511104)), (187/4398046511104), by norm_num⟩
  | 13 => ⟨((279210687/17592186044416), (-91995007/4398046511104)), (179/17592186044416), by norm_num⟩
  | 14 => ⟨((-493172621/140737488355328), (649966793/140737488355328)), (159/70368744177664), by norm_num⟩
  | 15 => ⟨((813022671/1125899906842624), (-66969165/70368744177664)), (263/562949953421312), by norm_num⟩
  | 16 => ⟨((-314135949/2251799813685248), (51751133/281474976710656)), (51/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (2891646800357/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777851567955213/633825300114114700748351602688), (3418773544123/633825300114114700748351602688)), (185073/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888709916552353/39614081257132168796771975168), (3845224385461/39614081257132168796771975168)), (208251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888420368017955/2475880078570760549798248448), (4084438984507/2475880078570760549798248448)), (221317/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221260809519229/19342813113834066795298816), (4083188480551/154742504910672534362390528)), (221373/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548518077411677/9671406556917033397649408), (3826660958209/9671406556917033397649408)), (103799/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157235325567099/75557863725914323419136), (3347000566259/604462909807314587353088)), (45427/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943159693297335/37778931862957161709568), (5436387346163/75557863725914323419136)), (73847/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648217357468833/2361183241434822606848), (2037557002967/2361183241434822606848)), (27705/590295810358705651712), by norm_num⟩
  | 9 => ⟨((404982175669345/147573952589676412928), (87496043929/9223372036854775808)), (304915/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821574759819841/73786976294838206464), (6994384368847/73786976294838206464)), (47673/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820518726266313/9223372036854775808), (7861401409141/9223372036854775808)), (429387/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397941549798331/288230376151711744), (1963077031809/288230376151711744)), (429801/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596318702030625/72057594037927936), (857568828709/18014398509481984)), (376543/144115188075855872), by norm_num⟩
  | 4 => ⟨((186090009046387/4503599627370496), (2567603841369/9007199254740992)), (565747/36028797018963968), by norm_num⟩
  | 3 => ⟨((46425220397549/281474976710656), (12802362261579/9007199254740992)), (177205/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110317547668149/2251799813685248), (25497999726113/4503599627370496)), (44455/140737488355328), by norm_num⟩
  | 1 => ⟨((2205105522598363/2251799813685248), (37981047679755/2251799813685248)), (16767/17592186044416), by norm_num⟩
  | 0 => ⟨((2158625158014783/2251799813685248), (18725859945113/562949953421312)), (4341919/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2158625158014783/2251799813685248), (18725859945113/562949953421312)), (16563106545455168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033407148192867/1125899906842624), (17951023948629/281474976710656)), (4306689/1125899906842624), by norm_num⟩
  | 2 => ⟨((1887866762052763/2251799813685248), (263621536559733/2251799813685248)), (16910211/2251799813685248), by norm_num⟩
  | 3 => ⟨((1551889548745619/2251799813685248), (110507677815707/562949953421312)), (4039227/281474976710656), by norm_num⟩
  | 4 => ⟨((491378054202931/1125899906842624), (609275155690425/2251799813685248)), (28613189/1125899906842624), by norm_num⟩
  | 5 => ⟨((132026246217319/1125899906842624), (132953399612989/562949953421312)), (161837095/4503599627370496), by norm_num⟩
  | 6 => ⟨((-757090336156359/18014398509481984), (249447939960619/4503599627370496)), (457591877/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-10415181/131072)), (1/8388608), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-338078719/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((571152684688481/18014398509481984), (1061490708611721/18014398509481984)), (161852849/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6671421/67108864), (-396764037/2147483648)), (61/1073741824), by norm_num⟩
  | 2 => ⟨((669382463/4294967296), (1244051343/4294967296)), (385/4294967296), by norm_num⟩
  | 3 => ⟨((-699614947/4294967296), (-1300238597/4294967296)), (405/4294967296), by norm_num⟩
  | 4 => ⟨((548409655/4294967296), (509611325/2147483648)), (319/4294967296), by norm_num⟩
  | 5 => ⟨((-85976765/1073741824), (-1278306689/8589934592)), (201/4294967296), by norm_num⟩
  | 6 => ⟨((718879065/17179869184), (334010269/4294967296)), (211/8589934592), by norm_num⟩
  | 7 => ⟨((-644011757/34359738368), (-1196899733/34359738368)), (95/8589934592), by norm_num⟩
  | 8 => ⟨((504823785/68719476736), (938218047/68719476736)), (75/17179869184), by norm_num⟩
  | 9 => ⟨((-175874673/68719476736), (-81716035/17179869184)), (105/68719476736), by norm_num⟩
  | 10 => ⟨((27572701/34359738368), (51244031/34359738368)), (265/549755813888), by norm_num⟩
  | 11 => ⟨((-251502675/1099511627776), (-467419237/1099511627776)), (19/137438953472), by norm_num⟩
  | 12 => ⟨((525723455/8796093022208), (977060209/8796093022208)), (319/8796093022208), by norm_num⟩
  | 13 => ⟨((-253600439/17592186044416), (-942635887/35184372088832)), (155/17592186044416), by norm_num⟩
  | 14 => ⟨((454378691/140737488355328), (844465535/140737488355328)), (35/17592186044416), by norm_num⟩
  | 15 => ⟨((-379920469/562949953421312), (-5516285/4398046511104)), (59/140737488355328), by norm_num⟩
  | 16 => ⟨((37226201/281474976710656), (1106961901/4503599627370496)), (93/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (1403122708975/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777797316805099/633825300114114700748351602688), (1658796978217/633825300114114700748351602688)), (184727/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472162290406043/9903520314283042199192993792), (1865711204887/39614081257132168796771975168)), (207839/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888356186436475/2475880078570760549798248448), (990885745595/1237940039285380274899124224)), (110427/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885011355480095/77371252455336267181195264), (1981156793209/154742504910672534362390528)), (220881/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774229369801881/4835703278458516698824704), (464170408193/2417851639229258349412352)), (207105/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257831125620949/604462909807314587353088), (202992981953/75557863725914323419136)), (90623/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943118280320723/37778931862957161709568), (1318842901107/37778931862957161709568)), (294579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296373318508915/4722366482869645213696), (988597434921/2361183241434822606848)), (220983/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809922727975667/295147905179352825856), (2716906182911/590295810358705651712)), (303929/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455368114678073/18446744073709551616), (1696764792991/36893488147419103232)), (95007/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820406049352053/9223372036854775808), (1907072356843/4611686018427387904)), (427693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795828265197081/576460752303423488), (1904839748367/576460752303423488)), (213947/576460752303423488), by norm_num⟩
  | 5 => ⟨((596272409414357/72057594037927936), (1664226440447/72057594037927936)), (374635/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488587921593137/36028797018963968), (4982662666839/36028797018963968)), (562407/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485453585303787/9007199254740992), (776354588407/1125899906842624)), (351903/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110181559497177/2251799813685248), (6184674149595/2251799813685248)), (705007/2251799813685248), by norm_num⟩
  | 1 => ⟨((551196060174597/562949953421312), (18423732428121/2251799813685248)), (2121051/2251799813685248), by norm_num⟩
  | 0 => ⟨((8430957283929/8796093022208), (18164715083965/1125899906842624)), (4266373/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((8430957283929/8796093022208), (18164715083965/1125899906842624)), (16274921425826262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((517036109188267/562949953421312), (69642709125969/2251799813685248)), (4158103/1125899906842624), by norm_num⟩
  | 2 => ⟨((474328499182415/562949953421312), (63962693559143/1125899906842624)), (3947571/562949953421312), by norm_num⟩
  | 3 => ⟨((198920629830119/281474976710656), (26946736788223/281474976710656)), (1775197/140737488355328), by norm_num⟩
  | 4 => ⟨((1103992711605243/2251799813685248), (152347804879007/1125899906842624)), (22791885/1125899906842624), by norm_num⟩
  | 5 => ⟨((1000053811025915/4503599627370496), (298766995526523/2251799813685248)), (114065781/4503599627370496), by norm_num⟩
  | 6 => ⟨((571152684688481/18014398509481984), (1061490708611721/18014398509481984)), (161852849/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-338078719/4194304)), (1/8388608), by norm_num⟩, -13, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-685335257/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((290446013322015/4503599627370496), (-19659375859599/18014398509481984)), (36768707/4503599627370496), by norm_num⟩
  | 1 => ⟨((-880292001/4294967296), (931003/268435456)), (225/8589934592), by norm_num⟩
  | 2 => ⟨((1398807683/4294967296), (-23670221/4294967296)), (181/4294967296), by norm_num⟩
  | 3 => ⟨((-1481828705/4294967296), (25075079/4294967296)), (97/2147483648), by norm_num⟩
  | 4 => ⟨((73583303/268435456), (-2490311/536870912)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((-1496650867/8589934592), (3165737/1073741824)), (25/1073741824), by norm_num⟩
  | 6 => ⟨((1585479007/17179869184), (-6707255/4294967296)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((-1439639323/34359738368), (24361163/34359738368)), (49/8589934592), by norm_num⟩
  | 8 => ⟨((71488301/4294967296), (-2419409/8589934592)), (157/68719476736), by norm_num⟩
  | 9 => ⟨((-807799711/137438953472), (27338709/274877906944)), (7/8589934592), by norm_num⟩
  | 10 => ⟨((513446193/274877906944), (-8688389/274877906944)), (287/1099511627776), by norm_num⟩
  | 11 => ⟨((-296683571/549755813888), (20081577/2199023255552)), (21/274877906944), by norm_num⟩
  | 12 => ⟨((1257168479/8796093022208), (-5318361/2199023255552)), (45/2199023255552), by norm_num⟩
  | 13 => ⟨((-153667273/4398046511104), (5200627/8796093022208)), (89/17592186044416), by norm_num⟩
  | 14 => ⟨((558128989/70368744177664), (-18888997/140737488355328)), (163/140737488355328), by norm_num⟩
  | 15 => ⟨((-946007451/562949953421312), (32016133/1125899906842624)), (139/562949953421312), by norm_num⟩
  | 16 => ⟨((1503231301/4503599627370496), (-25437249/4503599627370496)), (223/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-11020158221/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777742265420809/633825300114114700748351602688), (-13027439761/316912650057057350374175801344)), (184405/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888587324228945/39614081257132168796771975168), (-14652419237/19807040628566084398385987584)), (207457/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944145305534465/1237940039285380274899124224), (-7781922719/618970019642690137449562112)), (220423/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55311164942387/4835703278458516698824704), (-31117908665/154742504910672534362390528)), (27553/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387099386927001/2417851639229258349412352), (-29162650125/9671406556917033397649408)), (25831/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628888866969563/302231454903657293676544), (-25506934509/604462909807314587353088)), (90409/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886150082431221/75557863725914323419136), (-41429308323/75557863725914323419136)), (146915/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296308707437313/4722366482869645213696), (-7763740979/1180591620717411303424)), (110187/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619757017535301/590295810358705651712), (-10668235427/147573952589676412928)), (37877/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227670314061817/9223372036854775808), (-53299760679/73786976294838206464)), (378773/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455070796465073/2305843009213693952), (-936020913/144115188075855872)), (426123/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591534697197447/1152921504606846976), (-14958576467/288230376151711744)), (26633/72057594037927936), by norm_num⟩
  | 5 => ⟨((1192439370831713/144115188075855872), (-26137609887/72057594037927936)), (93217/36028797018963968), by norm_num⟩
  | 4 => ⟨((372108013533741/9007199254740992), (-78253517931/36028797018963968)), (139829/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485262766950343/9007199254740992), (-48769369827/4503599627370496)), (699169/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219993462538117/4503599627370496), (-48561387759/1125899906842624)), (87401/281474976710656), by norm_num⟩
  | 1 => ⟨((275532433857411/281474976710656), (-289297386231/2251799813685248)), (2097843/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078696488910101/1125899906842624), (-285182038229/1125899906842624)), (4196697/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078696488910101/1125899906842624), (-285182038229/1125899906842624)), (16009128579146575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033472004737299/1125899906842624), (-68306441245/140737488355328)), (2010907/562949953421312), by norm_num⟩
  | 2 => ⟨((1897262944024293/2251799813685248), (-2006367900831/2251799813685248)), (14774423/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598544698058457/2251799813685248), (-3380946607413/2251799813685248)), (6230707/562949953421312), by norm_num⟩
  | 4 => ⟨((567398066506817/1125899906842624), (-2400122000567/1125899906842624)), (34629/2199023255552), by norm_num⟩
  | 5 => ⟨((142967773304495/562949953421312), (-9676345644765/4503599627370496)), (17945733/1125899906842624), by norm_num⟩
  | 6 => ⟨((290446013322015/4503599627370496), (-19659375859599/18014398509481984)), (36768707/4503599627370496), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-685335257/8388608)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-347069183/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((67773138652399/2251799813685248), (-491009381796753/9007199254740992)), (75006279/4503599627370496), by norm_num⟩
  | 1 => ⟨((-13002951/134217728), (188410071/1073741824)), (29/536870912), by norm_num⟩
  | 2 => ⟨((334839077/2147483648), (-606468623/2147483648)), (375/4294967296), by norm_num⟩
  | 3 => ⟨((-179634235/1073741824), (325357865/1073741824)), (405/4294967296), by norm_num⟩
  | 4 => ⟨((72277537/536870912), (-523643283/2147483648)), (41/536870912), by norm_num⟩
  | 5 => ⟨((-744487733/8589934592), (337108541/2147483648)), (53/1073741824), by norm_num⟩
  | 6 => ⟨((399402261/8589934592), (-361703511/4294967296)), (229/8589934592), by norm_num⟩
  | 7 => ⟨((-367321795/17179869184), (665302107/17179869184)), (423/34359738368), by norm_num⟩
  | 8 => ⟨((591181623/68719476736), (-535381217/34359738368)), (171/34359738368), by norm_num⟩
  | 9 => ⟨((-52859451/17179869184), (382961257/68719476736)), (123/68719476736), by norm_num⟩
  | 10 => ⟨((544473629/549755813888), (-493081893/274877906944)), (319/549755813888), by norm_num⟩
  | 11 => ⟨((-318653273/1099511627776), (72144063/137438953472)), (47/274877906944), by norm_num⟩
  | 12 => ⟨((683803545/8796093022208), (-1238521495/8796093022208)), (405/8796093022208), by norm_num⟩
  | 13 => ⟨((-677254985/35184372088832), (153332573/4398046511104)), (403/35184372088832), by norm_num⟩
  | 14 => ⟨((622857057/140737488355328), (-1128133743/140737488355328)), (373/140737488355328), by norm_num⟩
  | 15 => ⟨((-534639873/562949953421312), (968352649/562949953421312)), (161/281474976710656), by norm_num⟩
  | 16 => ⟨((430234841/2251799813685248), (-779251733/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-173627136939/1267650600228229401496703205376)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777686603371835/633825300114114700748351602688), (-205240745393/79228162514264337593543950336)), (184723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118032790015757/2475880078570760549798248448), (-923362546523/19807040628566084398385987584)), (207835/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118013995102813/154742504910672534362390528), (-1961589953929/2475880078570760549798248448)), (220849/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884945245105455/77371252455336267181195264), (-490241345153/38685626227668133590597632)), (55219/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548334829428245/9671406556917033397649408), (-918870851471/4835703278458516698824704)), (207101/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257722750974177/604462909807314587353088), (-803680475025/302231454903657293676544)), (90621/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943030269733351/37778931862957161709568), (-2610718983843/75557863725914323419136)), (73643/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296241379258103/4722366482869645213696), (-122309539849/295147905179352825856)), (220977/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809832081962767/295147905179352825856), (-2689045349839/590295810358705651712)), (303919/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227655753775761/9223372036854775808), (-1679330996559/36893488147419103232)), (380015/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820151573528451/9223372036854775808), (-3774861690975/9223372036854775808)), (427677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795701187268517/576460752303423488), (-3770325476611/1152921504606846976)), (427877/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596161395973877/72057594037927936), (-3293938554759/144115188075855872)), (374617/144115188075855872), by norm_num⟩
  | 4 => ⟨((744127799545229/18014398509481984), (-1232683210639/9007199254740992)), (70297/4503599627370496), by norm_num⟩
  | 3 => ⟨((742519717865527/4503599627370496), (-6145649094663/9007199254740992)), (703761/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219538570025331/4503599627370496), (-12238154067505/4503599627370496)), (704951/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101778378026247/1125899906842624), (-18224917911733/2251799813685248)), (2120831/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155907231486571/2251799813685248), (-17961926800271/1125899906842624)), (16663/8796093022208), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2155907231486571/2251799813685248), (-17961926800271/1125899906842624)), (63564300570663807/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((515881278530925/562949953421312), (-68788082572511/2251799813685248)), (2076063/562949953421312), by norm_num⟩
  | 2 => ⟨((1888890864305649/2251799813685248), (-126073317066747/2251799813685248)), (15727213/2251799813685248), by norm_num⟩
  | 3 => ⟨((1577411186551249/2251799813685248), (-211509686956013/2251799813685248)), (7036543/562949953421312), by norm_num⟩
  | 4 => ⟨((542563705914387/1125899906842624), (-148164923116475/1125899906842624)), (44720917/2251799813685248), by norm_num⟩
  | 5 => ⟨((120979906329951/562949953421312), (-285598779372957/2251799813685248)), (109743391/4503599627370496), by norm_num⟩
  | 6 => ⟨((67773138652399/2251799813685248), (-491009381796753/9007199254740992)), (75006279/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-347069183/4194304)), (1/8388608), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-175649041/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-130876394295123/4503599627370496), (-949710787852011/18014398509481984)), (391875055/18014398509481984), by norm_num⟩
  | 1 => ⟨((406654289/4294967296), (737726553/4294967296)), (153/2147483648), by norm_num⟩
  | 2 => ⟨((-331229733/2147483648), (-300448041/1073741824)), (501/4294967296), by norm_num⟩
  | 3 => ⟨((359726149/2147483648), (1305184963/4294967296)), (273/2147483648), by norm_num⟩
  | 4 => ⟨((-146502815/1073741824), (-1063104653/4294967296)), (447/4294967296), by norm_num⟩
  | 5 => ⟨((95464063/1073741824), (346369759/2147483648)), (293/4294967296), by norm_num⟩
  | 6 => ⟨((-207354089/4294967296), (-752337409/8589934592)), (5/134217728), by norm_num⟩
  | 7 => ⟨((96511377/4294967296), (350169701/8589934592)), (75/4294967296), by norm_num⟩
  | 8 => ⟨((-628886767/68719476736), (-1140886691/68719476736)), (491/68719476736), by norm_num⟩
  | 9 => ⟨((455327511/137438953472), (103253305/17179869184)), (357/137438953472), by norm_num⟩
  | 10 => ⟨((-593400395/549755813888), (-538254777/274877906944)), (467/549755813888), by norm_num⟩
  | 11 => ⟨((703038463/2199023255552), (1275408019/2199023255552)), (555/2199023255552), by norm_num⟩
  | 12 => ⟨((-381761197/4398046511104), (-692567075/4398046511104)), (303/4398046511104), by norm_num⟩
  | 13 => ⟨((382712257/17592186044416), (173573107/4398046511104)), (153/8796093022208), by norm_num⟩
  | 14 => ⟨((-178130497/35184372088832), (-80788277/8796093022208)), (143/35184372088832), by norm_num⟩
  | 15 => ⟨((309528723/281474976710656), (1123054957/562949953421312)), (499/562949953421312), by norm_num⟩
  | 16 => ⟨((-252118615/1125899906842624), (-914755367/2251799813685248)), (51/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-2702372805191/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((6943869096365/2475880078570760549798248448), (-3194235752845/633825300114114700748351602688)), (185029/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944230653391531/19807040628566084398385987584), (-224539886673/2475880078570760549798248448)), (104099/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888156352570503/2475880078570760549798248448), (-3816083408003/2475880078570760549798248448)), (110629/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769822609617059/154742504910672534362390528), (-3814852394977/154742504910672534362390528)), (221311/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774135430338961/4835703278458516698824704), (-1787558315051/4835703278458516698824704)), (207535/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257666447957031/604462909807314587353088), (-3126920079773/604462909807314587353088)), (90825/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885968428344709/75557863725914323419136), (-5078795659665/75557863725914323419136)), (295285/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648085877621887/2361183241434822606848), (-1903477279925/2361183241434822606848)), (55389/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619567553635681/590295810358705651712), (-2615541766733/295147905179352825856)), (152395/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821123953751539/73786976294838206464), (-6533639547881/73786976294838206464)), (95303/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820012435081491/9223372036854775808), (-3671589955257/4611686018427387904)), (429173/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198907623583453/144115188075855872), (-3667116487415/576460752303423488)), (53695/144115188075855872), by norm_num⟩
  | 5 => ⟨((596098279339097/72057594037927936), (-3203700314041/72057594037927936)), (376301/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488061227167973/36028797018963968), (-1198878082455/4503599627370496)), (565325/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484787725493457/9007199254740992), (-5976857566093/4503599627370496)), (354093/4503599627370496), by norm_num⟩
  | 2 => ⟨((69344033930195/140737488355328), (-11901252011455/2251799813685248)), (88811/281474976710656), by norm_num⟩
  | 1 => ⟨((2202697970416223/2251799813685248), (-17721193339955/1125899906842624)), (2143009/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153935004107521/2251799813685248), (-69844960031595/2251799813685248)), (541553/281474976710656), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153935004107521/2251799813685248), (-69844960031595/2251799813685248)), (2065860749364757449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((257269632457527/281474976710656), (-133618897522097/2251799813685248)), (4278515/1125899906842624), by norm_num⟩
  | 2 => ⟨((936618887438049/1125899906842624), (-122128386177031/1125899906842624)), (8328935/1125899906842624), by norm_num⟩
  | 3 => ⟨((1531822842074395/2251799813685248), (-406386935430217/2251799813685248)), (31328673/2251799813685248), by norm_num⟩
  | 4 => ⟨((484352753063469/1125899906842624), (-552902426431795/2251799813685248)), (53931563/2251799813685248), by norm_num⟩
  | 5 => ⟨((280970475528655/2251799813685248), (-475708028378307/2251799813685248)), (145772631/4503599627370496), by norm_num⟩
  | 6 => ⟨((-130876394295123/4503599627370496), (-949710787852011/18014398509481984)), (391875055/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-175649041/2097152)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1421469445/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1044791801324833/18014398509481984), (-50737176427467/9007199254740992)), (44089173/2251799813685248), by norm_num⟩
  | 1 => ⟨((205246409/1073741824), (19934351/1073741824)), (557/8589934592), by norm_num⟩
  | 2 => ⟨((-1352917363/4294967296), (-65700369/2147483648)), (461/4294967296), by norm_num⟩
  | 3 => ⟨((185791455/536870912), (72179233/2147483648)), (509/4294967296), by norm_num⟩
  | 4 => ⟨((-612338327/2147483648), (-118945489/4294967296)), (211/2147483648), by norm_num⟩
  | 5 => ⟨((807266893/4294967296), (156809971/8589934592)), (279/4294967296), by norm_num⟩
  | 6 => ⟨((-886873329/8589934592), (-172273361/17179869184)), (615/17179869184), by norm_num⟩
  | 7 => ⟨((1670279893/34359738368), (162224255/34359738368)), (581/34359738368), by norm_num⟩
  | 8 => ⟨((-86015157/4294967296), (-66833085/34359738368)), (15/2147483648), by norm_num⟩
  | 9 => ⟨((1007971291/137438953472), (48949099/68719476736)), (353/137438953472), by norm_num⟩
  | 10 => ⟨((-166105447/68719476736), (-32265649/137438953472)), (467/549755813888), by norm_num⟩
  | 11 => ⟨((1592600599/2199023255552), (38669933/549755813888)), (281/1099511627776), by norm_num⟩
  | 12 => ⟨((-1749650589/8796093022208), (-84966527/4398046511104)), (619/8796093022208), by norm_num⟩
  | 13 => ⟨((887163525/17592186044416), (86164865/17592186044416)), (315/17592186044416), by norm_num⟩
  | 14 => ⟨((-835413215/70368744177664), (-20284667/17592186044416)), (149/35184372088832), by norm_num⟩
  | 15 => ⟨((1468472359/562949953421312), (35655975/140737488355328)), (263/281474976710656), by norm_num⟩
  | 16 => ⟨((-604980667/1125899906842624), (-117516277/2251799813685248)), (435/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-3966155916885/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777574052984587/633825300114114700748351602688), (-4687789780245/633825300114114700748351602688)), (185323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29506210758679/618970019642690137449562112), (-2636221929045/19807040628566084398385987584)), (208549/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((14750688284859/19342813113834066795298816), (-5600344403347/2475880078570760549798248448)), (221653/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769753857218661/154742504910672534362390528), (-2799257101165/77371252455336267181195264)), (110865/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774102937112647/4835703278458516698824704), (-5246663003631/9671406556917033397649408)), (103977/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628804527135227/302231454903657293676544), (-2294443329743/302231454903657293676544)), (91021/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471468542496083/18889465931478580854784), (-7453298076809/75557863725914323419136)), (295973/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296100193199233/4722366482869645213696), (-5586787414975/4722366482869645213696)), (222115/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809733873510037/295147905179352825856), (-7676657575039/590295810358705651712)), (76407/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820997086019259/73786976294838206464), (-9588063420865/73786976294838206464)), (95591/18446744073709551616), by norm_num⟩
  | 7 => ⟨((454966703612099/2305843009213693952), (-10775910062417/9223372036854775808)), (215307/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795555879547843/576460752303423488), (-10762593533303/1152921504606846976)), (215591/576460752303423488), by norm_num⟩
  | 5 => ⟨((298015483811455/36028797018963968), (-9402302108175/144115188075855872)), (377925/144115188075855872), by norm_num⟩
  | 4 => ⟨((743925614048763/18014398509481984), (-14073553361403/36028797018963968)), (71021/4503599627370496), by norm_num⟩
  | 3 => ⟨((1484511184819577/9007199254740992), (-8769847540195/4503599627370496)), (89057/1125899906842624), by norm_num⟩
  | 2 => ⟨((277301769781147/562949953421312), (-4365370321519/562949953421312)), (715833/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100850968965571/1125899906842624), (-25997234267087/1125899906842624)), (541109/562949953421312), by norm_num⟩
  | 0 => ⟨((33617721747725/35184372088832), (-51217801493737/1125899906842624)), (2198473/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((33617721747725/35184372088832), (-51217801493737/1125899906842624)), (8386508945945357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((256384154237963/281474976710656), (-195748930212479/2251799813685248)), (137537/35184372088832), by norm_num⟩
  | 2 => ⟨((1851223071350491/2251799813685248), (-178299771091561/1125899906842624)), (17565821/2251799813685248), by norm_num⟩
  | 3 => ⟨((1465433830467659/2251799813685248), (-586326809079923/2251799813685248)), (34445529/2251799813685248), by norm_num⟩
  | 4 => ⟨((801011339227951/2251799813685248), (-763143452196743/2251799813685248)), (31385553/1125899906842624), by norm_num⟩
  | 5 => ⟨((52607906423135/4503599627370496), (-1085863059321843/4503599627370496)), (87204669/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1044791801324833/18014398509481984), (-50737176427467/9007199254740992)), (44089173/2251799813685248), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1421469445/16777216)), (1/8388608), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile035Terms3
