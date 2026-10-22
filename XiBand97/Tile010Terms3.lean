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
namespace Reinmann.XiBand97.Tile010Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (24671/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (24671/1280))
  have he : value ((69/80), (24671/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-89456925/33554432), (-999543385/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1244542698323117/18014398509481984), (-70511615453209/9007199254740992)), (210824375/18014398509481984), by norm_num⟩
  | 1 => ⟨((1834361227/8589934592), (103928755/4294967296)), (313/8589934592), by norm_num⟩
  | 2 => ⟨((-1417522107/4294967296), (-160624097/4294967296)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((1460540337/4294967296), (82749317/2147483648)), (253/4294967296), by norm_num⟩
  | 4 => ⟨((-1128648047/4294967296), (-63945413/2147483648)), (197/4294967296), by norm_num⟩
  | 5 => ⟨((1395479611/8589934592), (158126389/8589934592)), (245/8589934592), by norm_num⟩
  | 6 => ⟨((-1437828907/17179869184), (-162925127/17179869184)), (127/8589934592), by norm_num⟩
  | 7 => ⟨((1269825769/34359738368), (71944069/17179869184)), (113/17179869184), by norm_num⟩
  | 8 => ⟨((-245317835/17179869184), (-55595543/34359738368)), (11/4294967296), by norm_num⟩
  | 9 => ⟨((337016819/68719476736), (152753941/274877906944)), (61/68719476736), by norm_num⟩
  | 10 => ⟨((-208346659/137438953472), (-188867567/1099511627776)), (19/68719476736), by norm_num⟩
  | 11 => ⟨((1873478889/4398046511104), (212290061/4398046511104)), (43/549755813888), by norm_num⟩
  | 12 => ⟨((-482583565/4398046511104), (-109366265/8796093022208)), (179/8796093022208), by norm_num⟩
  | 13 => ⟨((114745099/4398046511104), (208034319/70368744177664)), (343/70368744177664), by norm_num⟩
  | 14 => ⟨((-810701651/140737488355328), (-91863273/140737488355328)), (305/281474976710656), by norm_num⟩
  | 15 => ⟨((1336487051/1125899906842624), (37860437/281474976710656)), (253/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1032784553/4503599627370496), (-58514109/2251799813685248)), (197/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580502973027685/10141204801825835211973625643008), (-1972649445571/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777846167279017/633825300114114700748351602688), (-1166124738191/158456325028528675187087900672)), (23165/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472175886358627/9903520314283042199192993792), (-1311580766951/9903520314283042199192993792)), (6517/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944206601501497/1237940039285380274899124224), (-5572699343227/2475880078570760549798248448)), (110823/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221259858305153/19342813113834066795298816), (-5570990842495/154742504910672534362390528)), (55431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548510471202749/9671406556917033397649408), (-1305247264933/2417851639229258349412352)), (51987/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78617217339799/37778931862957161709568), (-2283275525733/302231454903657293676544)), (45509/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886306921607505/75557863725914323419136), (-7417244522817/75557863725914323419136)), (147981/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324106148526153/1180591620717411303424), (-2779979296191/2361183241434822606848)), (111053/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202489191701989/73786976294838206464), (-1910027731607/147573952589676412928)), (152807/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910776961076031/36893488147419103232), (-1192861724653/9223372036854775808)), (191173/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910246354422719/4611686018427387904), (-10725799278435/9223372036854775808)), (215295/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795868485172457/576460752303423488), (-334792566829/36028797018963968)), (107789/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192608226094967/144115188075855872), (-585013207597/9007199254740992)), (47237/36028797018963968), by norm_num⟩
  | 4 => ⟨((372167281316215/9007199254740992), (-7006191992399/18014398509481984)), (284059/36028797018963968), by norm_num⟩
  | 3 => ⟨((742765430180841/4503599627370496), (-2183332564853/1125899906842624)), (178095/4503599627370496), by norm_num⟩
  | 2 => ⟨((555111352959279/1125899906842624), (-17393558027589/2251799813685248)), (89467/562949953421312), by norm_num⟩
  | 1 => ⟨((551182135316089/562949953421312), (-12954012435773/562949953421312)), (270505/562949953421312), by norm_num⟩
  | 0 => ⟨((1078753048421665/1125899906842624), (-51089470158425/1125899906842624)), (549463/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1078753048421665/1125899906842624), (-51089470158425/1125899906842624)), (2096035005809593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1031262191657915/1125899906842624), (-97900215357869/1125899906842624)), (2205549/1125899906842624), by norm_num⟩
  | 2 => ⟨((936066562729793/1125899906842624), (-5604449718407/35184372088832)), (8847761/2251799813685248), by norm_num⟩
  | 3 => ⟨((1499346276743391/2251799813685248), (-596416837640981/2251799813685248)), (17530639/2251799813685248), by norm_num⟩
  | 4 => ⟨((420180826435379/1125899906842624), (-49640034577529/140737488355328)), (4078967/281474976710656), by norm_num⟩
  | 5 => ⟨((8369932658509/562949953421312), (-1185628136287671/4503599627370496)), (11843839/562949953421312), by norm_num⟩
  | 6 => ⟨((-1244542698323117/18014398509481984), (-70511615453209/9007199254740992)), (210824375/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89456925/33554432), (-999543385/16777216)), (1/16777216), by norm_num⟩, -9, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-2027835301/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-55433530938261/1125899906842624), (816285224361755/18014398509481984)), (221525211/18014398509481984), by norm_num⟩
  | 1 => ⟨((663038313/4294967296), (-152555561/1073741824)), (167/4294967296), by norm_num⟩
  | 2 => ⟨((-519738199/2147483648), (478337079/2147483648)), (33/536870912), by norm_num⟩
  | 3 => ⟨((543212039/2147483648), (-62492631/268435456)), (139/2147483648), by norm_num⟩
  | 4 => ⟨((-851619103/4294967296), (195945283/1073741824)), (219/4294967296), by norm_num⟩
  | 5 => ⟨((267024677/2147483648), (-491508241/4294967296)), (277/8589934592), by norm_num⟩
  | 6 => ⟨((-1116339107/17179869184), (256853541/4294967296)), (73/4294967296), by norm_num⟩
  | 7 => ⟨((500039259/17179869184), (-920414619/34359738368)), (33/4294967296), by norm_num⟩
  | 8 => ⟨((-391967551/34359738368), (360744339/34359738368)), (209/68719476736), by norm_num⟩
  | 9 => ⟨((1092455101/274877906944), (-1005432701/274877906944)), (147/137438953472), by norm_num⟩
  | 10 => ⟨((-342538665/274877906944), (157626421/137438953472)), (93/274877906944), by norm_num⟩
  | 11 => ⟨((781111275/2199023255552), (-718889791/2199023255552)), (107/1099511627776), by norm_num⟩
  | 12 => ⟨((-816389961/8796093022208), (187839565/2199023255552)), (113/4398046511104), by norm_num⟩
  | 13 => ⟨((393813231/17592186044416), (-724885993/35184372088832)), (55/8796093022208), by norm_num⟩
  | 14 => ⟨((-352799745/70368744177664), (649393097/140737488355328)), (199/140737488355328), by norm_num⟩
  | 15 => ⟨((589974165/562949953421312), (-542978213/562949953421312)), (21/70368744177664), by norm_num⟩
  | 16 => ⟨((-924930291/4503599627370496), (851252523/4503599627370496)), (265/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (3123209015325/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444447869978123/158456325028528675187087900672), (3692314039123/633825300114114700748351602688)), (23141/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944321138279777/19807040628566084398385987584), (2076435240333/19807040628566084398385987584)), (52079/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888348443423309/2475880078570760549798248448), (4411206503037/2475880078570760549798248448)), (110695/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885007243707907/77371252455336267181195264), (4409836245135/154742504910672534362390528)), (55363/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548450519890249/9671406556917033397649408), (2066383013675/4835703278458516698824704)), (51919/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628911711853963/302231454903657293676544), (1807357661719/302231454903657293676544)), (90891/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886223090426185/75557863725914323419136), (5871185434931/75557863725914323419136)), (147757/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296362381578731/4722366482869645213696), (4401004047569/4722366482869645213696)), (13859/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809914531940753/295147905179352825856), (6047506892817/590295810358705651712)), (152535/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821449941253167/73786976294838206464), (944197075553/9223372036854775808)), (95399/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910188967476903/4611686018427387904), (4244897360271/4611686018427387904)), (107413/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591624946233235/1152921504606846976), (2119957385187/288230376151711744)), (107525/576460752303423488), by norm_num⟩
  | 5 => ⟨((149064161283369/18014398509481984), (7408651730683/144115188075855872)), (188421/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488532871509793/36028797018963968), (693163038875/2251799813685248)), (283135/36028797018963968), by norm_num⟩
  | 3 => ⟨((371342814870725/2251799813685248), (13824180872583/9007199254740992)), (177401/4503599627370496), by norm_num⟩
  | 2 => ⟨((555039543695207/1125899906842624), (6882846260249/1125899906842624)), (712261/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102188477200431/1125899906842624), (20502777744349/1125899906842624)), (1075053/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157116154383599/2251799813685248), (40425266989545/1125899906842624)), (2176879/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157116154383599/2251799813685248), (40425266989545/1125899906842624)), (8304134377486418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((515877706625865/562949953421312), (77450931418015/1125899906842624)), (4327013/2251799813685248), by norm_num⟩
  | 2 => ⟨((470077570645313/562949953421312), (35487354278241/281474976710656)), (8525715/2251799813685248), by norm_num⟩
  | 3 => ⟨((1534314102749489/2251799813685248), (237062768174853/1125899906842624)), (16388163/2251799813685248), by norm_num⟩
  | 4 => ⟨((118201267755695/281474976710656), (646112049991227/2251799813685248)), (14617035/1125899906842624), by norm_num⟩
  | 5 => ⟨((423410426360567/4503599627370496), (1085300928895009/4503599627370496)), (41329179/2251799813685248), by norm_num⟩
  | 6 => ⟨((-55433530938261/1125899906842624), (816285224361755/18014398509481984)), (221525211/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-2027835301/33554432)), (1/16777216), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-91975095/33554432), (-2055360113/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-29738610673/70368744177664), (1161925401222757/18014398509481984)), (94623983/9007199254740992), by norm_num⟩
  | 1 => ⟨((721061/536870912), (-880399101/4294967296)), (289/8589934592), by norm_num⟩
  | 2 => ⟨((-9166283/4294967296), (1398977867/4294967296)), (29/536870912), by norm_num⟩
  | 3 => ⟨((4855157/2147483648), (-1482008989/4294967296)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-7714975/4294967296), (588738043/2147483648)), (199/4294967296), by norm_num⟩
  | 5 => ⟨((4903721/4294967296), (-748416477/4294967296)), (255/8589934592), by norm_num⟩
  | 6 => ⟨((-5194763/8589934592), (1585671901/17179869184)), (17/1073741824), by norm_num⟩
  | 7 => ⟨((9433849/34359738368), (-719907237/17179869184)), (249/34359738368), by norm_num⟩
  | 8 => ⟨((-936915/8589934592), (142993997/8589934592)), (199/68719476736), by norm_num⟩
  | 9 => ⟨((5293451/137438953472), (-807897991/137438953472)), (283/274877906944), by norm_num⟩
  | 10 => ⟨((-6729149/549755813888), (513508661/274877906944)), (181/549755813888), by norm_num⟩
  | 11 => ⟨((7776581/2199023255552), (-1186878667/2199023255552)), (211/2199023255552), by norm_num⟩
  | 12 => ⟨((-8238131/8796093022208), (1257321431/8796093022208)), (225/8796093022208), by norm_num⟩
  | 13 => ⟨((8055761/35184372088832), (-614743875/17592186044416)), (111/17592186044416), by norm_num⟩
  | 14 => ⟨((-7314755/140737488355328), (558196893/70368744177664)), (203/140737488355328), by norm_num⟩
  | 15 => ⟨((1549779/140737488355328), (-473061273/281474976710656)), (173/562949953421312), by norm_num⟩
  | 16 => ⟨((-4925281/2251799813685248), (751707095/2251799813685248)), (277/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215521907/10141204801825835211973625643008), (2054672352531/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222217387595553/79228162514264337593543950336), (2428923411425/633825300114114700748351602688)), (11555/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888583591615719/39614081257132168796771975168), (2731890629825/39614081257132168796771975168)), (52005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944143206671041/1237940039285380274899124224), (2901822193519/2475880078570760549798248448)), (1727/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((884976409972819/77371252455336267181195264), (2900909548775/154742504910672534362390528)), (110549/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548393091603629/9671406556917033397649408), (339829172355/1208925819614629174706176)), (103661/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257773558577685/604462909807314587353088), (2377835290519/604462909807314587353088)), (90725/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886142780018057/75557863725914323419136), (3862166494527/75557863725914323419136)), (147467/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296302778413115/4722366482869645213696), (2895036864361/4722366482869645213696)), (27659/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((25308564551853/9223372036854775808), (248631049867/36893488147419103232)), (38045/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455337576457153/18446744073709551616), (1242188873663/18446744073709551616)), (190311/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455066986332535/2305843009213693952), (5584539466051/9223372036854775808)), (214217/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198939697005775/144115188075855872), (5577908279701/1152921504606846976)), (214365/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596211140094357/72057594037927936), (2436609566027/72057594037927936)), (187735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488402214023343/36028797018963968), (1823737781207/9007199254740992)), (281935/36028797018963968), by norm_num⟩
  | 3 => ⟨((742609071745431/4503599627370496), (4546353146879/4503599627370496)), (353001/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109941190475379/2251799813685248), (18107676933035/4503599627370496)), (707753/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102019366634801/1125899906842624), (26967917187879/2251799813685248)), (133253/281474976710656), by norm_num⟩
  | 0 => ⟨((539184463543971/562949953421312), (53165873388909/2251799813685248)), (1074859/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539184463543971/562949953421312), (53165873388909/2251799813685248)), (4100261692527389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2064433762401837/2251799813685248), (101842846767559/2251799813685248)), (4219443/2251799813685248), by norm_num⟩
  | 2 => ⟨((236006480686495/281474976710656), (186737568808995/2251799813685248)), (4059189/1125899906842624), by norm_num⟩
  | 3 => ⟨((783788334604219/1125899906842624), (156572626602849/1125899906842624)), (3740103/562949953421312), by norm_num⟩
  | 4 => ⟨((1047711546072243/2251799813685248), (108997076475297/562949953421312)), (12495061/1125899906842624), by norm_num⟩
  | 5 => ⟨((201530721197885/1125899906842624), (811422008775423/4503599627370496)), (65863477/4503599627370496), by norm_num⟩
  | 6 => ⟨((-29738610673/70368744177664), (1161925401222757/18014398509481984)), (94623983/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-91975095/33554432), (-2055360113/33554432)), (1/16777216), by norm_num⟩, -10, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1040880573/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((789111831266085/18014398509481984), (797262856569049/18014398509481984)), (129403745/9007199254740992), by norm_num⟩
  | 1 => ⟨((-302797913/2147483648), (-38240703/268435456)), (201/4294967296), by norm_num⟩
  | 2 => ⟨((487334441/2147483648), (984736595/4294967296)), (163/2147483648), by norm_num⟩
  | 3 => ⟨((-1045779367/4294967296), (-1056581607/4294967296)), (11/134217728), by norm_num⟩
  | 4 => ⟨((841558481/4294967296), (53140703/268435456)), (285/4294967296), by norm_num⟩
  | 5 => ⟨((-270887225/2147483648), (-273685319/2147483648)), (185/4294967296), by norm_num⟩
  | 6 => ⟨((72662695/1073741824), (293653019/4294967296)), (25/1073741824), by norm_num⟩
  | 7 => ⟨((-534610725/17179869184), (-540132917/17179869184)), (93/8589934592), by norm_num⟩
  | 8 => ⟨((860422769/68719476736), (869310395/68719476736)), (151/34359738368), by norm_num⟩
  | 9 => ⟨((-615465345/137438953472), (-310911357/68719476736)), (109/68719476736), by norm_num⟩
  | 10 => ⟨((49527663/34359738368), (800628041/549755813888)), (283/549755813888), by norm_num⟩
  | 11 => ⟨((-927554311/2199023255552), (-468567681/1099511627776)), (167/1099511627776), by norm_num⟩
  | 12 => ⟨((995227383/8796093022208), (502753727/4398046511104)), (45/1099511627776), by norm_num⟩
  | 13 => ⟨((-246424105/8796093022208), (-497939021/17592186044416)), (359/35184372088832), by norm_num⟩
  | 14 => ⟨((226631027/35184372088832), (457943965/70368744177664)), (83/35184372088832), by norm_num⟩
  | 15 => ⟨((-194532569/140737488355328), (-786167871/562949953421312)), (287/562949953421312), by norm_num⟩
  | 16 => ⟨((78272023/281474976710656), (632644189/2251799813685248)), (233/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (1029761748377/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888843627413467/316912650057057350374175801344), (1217258272757/633825300114114700748351602688)), (2885/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((236065676069543/4951760157141521099596496896), (1369088663709/39614081257132168796771975168)), (25967/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944112392841869/1237940039285380274899124224), (1454244968667/2475880078570760549798248448)), (220737/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769891407862137/154742504910672534362390528), (363445502161/38685626227668133590597632)), (110379/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548335746641133/9671406556917033397649408), (340607235275/2417851639229258349412352)), (103491/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628861805197889/302231454903657293676544), (297908464993/151115727451828646838272)), (181131/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886062042524109/75557863725914323419136), (483871003435/18889465931478580854784)), (294377/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296242599620607/4722366482869645213696), (725403806359/2361183241434822606848)), (110409/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619665992945135/590295810358705651712), (1993552605233/590295810358705651712)), (151841/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821248542633553/73786976294838206464), (2489980552367/73786976294838206464)), (47461/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820154710355019/9223372036854775808), (1399267710405/4611686018427387904)), (106817/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591405898375185/1152921504606846976), (2795173411205/1152921504606846976)), (427417/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298081577357719/36028797018963968), (2441999783361/144115188075855872)), (374157/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488261740413585/36028797018963968), (1827729512911/18014398509481984)), (561571/36028797018963968), by norm_num⟩
  | 3 => ⟨((371262154809287/2251799813685248), (4556157412677/9007199254740992)), (702553/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219561429412157/4503599627370496), (9072934512129/4503599627370496)), (1406881/4503599627370496), by norm_num⟩
  | 1 => ⟨((275450272234295/281474976710656), (13511365554751/2251799813685248)), (1057391/1125899906842624), by norm_num⟩
  | 0 => ⟨((2156042020447789/2251799813685248), (13316531990535/1125899906842624)), (4247557/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156042020447789/2251799813685248), (13316531990535/1125899906842624)), (16203144082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258005165778539/281474976710656), (6375123215603/281474976710656)), (257323/70368744177664), by norm_num⟩
  | 2 => ⟨((1890783305850541/2251799813685248), (93496892196769/2251799813685248)), (15468489/2251799813685248), by norm_num⟩
  | 3 => ⟨((1583764160187971/2251799813685248), (157014279724307/2251799813685248)), (13630793/1125899906842624), by norm_num⟩
  | 4 => ⟨((1102964577918615/2251799813685248), (220866515179351/2251799813685248)), (42149735/2251799813685248), by norm_num⟩
  | 5 => ⟨((1037169321641079/4503599627370496), (432734635131645/4503599627370496)), (99119169/4503599627370496), by norm_num⟩
  | 6 => ⟨((789111831266085/18014398509481984), (797262856569049/18014398509481984)), (129403745/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1040880573/16777216)), (1/8388608), by norm_num⟩, -10, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-526781643/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((541895369103509/9007199254740992), (18750371184831/9007199254740992)), (34955369/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1683757235/8589934592), (-58260459/8589934592)), (219/8589934592), by norm_num⟩
  | 2 => ⟨((1371460905/4294967296), (23727275/2147483648)), (45/1073741824), by norm_num⟩
  | 3 => ⟨((-372362669/1073741824), (-3221073/268435456)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((1213193523/4294967296), (41978267/4294967296)), (81/2147483648), by norm_num⟩
  | 5 => ⟨((-1581080647/8589934592), (-54707699/8589934592)), (213/8589934592), by norm_num⟩
  | 6 => ⟨((1717104461/17179869184), (29707161/8589934592)), (233/17179869184), by norm_num⟩
  | 7 => ⟨((-799213157/17179869184), (-55307885/34359738368)), (219/34359738368), by norm_num⟩
  | 8 => ⟨((650978405/34359738368), (45049607/68719476736)), (45/17179869184), by norm_num⟩
  | 9 => ⟨((-1885289323/274877906944), (-16308441/68719476736)), (263/274877906944), by norm_num⟩
  | 10 => ⟨((1228490923/549755813888), (10626895/137438953472)), (173/549755813888), by norm_num⟩
  | 11 => ⟨((-1455469827/2199023255552), (-25180691/1099511627776)), (207/2199023255552), by norm_num⟩
  | 12 => ⟨((395171767/2199023255552), (54694081/8796093022208)), (227/8796093022208), by norm_num⟩
  | 13 => ⟨((-1584624943/35184372088832), (-54830337/35184372088832)), (229/35184372088832), by norm_num⟩
  | 14 => ⟨((1475103155/140737488355328), (51040723/140737488355328)), (215/140737488355328), by norm_num⟩
  | 15 => ⟨((-320401899/140737488355328), (-22172747/281474976710656)), (189/562949953421312), by norm_num⟩
  | 16 => ⟨((521950159/1125899906842624), (36120475/2251799813685248)), (155/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (22527145335/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777635962040299/633825300114114700748351602688), (53254690027/633825300114114700748351602688)), (92205/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472116940337531/9903520314283042199192993792), (14974272279/9903520314283042199192993792)), (25933/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944081805683495/1237940039285380274899124224), (31811213935/1237940039285380274899124224)), (220431/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884915159385625/77371252455336267181195264), (63601931345/154742504910672534362390528)), (13777/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548278566102933/9671406556917033397649408), (59605042423/9671406556917033397649408)), (3229/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1257673667832789/604462909807314587353088), (52132654427/604462909807314587353088)), (90413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471495263802889/18889465931478580854784), (42337395057/37778931862957161709568)), (293843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296182007157025/4722366482869645213696), (63470438249/4722366482869645213696)), (6887/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1619582918537313/590295810358705651712), (87213956131/590295810358705651712)), (303031/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910572529718185/36893488147419103232), (108930673621/73786976294838206464)), (378793/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455009696409369/2305843009213693952), (122427815707/9223372036854775808)), (426149/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198911323714281/144115188075855872), (122279003493/1152921504606846976)), (213079/576460752303423488), by norm_num⟩
  | 5 => ⟨((74514131602647/9007199254740992), (53413479323/72057594037927936)), (372899/144115188075855872), by norm_num⟩
  | 4 => ⟨((372028203221397/9007199254740992), (159906709001/36028797018963968)), (69921/4503599627370496), by norm_num⟩
  | 3 => ⟨((1484864861669405/9007199254740992), (199300730059/9007199254740992)), (43703/562949953421312), by norm_num⟩
  | 2 => ⟨((2219201080224533/4503599627370496), (396858956209/4503599627370496)), (1398615/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203079431044733/2251799813685248), (590951241061/2251799813685248)), (1049123/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155066811936649/2251799813685248), (582333815495/1125899906842624)), (4197921/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2155066811936649/2251799813685248), (582333815495/1125899906842624)), (16013797768599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062488672054431/2251799813685248), (2229271486061/2251799813685248)), (2009879/562949953421312), by norm_num⟩
  | 2 => ⟨((1889090907126297/2251799813685248), (2041854324257/1125899906842624)), (7371585/1125899906842624), by norm_num⟩
  | 3 => ⟨((792398986140459/1125899906842624), (6851849643451/2251799813685248)), (6197575/562949953421312), by norm_num⟩
  | 4 => ⟨((1115346777203895/2251799813685248), (9644549533507/2251799813685248)), (1095165/70368744177664), by norm_num⟩
  | 5 => ⟨((2209619893426781/9007199254740992), (9554150572715/2251799813685248)), (4377125/281474976710656), by norm_num⟩
  | 6 => ⟨((541895369103509/9007199254740992), (18750371184831/9007199254740992)), (34955369/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-526781643/8388608)), (1/8388608), by norm_num⟩, -10, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-532883645/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((807690520506171/18014398509481984), (-335232372947239/9007199254740992)), (114179573/18014398509481984), by norm_num⟩
  | 1 => ⟨((-317337059/2147483648), (263421825/2147483648)), (23/1073741824), by norm_num⟩
  | 2 => ⟨((522945589/2147483648), (-434097681/2147483648)), (153/4294967296), by norm_num⟩
  | 3 => ⟨((-1149028901/4294967296), (476905047/2147483648)), (85/2147483648), by norm_num⟩
  | 4 => ⟨((946752953/4294967296), (-392950309/2147483648)), (71/2147483648), by norm_num⟩
  | 5 => ⟨((-624068657/4294967296), (259020023/2147483648)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((85701187/1073741824), (-569125161/8589934592)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((-645616301/17179869184), (33495423/1073741824)), (103/17179869184), by norm_num⟩
  | 8 => ⟨((1063923003/68719476736), (-55197725/4294967296)), (43/17179869184), by norm_num⟩
  | 9 => ⟨((-194806481/34359738368), (20213633/4294967296)), (1/1073741824), by norm_num⟩
  | 10 => ⟨((1027280611/549755813888), (-852746711/549755813888)), (171/549755813888), by norm_num⟩
  | 11 => ⟨((-4809303/8589934592), (255501277/549755813888)), (13/137438953472), by norm_num⟩
  | 12 => ⟨((42268475/274877906944), (-561393685/4398046511104)), (29/1099511627776), by norm_num⟩
  | 13 => ⟨((-685833837/17592186044416), (284655693/8796093022208)), (119/17592186044416), by norm_num⟩
  | 14 => ⟨((645827555/70368744177664), (-268051065/35184372088832)), (57/35184372088832), by norm_num⟩
  | 15 => ⟨((-1135222541/562949953421312), (942349421/562949953421312)), (203/562949953421312), by norm_num⟩
  | 16 => ⟨((935377075/2251799813685248), (-776457491/2251799813685248)), (85/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-902485384215/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888792617691011/316912650057057350374175801344), (-533345366345/316912650057057350374175801344)), (92305/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888410674524247/39614081257132168796771975168), (-599867179739/19807040628566084398385987584)), (103851/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051464634701/1237940039285380274899124224), (-1274348355743/2475880078570760549798248448)), (55175/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769769605965405/154742504910672534362390528), (-636966503753/77371252455336267181195264)), (55179/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548221615257337/9671406556917033397649408), (-596935537437/4835703278458516698824704)), (51735/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257623803294935/604462909807314587353088), (-130524535287/75557863725914323419136)), (45273/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885899964399623/75557863725914323419136), (-1695992704883/75557863725914323419136)), (73577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296121135816805/4722366482869645213696), (-635636002665/2361183241434822606848)), (55191/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619499134111139/590295810358705651712), (-218353218473/73786976294838206464)), (18975/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910520099848111/36893488147419103232), (-545443441437/18446744073709551616)), (189787/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819920641244369/9223372036854775808), (-1226040023711/4611686018427387904)), (213563/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795586112275103/576460752303423488), (-153066520331/72057594037927936)), (53407/288230376151711744), by norm_num⟩
  | 5 => ⟨((149015286091481/18014398509481984), (-534885877209/36028797018963968)), (93499/72057594037927936), by norm_num⟩
  | 4 => ⟨((743978297583957/18014398509481984), (-1601275985823/18014398509481984)), (70161/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484668733361189/9007199254740992), (-3991381737061/9007199254740992)), (351065/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109403138428657/2251799813685248), (-7947448662617/4503599627370496)), (702909/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101240467396875/1125899906842624), (-5916634672505/1125899906842624)), (1056329/2251799813685248), by norm_num⟩
  | 0 => ⟨((538461276402503/562949953421312), (-11658607525859/1125899906842624)), (530149/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538461276402503/562949953421312), (-11658607525859/1125899906842624)), (2022357942821311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2059910040960149/2251799813685248), (-44605803065067/2251799813685248)), (512577/281474976710656), by norm_num⟩
  | 2 => ⟨((1883488786794169/2251799813685248), (-10201166757853/281474976710656)), (7664813/2251799813685248), by norm_num⟩
  | 3 => ⟨((1572462127873739/2251799813685248), (-34130535199199/562949953421312)), (6688921/1125899906842624), by norm_num⟩
  | 4 => ⟨((1089794409678587/2251799813685248), (-190670498074049/2251799813685248)), (20305999/2251799813685248), by norm_num⟩
  | 5 => ⟨((1022556809476511/4503599627370496), (-92278026505235/1125899906842624)), (46187267/4503599627370496), by norm_num⟩
  | 6 => ⟨((807690520506171/18014398509481984), (-335232372947239/9007199254740992)), (114179573/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-532883645/8388608)), (1/16777216), by norm_num⟩, -10, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile010Terms3
