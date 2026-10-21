/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile005Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2697/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2697/160))
  have he : value ((15/16), (2697/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24308947/8388608), (-1748299467/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-262183251178933/18014398509481984), (-958116341611937/18014398509481984)), (86519679/9007199254740992), by norm_num⟩
  | 1 => ⟨((24152385/536870912), (706095287/4294967296)), (257/8589934592), by norm_num⟩
  | 2 => ⟨((-149312095/2147483648), (-545642627/2147483648)), (201/4294967296), by norm_num⟩
  | 3 => ⟨((307686683/4294967296), (140550377/536870912)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((-118884075/2147483648), (-217223591/1073741824)), (163/4294967296), by norm_num⟩
  | 5 => ⟨((146990289/4294967296), (1074315747/8589934592)), (203/8589934592), by norm_num⟩
  | 6 => ⟨((-302902149/17179869184), (-1106918527/17179869184)), (211/17179869184), by norm_num⟩
  | 7 => ⟨((267509543/34359738368), (977580617/34359738368)), (47/8589934592), by norm_num⟩
  | 8 => ⟨((-413441677/137438953472), (-755435797/68719476736)), (293/137438953472), by norm_num⟩
  | 9 => ⟨((283992395/274877906944), (259453791/68719476736)), (203/274877906944), by norm_num⟩
  | 10 => ⟨((-87783255/274877906944), (-320793073/274877906944)), (253/1099511627776), by norm_num⟩
  | 11 => ⟨((394678935/4398046511104), (1442305465/4398046511104)), (143/2199023255552), by norm_num⟩
  | 12 => ⟨((-6354007/274877906944), (-46439869/549755813888)), (297/17592186044416), by norm_num⟩
  | 13 => ⟨((386766875/70368744177664), (1413391819/70368744177664)), (71/17592186044416), by norm_num⟩
  | 14 => ⟨((-170787547/140737488355328), (-1248244033/281474976710656)), (253/281474976710656), by norm_num⟩
  | 15 => ⟨((281552831/1125899906842624), (64306255/70368744177664)), (105/562949953421312), by norm_num⟩
  | 16 => ⟨((-435145877/9007199254740992), (-795093457/4503599627370496)), (327/9007199254740992), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (-1197036206183/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444374144178863/158456325028528675187087900672), (-2829410856383/633825300114114700748351602688)), (92479/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888310758019057/39614081257132168796771975168), (-3182290136805/39614081257132168796771975168)), (52029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1887996527855155/2475880078570760549798248448), (-1690091846253/1237940039285380274899124224)), (110581/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769662934788849/154742504910672534362390528), (-1689529839169/77371252455336267181195264)), (110605/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774060662339089/4835703278458516698824704), (-3166674642281/9671406556917033397649408)), (103717/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257535762992639/604462909807314587353088), (-2769647022065/604462909807314587353088)), (45389/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((942878181610945/37778931862957161709568), (-562305011097/9444732965739290427392)), (147559/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296012966856071/4722366482869645213696), (-1685937190399/2361183241434822606848)), (110711/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619349642378481/590295810358705651712), (-4633151338191/590295810358705651712)), (76147/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820852198035155/73786976294838206464), (-5786678861973/73786976294838206464)), (95233/36893488147419103232), by norm_num⟩
  | 7 => ⟨((454926894862743/2305843009213693952), (-6503474125949/9223372036854775808)), (53603/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1590957218008097/1152921504606846976), (-3247654188499/576460752303423488)), (214583/1152921504606846976), by norm_num⟩
  | 5 => ⟨((297982994310631/36028797018963968), (-1418555093215/36028797018963968)), (93977/72057594037927936), by norm_num⟩
  | 4 => ⟨((46489587001751/1125899906842624), (-8493011637389/36028797018963968)), (282317/36028797018963968), by norm_num⟩
  | 3 => ⟨((742149453644471/4503599627370496), (-10584273821509/9007199254740992)), (44197/1125899906842624), by norm_num⟩
  | 2 => ⟨((1109022048008291/2251799813685248), (-21072844549241/4503599627370496)), (709191/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201281891736215/2251799813685248), (-15685474380457/1125899906842624)), (534455/1125899906842624), by norm_num⟩
  | 0 => ⟨((1075613605886379/1125899906842624), (-15448561599631/562949953421312)), (134901/140737488355328), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1075613605886379/1125899906842624), (-15448561599631/562949953421312)), (514606476366949037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2053450737353139/2251799813685248), (-29517158580349/562949953421312)), (1060623/562949953421312), by norm_num⟩
  | 2 => ⟨((1866382483373399/2251799813685248), (-13458574488509/140737488355328)), (8182481/2251799813685248), by norm_num⟩
  | 3 => ⟨((1526340595276473/2251799813685248), (-356960294944447/2251799813685248)), (15128905/2251799813685248), by norm_num⟩
  | 4 => ⟨((122251928614931/281474976710656), (-483917785021835/2251799813685248)), (12653115/1125899906842624), by norm_num⟩
  | 5 => ⟨((641564807097031/4503599627370496), (-840712495317815/4503599627370496)), (16429533/1125899906842624), by norm_num⟩
  | 6 => ⟨((-262183251178933/18014398509481984), (-958116341611937/18014398509481984)), (86519679/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-1748299467/33554432)), (1/16777216), by norm_num⟩, -8, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-98634119/33554432), (-443360367/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-810082462884377/18014398509481984), (-501584114365817/18014398509481984)), (174381405/18014398509481984), by norm_num⟩
  | 1 => ⟨((605585307/4294967296), (749928517/8589934592)), (263/8589934592), by norm_num⟩
  | 2 => ⟨((-474702307/2147483648), (-146962283/1073741824)), (13/268435456), by norm_num⟩
  | 3 => ⟨((992284225/4294967296), (38399949/268435456)), (219/4294967296), by norm_num⟩
  | 4 => ⟨((-388912681/2147483648), (-60201409/536870912)), (173/4294967296), by norm_num⟩
  | 5 => ⟨((975546769/8589934592), (604035743/8589934592)), (219/8589934592), by norm_num⟩
  | 6 => ⟨((-254901771/4294967296), (-631316859/17179869184)), (231/17179869184), by norm_num⟩
  | 7 => ⟨((228355151/8589934592), (282784337/17179869184)), (13/2147483648), by norm_num⟩
  | 8 => ⟨((-716006255/68719476736), (-221667163/34359738368)), (165/68719476736), by norm_num⟩
  | 9 => ⟨((498896327/137438953472), (617809873/274877906944)), (29/34359738368), by norm_num⟩
  | 10 => ⟨((-625714619/549755813888), (-774855713/1099511627776)), (293/1099511627776), by norm_num⟩
  | 11 => ⟨((178356779/549755813888), (441737383/2199023255552)), (169/2199023255552), by norm_num⟩
  | 12 => ⟨((-745648865/8796093022208), (-28855521/549755813888)), (89/4398046511104), by norm_num⟩
  | 13 => ⟨((719377755/35184372088832), (445421879/35184372088832)), (173/35184372088832), by norm_num⟩
  | 14 => ⟨((-1288917023/281474976710656), (-798067271/281474976710656)), (313/281474976710656), by norm_num⟩
  | 15 => ⟨((1077704499/1125899906842624), (83411177/140737488355328)), (33/140737488355328), by norm_num⟩
  | 16 => ⟨((-105598007/562949953421312), (-261535263/2251799813685248)), (209/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (-3370106321135/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888714102813295/316912650057057350374175801344), (-1991326297585/316912650057057350374175801344)), (92593/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888233631796357/39614081257132168796771975168), (-4479336679533/39614081257132168796771975168)), (104193/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887914295441401/2475880078570760549798248448), (-18585417351/9671406556917033397649408)), (55367/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769580381284091/154742504910672534362390528), (-1189065115973/38685626227668133590597632)), (110767/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548043589933537/9671406556917033397649408), (-4457287980383/9671406556917033397649408)), (103879/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257467404623239/604462909807314587353088), (-1949210710657/302231454903657293676544)), (90929/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885644643271777/75557863725914323419136), (-6331738247897/75557863725914323419136)), (147825/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((647964309885167/2361183241434822606848), (-2373004030115/2361183241434822606848)), (55463/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404808190316351/147573952589676412928), (-6521220751377/590295810358705651712)), (152617/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910352371690937/36893488147419103232), (-8144719921383/73786976294838206464)), (190911/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909769918179301/4611686018427387904), (-9153458913617/9223372036854775808)), (26871/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795393580169463/576460752303423488), (-9141781077035/1152921504606846976)), (215209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((9310785791947/1125899906842624), (-7985935872075/144115188075855872)), (47145/36028797018963968), by norm_num⟩
  | 4 => ⟨((743717260295731/18014398509481984), (-5976348068605/18014398509481984)), (283415/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483999578575539/9007199254740992), (-14895090999769/9007199254740992)), (355223/9007199254740992), by norm_num⟩
  | 2 => ⟨((1108709314942623/2251799813685248), (-14826590609781/2251799813685248)), (178329/1125899906842624), by norm_num⟩
  | 1 => ⟨((275034666387453/281474976710656), (-44138447213965/2251799813685248)), (1077175/2251799813685248), by norm_num⟩
  | 0 => ⟨((537239146219461/562949953421312), (-5432415625573/140737488355328)), (17057/17592186044416), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((537239146219461/562949953421312), (-5432415625573/140737488355328)), (65067291326874489/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1023727669740111/1125899906842624), (-165897877911453/2251799813685248)), (4335713/2251799813685248), by norm_num⟩
  | 2 => ⟨((1849432278997719/2251799813685248), (-301686227944347/2251799813685248)), (4261687/1125899906842624), by norm_num⟩
  | 3 => ⟨((23102250490871/35184372088832), (-495557593262443/2251799813685248)), (4071141/562949953421312), by norm_num⟩
  | 4 => ⟨((430880914191757/1125899906842624), (-650771633684265/2251799813685248)), (14276307/1125899906842624), by norm_num⟩
  | 5 => ⟨((35430517370073/562949953421312), (-996198950715905/4503599627370496)), (76715141/4503599627370496), by norm_num⟩
  | 6 => ⟨((-810082462884377/18014398509481984), (-501584114365817/18014398509481984)), (174381405/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-443360367/8388608)), (1/16777216), by norm_num⟩, -8, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-99972929/33554432), (-1797513267/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1806787108930751/36028797018963968), (297132857160271/36028797018963968)), (314040137/36028797018963968), by norm_num⟩
  | 1 => ⟨((684507691/4294967296), (-225139669/8589934592)), (15/536870912), by norm_num⟩
  | 2 => ⟨((-135962643/536870912), (178876497/4294967296)), (193/4294967296), by norm_num⟩
  | 3 => ⟨((1152257595/4294967296), (-189493045/4294967296)), (207/4294967296), by norm_num⟩
  | 4 => ⟨((-1830968331/8589934592), (301109549/8589934592)), (331/8589934592), by norm_num⟩
  | 5 => ⟨((1163783183/8589934592), (-191388471/8589934592)), (53/2147483648), by norm_num⟩
  | 6 => ⟨((-1232855201/17179869184), (202747621/17179869184)), (113/8589934592), by norm_num⟩
  | 7 => ⟨((279862871/8589934592), (-92048979/17179869184)), (207/34359738368), by norm_num⟩
  | 8 => ⟨((-889419269/68719476736), (146268305/68719476736)), (331/137438953472), by norm_num⟩
  | 9 => ⟨((157034573/34359738368), (-103299677/137438953472)), (235/274877906944), by norm_num⟩
  | 10 => ⟨((-399251461/274877906944), (262633547/1099511627776)), (301/1099511627776), by norm_num⟩
  | 11 => ⟨((922794643/2199023255552), (-151757009/2199023255552)), (11/137438953472), by norm_num⟩
  | 12 => ⟨((-977563683/8796093022208), (160763981/8796093022208)), (47/2199023255552), by norm_num⟩
  | 13 => ⟨((955923079/35184372088832), (-157205103/35184372088832)), (185/35184372088832), by norm_num⟩
  | 14 => ⟨((-433996429/70368744177664), (285489303/281474976710656)), (169/140737488355328), by norm_num⟩
  | 15 => ⟨((367803737/281474976710656), (-120973383/562949953421312)), (9/35184372088832), by norm_num⟩
  | 16 => ⟨((-1168900075/4503599627370496), (96114981/2251799813685248)), (231/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (3879956307815/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777364016015141/633825300114114700748351602688), (2292434955609/316912650057057350374175801344)), (23163/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888161287941391/39614081257132168796771975168), (2578316612015/19807040628566084398385987584)), (104263/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((471959312398951/618970019642690137449562112), (2738627644089/1237940039285380274899124224)), (55407/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769503132662535/154742504910672534362390528), (5475379849241/154742504910672534362390528)), (110851/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547970954120337/9671406556917033397649408), (2565588282663/4835703278458516698824704)), (25991/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628701816651255/302231454903657293676544), (4487788137095/604462909807314587353088)), (711/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1885540612303301/75557863725914323419136), (7288923384603/75557863725914323419136)), (36991/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1295850244815855/4722366482869645213696), (5463428199793/4722366482869645213696)), (111039/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101195276570241/36893488147419103232), (7506911956691/590295810358705651712)), (76393/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910284234523913/36893488147419103232), (9375692000269/73786976294838206464)), (23893/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1819385356044821/9223372036854775808), (2634183211201/2305843009213693952)), (215259/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99414451223531/72057594037927936), (2630773419921/288230376151711744)), (215537/1152921504606846976), by norm_num⟩
  | 5 => ⟨((148955311988729/18014398509481984), (2298094733267/36028797018963968)), (47227/36028797018963968), by norm_num⟩
  | 4 => ⟨((185903016508877/4503599627370496), (859872024059/2251799813685248)), (283989/36028797018963968), by norm_num⟩
  | 3 => ⟨((741865459668817/4503599627370496), (4285988145677/2251799813685248)), (356085/9007199254740992), by norm_num⟩
  | 2 => ⟨((1108432209116369/2251799813685248), (34127801952465/4503599627370496)), (715475/4503599627370496), by norm_num⟩
  | 1 => ⟨((2199404225497755/2251799813685248), (50792706454383/2251799813685248)), (33797/70368744177664), by norm_num⟩
  | 0 => ⟨((1073522938135321/1125899906842624), (24999248797813/562949953421312)), (1098171/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1073522938135321/1125899906842624), (24999248797813/562949953421312)), (4189189915183639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2042724476575715/2251799813685248), (47672562822861/562949953421312)), (2191703/1125899906842624), by norm_num⟩
  | 2 => ⟨((1836913072878559/2251799813685248), (345970047061967/2251799813685248)), (2173809/562949953421312), by norm_num⟩
  | 3 => ⟨((361328118963843/562949953421312), (564452397953141/2251799813685248)), (16858235/2251799813685248), by norm_num⟩
  | 4 => ⟨((393090369878587/1125899906842624), (724584918987997/2251799813685248)), (30092453/2251799813685248), by norm_num⟩
  | 5 => ⟨((41325543316393/2251799813685248), (2023820071979101/9007199254740992)), (80757881/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1806787108930751/36028797018963968), (297132857160271/36028797018963968)), (314040137/36028797018963968), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-1797513267/33554432)), (1/16777216), by norm_num⟩, -9, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-50628539/16777216), (-1820602265/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-145204203064775/4503599627370496), (331316055117781/9007199254740992)), (162444543/18014398509481984), by norm_num⟩
  | 1 => ⟨((891483877/8589934592), (-1017060509/8589934592)), (251/8589934592), by norm_num⟩
  | 2 => ⟨((-717393975/4294967296), (818447871/4294967296)), (51/1073741824), by norm_num⟩
  | 3 => ⟨((769734041/4294967296), (-878160689/4294967296)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-309709787/2147483648), (706672553/4294967296)), (179/4294967296), by norm_num⟩
  | 5 => ⟨((797533877/8589934592), (-909876479/8589934592)), (29/1073741824), by norm_num⟩
  | 6 => ⟨((-855720839/17179869184), (976259801/17179869184)), (251/17179869184), by norm_num⟩
  | 7 => ⟨((786988321/34359738368), (-897845449/34359738368)), (233/34359738368), by norm_num⟩
  | 8 => ⟨((-158326105/17179869184), (722513253/68719476736)), (189/68719476736), by norm_num⟩
  | 9 => ⟨((226503143/68719476736), (-1033635753/274877906944)), (273/274877906944), by norm_num⟩
  | 10 => ⟨((-583268393/549755813888), (166357257/137438953472)), (89/274877906944), by norm_num⟩
  | 11 => ⟨((682715829/2199023255552), (-778884877/2199023255552)), (105/1099511627776), by norm_num⟩
  | 12 => ⟨((-366262913/4398046511104), (417855617/4398046511104)), (227/8796093022208), by norm_num⟩
  | 13 => ⟨((725510669/35184372088832), (-1616617/68719476736)), (227/35184372088832), by norm_num⟩
  | 14 => ⟨((-667236787/140737488355328), (380612709/70368744177664)), (105/70368744177664), by norm_num⟩
  | 15 => ⟨((143183491/140737488355328), (-163352673/140737488355328)), (91/281474976710656), by norm_num⟩
  | 16 => ⟨((-230444939/1125899906842624), (262905985/1125899906842624)), (295/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (745905431349/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777309721187045/633825300114114700748351602688), (3525465518453/633825300114114700748351602688)), (23137/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944050235987699/19807040628566084398385987584), (991278108787/9903520314283042199192993792)), (104139/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887772991680045/2475880078570760549798248448), (4211634526201/2475880078570760549798248448)), (55337/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884719639099561/77371252455336267181195264), (526271940313/19342813113834066795298816)), (110703/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((773955759427329/4835703278458516698824704), (493186242581/1208925819614629174706176)), (103815/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257352055317735/604462909807314587353088), (3450754738273/604462909807314587353088)), (45435/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885457599445137/75557863725914323419136), (700571691867/9444732965739290427392)), (18465/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((323947171368723/1180591620717411303424), (4200891485135/4722366482869645213696)), (110841/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619040917347843/590295810358705651712), (5772103054271/590295810358705651712)), (152489/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910232892938899/36893488147419103232), (7208949249491/73786976294838206464)), (190735/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227409021544883/1152921504606846976), (2025394592487/2305843009213693952)), (53687/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198815118421809/144115188075855872), (8090977499317/1152921504606846976)), (107481/576460752303423488), by norm_num⟩
  | 5 => ⟨((595774636690671/72057594037927936), (7067694513339/144115188075855872)), (47083/36028797018963968), by norm_num⟩
  | 4 => ⟨((1487090805192075/36028797018963968), (661109880659/2251799813685248)), (282981/36028797018963968), by norm_num⟩
  | 3 => ⟨((1483575593099245/9007199254740992), (13180661393745/9007199254740992)), (88643/2251799813685248), by norm_num⟩
  | 2 => ⟨((138536721530803/281474976710656), (3279631816491/562949953421312)), (355843/2251799813685248), by norm_num⟩
  | 1 => ⟨((1099536300137613/1125899906842624), (39046100426765/2251799813685248)), (134239/281474976710656), by norm_num⟩
  | 0 => ⟨((2146712820612439/2251799813685248), (19215348457955/562949953421312)), (1086741/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2146712820612439/2251799813685248), (19215348457955/562949953421312)), (4145587925437545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((127744155817845/140737488355328), (146548852652115/2251799813685248)), (4292477/2251799813685248), by norm_num⟩
  | 2 => ⟨((461417258430907/562949953421312), (133018996479835/1125899906842624)), (1043885/281474976710656), by norm_num⟩
  | 3 => ⟨((1481356356846453/2251799813685248), (54513958391805/281474976710656)), (7831529/1125899906842624), by norm_num⟩
  | 4 => ⟨((222513482057553/562949953421312), (35862245973101/140737488355328)), (13337515/1125899906842624), by norm_num⟩
  | 5 => ⟨((102796486763217/1125899906842624), (226800501249021/1125899906842624)), (8670451/562949953421312), by norm_num⟩
  | 6 => ⟨((-145204203064775/4503599627370496), (331316055117781/9007199254740992)), (162444543/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-1820602265/33554432)), (1/16777216), by norm_num⟩, -9, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-102490855/33554432), (-921392787/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-99454758232715/36028797018963968), (1695768694328253/36028797018963968)), (282204503/36028797018963968), by norm_num⟩
  | 1 => ⟨((4828471/536870912), (-1317257431/8589934592)), (221/8589934592), by norm_num⟩
  | 2 => ⟨((-62926499/4294967296), (1072937969/4294967296)), (91/2147483648), by norm_num⟩
  | 3 => ⟨((68340203/4294967296), (-1165245161/4294967296)), (199/4294967296), by norm_num⟩
  | 4 => ⟨((-111329489/8589934592), (1898240613/8589934592)), (163/4294967296), by norm_num⟩
  | 5 => ⟨((72544445/8589934592), (-618465117/4294967296)), (107/4294967296), by norm_num⟩
  | 6 => ⟨((-39392801/8589934592), (671673019/8589934592)), (117/8589934592), by norm_num⟩
  | 7 => ⟨((73340313/34359738368), (-312625077/8589934592)), (55/8589934592), by norm_num⟩
  | 8 => ⟨((-59737455/68719476736), (1018562681/68719476736)), (181/68719476736), by norm_num⟩
  | 9 => ⟨((43251199/137438953472), (-1474922465/274877906944)), (33/34359738368), by norm_num⟩
  | 10 => ⟨((-112733265/1099511627776), (1922175911/1099511627776)), (173/549755813888), by norm_num⟩
  | 11 => ⟨((33390533/1099511627776), (-1138660851/2199023255552)), (207/2199023255552), by norm_num⟩
  | 12 => ⟨((-72526387/8796093022208), (618311163/4398046511104)), (227/8796093022208), by norm_num⟩
  | 13 => ⟨((18176767/8796093022208), (-309925763/8796093022208)), (229/35184372088832), by norm_num⟩
  | 14 => ⟨((-67681899/140737488355328), (1154020635/140737488355328)), (107/70368744177664), by norm_num⟩
  | 15 => ⟨((918809/8796093022208), (-2005285673/1125899906842624)), (187/562949953421312), by norm_num⟩
  | 16 => ⟨((-47897095/2251799813685248), (1633353577/4503599627370496)), (307/4503599627370496), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (2122446761927/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777256424954449/633825300114114700748351602688), (1253871768395/316912650057057350374175801344)), (92447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472010176864191/9903520314283042199192993792), (2820471384279/39614081257132168796771975168)), (26005/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1887709754018291/2475880078570760549798248448), (1497908668647/1237940039285380274899124224)), (27635/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769376335070499/154742504910672534362390528), (2994767692357/154742504910672534362390528)), (3455/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1547852822338135/9671406556917033397649408), (2806479935497/9671406556917033397649408)), (12959/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257301008222855/604462909807314587353088), (1227277849107/302231454903657293676544)), (5671/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885375232928333/75557863725914323419136), (3986564926839/75557863725914323419136)), (73743/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40491481931767/147573952589676412928), (1494048874679/2361183241434822606848)), (110651/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1618957509335293/590295810358705651712), (4105669354611/590295810358705651712)), (152203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910181383994397/36893488147419103232), (5127642808939/73786976294838206464)), (95171/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909578990834593/4611686018427387904), (2881246906661/4611686018427387904)), (214257/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795204441001597/576460752303423488), (5754872362517/1152921504606846976)), (107205/576460752303423488), by norm_num⟩
  | 5 => ⟨((595726799996387/72057594037927936), (5026951522005/144115188075855872)), (46945/36028797018963968), by norm_num⟩
  | 4 => ⟨((1486952044840129/36028797018963968), (940416811581/4503599627370496)), (141007/18014398509481984), by norm_num⟩
  | 3 => ⟨((1483410414538125/9007199254740992), (4687162458199/4503599627370496)), (11035/281474976710656), by norm_num⟩
  | 2 => ⟨((1108140921467581/2251799813685248), (9329698194203/2251799813685248)), (354027/2251799813685248), by norm_num⟩
  | 1 => ⟨((1099337564487257/1125899906842624), (27766924899877/2251799813685248)), (266659/562949953421312), by norm_num⟩
  | 0 => ⟨((67067464807971/70368744177664), (54650933800129/2251799813685248)), (1075799/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((67067464807971/70368744177664), (54650933800129/2251799813685248)), (4103847507957076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1022073800541011/1125899906842624), (104174079620035/2251799813685248)), (4205755/2251799813685248), by norm_num⟩
  | 2 => ⟨((462706226239085/562949953421312), (189135103090463/2251799813685248)), (8024973/2251799813685248), by norm_num⟩
  | 3 => ⟨((1505365051095711/2251799813685248), (155456074325017/1125899906842624)), (3635009/562949953421312), by norm_num⟩
  | 4 => ⟨((60214543709031/140737488355328), (25981232861729/140737488355328)), (11727835/1125899906842624), by norm_num⟩
  | 5 => ⟨((670926695663961/4503599627370496), (177857155195749/1125899906842624)), (14365609/1125899906842624), by norm_num⟩
  | 6 => ⟨((-99454758232715/36028797018963968), (1695768694328253/36028797018963968)), (282204503/36028797018963968), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-921392787/16777216)), (1/16777216), by norm_num⟩, -9, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-103678063/33554432), (-1864131575/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((447616947819807/18014398509481984), (343415518473845/9007199254740992)), (106259921/18014398509481984), by norm_num⟩
  | 1 => ⟨((-703464717/8589934592), (-539704097/4294967296)), (169/8589934592), by norm_num⟩
  | 2 => ⟨((579626237/4294967296), (444694165/2147483648)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-636784507/4294967296), (-977092949/4294967296)), (157/4294967296), by norm_num⟩
  | 4 => ⟨((524684463/4294967296), (805084741/4294967296)), (131/4294967296), by norm_num⟩
  | 5 => ⟨((-345854879/4294967296), (-265342797/2147483648)), (175/8589934592), by norm_num⟩
  | 6 => ⟨((94990105/2147483648), (583017715/8589934592)), (97/8589934592), by norm_num⟩
  | 7 => ⟨((-715592891/34359738368), (-1098017873/34359738368)), (185/34359738368), by norm_num⟩
  | 8 => ⟨((294809679/34359738368), (452360973/34359738368)), (77/34359738368), by norm_num⟩
  | 9 => ⟨((-1686883/536870912), (-662625765/137438953472)), (57/68719476736), by norm_num⟩
  | 10 => ⟨((569312377/549755813888), (436781285/274877906944)), (19/68719476736), by norm_num⟩
  | 11 => ⟨((-682312989/2199023255552), (-1046952627/2199023255552)), (23/274877906944), by norm_num⟩
  | 12 => ⟨((374798717/4398046511104), (575097511/4398046511104)), (51/2199023255552), by norm_num⟩
  | 13 => ⟨((-760169495/35184372088832), (-1166416971/35184372088832)), (209/35184372088832), by norm_num⟩
  | 14 => ⟨((357913521/70368744177664), (549188579/70368744177664)), (199/140737488355328), by norm_num⟩
  | 15 => ⟨((-157283277/140737488355328), (-965352515/562949953421312)), (177/562949953421312), by norm_num⟩
  | 16 => ⟨((518380023/2251799813685248), (397705551/1125899906842624)), (147/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (1293776808703/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777204093822865/633825300114114700748351602688), (382138050403/158456325028528675187087900672)), (92351/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1887981964757013/39614081257132168796771975168), (1719167363765/39614081257132168796771975168)), (103905/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887647515537349/2475880078570760549798248448), (1826039979655/2475880078570760549798248448)), (110411/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769314293921737/154742504910672534362390528), (1825393103789/154742504910672534362390528)), (110423/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193474358530377/1208925819614629174706176), (1710619042419/9671406556917033397649408)), (103535/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257250507664641/604462909807314587353088), (1496105022337/604462909807314587353088)), (90607/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942646780736377/37778931862957161709568), (1214941980275/37778931862957161709568)), (147261/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((323916627685931/1180591620717411303424), (1821287855607/4722366482869645213696)), (27617/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202359289047703/73786976294838206464), (2502443892005/590295810358705651712)), (75965/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227532450502215/9223372036854775808), (3125316952417/73786976294838206464)), (94983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819043064175181/9223372036854775808), (1756110460787/4611686018427387904)), (106893/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590295388486203/1152921504606846976), (3507526072227/1152921504606846976)), (213879/1152921504606846976), by norm_num⟩
  | 5 => ⟨((148919486293821/18014398509481984), (765952948929/36028797018963968)), (93625/72057594037927936), by norm_num⟩
  | 4 => ⟨((1486808662803143/36028797018963968), (4585191095369/36028797018963968)), (281085/36028797018963968), by norm_num⟩
  | 3 => ⟨((92702295590127/562949953421312), (5713113213575/9007199254740992)), (175863/4503599627370496), by norm_num⟩
  | 2 => ⟨((69248468540597/140737488355328), (11371282568593/4503599627370496)), (704567/4503599627370496), by norm_num⟩
  | 1 => ⟨((2198219783877811/2251799813685248), (16920203036177/2251799813685248)), (1059653/2251799813685248), by norm_num⟩
  | 0 => ⟨((536352420704443/562949953421312), (16648669717963/1125899906842624)), (1065307/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((536352420704443/562949953421312), (16648669717963/1125899906842624)), (4063823704246139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2043553768122815/2251799813685248), (63448299448071/2251799813685248)), (4122911/2251799813685248), by norm_num⟩
  | 2 => ⟨((926389257861727/1125899906842624), (28790306009905/562949953421312)), (7715591/2251799813685248), by norm_num⟩
  | 3 => ⟨((1518574653049543/2251799813685248), (189509067767289/2251799813685248)), (13485941/2251799813685248), by norm_num⟩
  | 4 => ⟨((504075734512835/1125899906842624), (63900810606133/562949953421312)), (10229647/1125899906842624), by norm_num⟩
  | 5 => ⟨((844689977484487/4503599627370496), (457743681781893/4503599627370496)), (45928647/4503599627370496), by norm_num⟩
  | 6 => ⟨((447616947819807/18014398509481984), (343415518473845/9007199254740992)), (106259921/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-1864131575/33554432)), (1/16777216), by norm_num⟩, -9, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile005Terms3
