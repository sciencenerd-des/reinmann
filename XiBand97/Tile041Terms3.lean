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
namespace Reinmann.XiBand97.Tile041Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35053/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35053/1280))
  have he : value ((69/80), (35053/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-710084599/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-308381201189265/4503599627370496), (-108617136263073/9007199254740992)), (428752573/18014398509481984), by norm_num⟩
  | 1 => ⟨((909060845/4294967296), (160093393/4294967296)), (317/4294967296), by norm_num⟩
  | 2 => ⟨((-43905401/134217728), (-247427737/4294967296)), (123/1073741824), by norm_num⟩
  | 3 => ⟨((1447610223/4294967296), (127468273/2147483648)), (509/4294967296), by norm_num⟩
  | 4 => ⟨((-279664041/1073741824), (-98502461/2147483648)), (395/4294967296), by norm_num⟩
  | 5 => ⟨((1383125477/8589934592), (243580231/8589934592)), (245/4294967296), by norm_num⟩
  | 6 => ⟨((-89068741/1073741824), (-125486139/8589934592)), (507/17179869184), by norm_num⟩
  | 7 => ⟨((314646011/8589934592), (221647419/34359738368)), (225/17179869184), by norm_num⟩
  | 8 => ⟨((-486292089/34359738368), (-171280395/68719476736)), (175/34359738368), by norm_num⟩
  | 9 => ⟨((668066441/137438953472), (14706527/17179869184)), (483/274877906944), by norm_num⟩
  | 10 => ⟨((-1652017385/1099511627776), (-72733599/274877906944)), (75/137438953472), by norm_num⟩
  | 11 => ⟨((464223261/1099511627776), (10219211/137438953472)), (339/2199023255552), by norm_num⟩
  | 12 => ⟨((-478311269/4398046511104), (-84234707/4398046511104)), (351/8796093022208), by norm_num⟩
  | 13 => ⟨((227458529/8796093022208), (320459145/70368744177664)), (335/35184372088832), by norm_num⟩
  | 14 => ⟨((-1607049073/281474976710656), (-70753773/70368744177664)), (297/140737488355328), by norm_num⟩
  | 15 => ⟨((165581897/140737488355328), (116641555/562949953421312)), (123/281474976710656), by norm_num⟩
  | 16 => ⟨((-511820673/2251799813685248), (-180271999/4503599627370496)), (191/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-3865202523257/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777846636329213/633825300114114700748351602688), (-2284900792095/316912650057057350374175801344)), (46325/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944352049382761/19807040628566084398385987584), (-1284953756477/9903520314283042199192993792)), (208521/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888413825279225/2475880078570760549798248448), (-5459565541075/2475880078570760549798248448)), (221621/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885039763667899/77371252455336267181195264), (-1364472981255/38685626227668133590597632)), (433/302231454903657293676544), by norm_num⟩
  | 13 => ⟨((193563891473707/1208925819614629174706176), (-5114995893121/9671406556917033397649408)), (12995/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((157234512051331/75557863725914323419136), (-1118461025817/151115727451828646838272)), (91005/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886308004160081/75557863725914323419136), (-908333156459/9444732965739290427392)), (295917/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648212736534289/2361183241434822606848), (-5447084977259/4722366482869645213696)), (111035/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619914850995995/590295810358705651712), (-7485008583613/590295810358705651712)), (38195/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821555731820291/73786976294838206464), (-4674582106573/36893488147419103232)), (5973/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1820494968340631/9223372036854775808), (-82094199329/72057594037927936)), (215249/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795869754360607/576460752303423488), (-2623968865453/288230376151711744)), (107763/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192610760033799/144115188075855872), (-4585098770775/72057594037927936)), (377793/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488673549691025/36028797018963968), (-13727937656385/36028797018963968)), (567937/36028797018963968), by norm_num⟩
  | 3 => ⟨((185692184638269/1125899906842624), (-8556054091967/4503599627370496)), (178027/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110230942111917/2251799813685248), (-8520257491999/1125899906842624)), (178849/562949953421312), by norm_num⟩
  | 1 => ⟨((1102380639095805/1125899906842624), (-1586389791075/70368744177664)), (1081339/1125899906842624), by norm_num⟩
  | 0 => ⟨((269700409022181/281474976710656), (-12513254219563/281474976710656)), (2195803/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((269700409022181/281474976710656), (-12513254219563/281474976710656)), (8376323704246139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((128931050894409/140737488355328), (-95918431418757/1125899906842624)), (1100783/281474976710656), by norm_num⟩
  | 2 => ⟨((1873497750070841/2251799813685248), (-351487419805029/2251799813685248)), (4408869/562949953421312), by norm_num⟩
  | 3 => ⟨((751943044105931/1125899906842624), (-584875161797995/2251799813685248)), (34850943/2251799813685248), by norm_num⟩
  | 4 => ⟨((213117791351019/562949953421312), (-390614482612091/1125899906842624)), (4040951/140737488355328), by norm_num⟩
  | 5 => ⟨((51686828923597/2251799813685248), (-1183009541762343/4503599627370496)), (93815833/2251799813685248), by norm_num⟩
  | 6 => ⟨((-308381201189265/4503599627370496), (-108617136263073/9007199254740992)), (428752573/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-710084599/8388608)), (1/8388608), by norm_num⟩, -13, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-360148103/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-151769238744771/4503599627370496), (65085145087425/1125899906842624)), (436039359/18014398509481984), by norm_num⟩
  | 1 => ⟨((226913247/2147483648), (-3040941/16777216)), (41/536870912), by norm_num⟩
  | 2 => ⟨((-711485173/4294967296), (1220461173/4294967296)), (129/1073741824), by norm_num⟩
  | 3 => ⟨((743619215/4294967296), (-1275582983/4294967296)), (271/2147483648), by norm_num⟩
  | 4 => ⟨((-582903437/4294967296), (499947883/2147483648)), (427/4294967296), by norm_num⟩
  | 5 => ⟨((365538071/4294967296), (-313516739/2147483648)), (537/8589934592), by norm_num⟩
  | 6 => ⟨((-764095005/17179869184), (655353281/8589934592)), (563/17179869184), by norm_num⟩
  | 7 => ⟨((684518705/34359738368), (-587101835/17179869184)), (507/34359738368), by norm_num⟩
  | 8 => ⟨((-268288055/34359738368), (230106801/17179869184)), (399/68719476736), by norm_num⟩
  | 9 => ⟨((93468405/34359738368), (-1282664077/274877906944)), (279/137438953472), by norm_num⟩
  | 10 => ⟨((-468911429/549755813888), (804357159/549755813888)), (11/17179869184), by norm_num⟩
  | 11 => ⟨((534643299/2199023255552), (-229277929/549755813888)), (403/2199023255552), by norm_num⟩
  | 12 => ⟨((-139697581/2199023255552), (958532827/8796093022208)), (423/8796093022208), by norm_num⟩
  | 13 => ⟨((134775679/8796093022208), (-115595159/4398046511104)), (205/17592186044416), by norm_num⟩
  | 14 => ⟨((-30184883/8796093022208), (828452463/140737488355328)), (369/140737488355328), by norm_num⟩
  | 15 => ⟨((100954161/140737488355328), (-692695441/562949953421312)), (311/562949953421312), by norm_num⟩
  | 16 => ⟨((-79135297/562949953421312), (542985637/2251799813685248)), (245/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (683413677487/2535301200456458802993406410752)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777793190393329/633825300114114700748351602688), (807943977983/158456325028528675187087900672)), (46259/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944322147101755/19807040628566084398385987584), (1817445589121/19807040628566084398385987584)), (13013/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888350712480775/2475880078570760549798248448), (3861005862847/2475880078570760549798248448)), (55317/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770016897290339/154742504910672534362390528), (3859807029265/154742504910672534362390528)), (110661/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387113232160345/2417851639229258349412352), (3617295751595/9671406556917033397649408)), (103773/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628912840359507/302231454903657293676544), (3163860919231/604462909807314587353088)), (181659/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235778379726317/9444732965739290427392), (5138888383793/75557863725914323419136)), (147651/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296365586593745/4722366482869645213696), (240754992985/295147905179352825856)), (110785/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404958466873901/147573952589676412928), (2646610668021/295147905179352825856)), (152405/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821456539875915/73786976294838206464), (826430901583/9223372036854775808)), (47655/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455096543430061/2305843009213693952), (7430899231789/9223372036854775808)), (53651/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397908550444853/288230376151711744), (1855545920375/288230376151711744)), (429599/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596261264749963/72057594037927936), (3242308396335/72057594037927936)), (94085/36028797018963968), by norm_num⟩
  | 4 => ⟨((744274501758029/18014398509481984), (4853682486931/18014398509481984)), (565393/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485395384322473/9007199254740992), (1512504747083/1125899906842624)), (708289/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220218231383547/4503599627370496), (24097819479595/4503599627370496)), (1421229/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204496303507463/2251799813685248), (35891955575113/2251799813685248)), (267939/281474976710656), by norm_num⟩
  | 0 => ⟨((539367599477959/562949953421312), (70770011173765/2251799813685248)), (541739/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((539367599477959/562949953421312), (70770011173765/2251799813685248)), (2066570283056163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1032434165578593/1125899906842624), (135610815170473/2251799813685248)), (4288569/1125899906842624), by norm_num⟩
  | 2 => ⟨((942643947748825/1125899906842624), (248706368928637/2251799813685248)), (16763315/2251799813685248), by norm_num⟩
  | 3 => ⟨((1550961843827765/2251799813685248), (416451856887729/2251799813685248)), (15886323/1125899906842624), by norm_num⟩
  | 4 => ⟨((991229539295261/2251799813685248), (573675276015785/2251799813685248)), (13879995/562949953421312), by norm_num⟩
  | 5 => ⟨((290182401334475/2251799813685248), (1010114444622105/4503599627370496)), (154336075/4503599627370496), by norm_num⟩
  | 6 => ⟨((-151769238744771/4503599627370496), (65085145087425/1125899906842624)), (436039359/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-360148103/4194304)), (1/8388608), by norm_num⟩, -14, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-730073143/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((691768587424953/18014398509481984), (933587113763729/18014398509481984)), (290299277/18014398509481984), by norm_num⟩
  | 1 => ⟨((-524157955/4294967296), (-176846391/1073741824)), (111/2147483648), by norm_num⟩
  | 2 => ⟨((416450549/2147483648), (281013675/1073741824)), (355/4294967296), by norm_num⟩
  | 3 => ⟨((-882334841/4294967296), (-1190768781/4294967296)), (379/4294967296), by norm_num⟩
  | 4 => ⟨((701026905/4294967296), (946081821/4294967296)), (303/4294967296), by norm_num⟩
  | 5 => ⟨((-55697531/536870912), (-601339791/4294967296)), (387/8589934592), by norm_num⟩
  | 6 => ⟨((472026005/8589934592), (637030075/8589934592)), (207/8589934592), by norm_num⟩
  | 7 => ⟨((-857213745/34359738368), (-1156866211/34359738368)), (189/17179869184), by norm_num⟩
  | 8 => ⟨((42566741/4294967296), (919145773/68719476736)), (151/34359738368), by norm_num⟩
  | 9 => ⟨((-240496701/68719476736), (-649132165/137438953472)), (215/137438953472), by norm_num⟩
  | 10 => ⟨((611449169/549755813888), (825190785/549755813888)), (275/549755813888), by norm_num⟩
  | 11 => ⟨((-706624863/2199023255552), (-953636631/2199023255552)), (5/34359738368), by norm_num⟩
  | 12 => ⟨((748563951/8796093022208), (505118091/4398046511104)), (341/8796093022208), by norm_num⟩
  | 13 => ⟨((-731992779/35184372088832), (-493936149/17592186044416)), (335/35184372088832), by norm_num⟩
  | 14 => ⟨((664660701/140737488355328), (112125405/17592186044416)), (153/70368744177664), by norm_num⟩
  | 15 => ⟨((-281643665/281474976710656), (-380096611/281474976710656)), (261/562949953421312), by norm_num⟩
  | 16 => ⟨((111884841/562949953421312), (603983745/2251799813685248)), (417/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (607729299421/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444435289557419/158456325028528675187087900672), (718424970009/316912650057057350374175801344)), (184683/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888586018330755/39614081257132168796771975168), (1616074604419/39614081257132168796771975168)), (51947/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888289142442489/2475880078570760549798248448), (1716599372315/2475880078570760549798248448)), (220795/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110622232399691/9671406556917033397649408), (429014941087/38685626227668133590597632)), (220819/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774197994341085/4835703278458516698824704), (1608232926515/9671406556917033397649408)), (207043/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628888136566721/302231454903657293676544), (1406630968019/604462909807314587353088)), (45297/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886147527582381/75557863725914323419136), (1142350897481/37778931862957161709568)), (147239/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296306633085145/4722366482869645213696), (1712587560801/4722366482869645213696)), (55225/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619753908564407/590295810358705651712), (1176641701719/295147905179352825856)), (303805/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227669780226429/9223372036854775808), (734829830707/18446744073709551616)), (379857/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820277853727531/9223372036854775808), (1651797696049/4611686018427387904)), (427479/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397882176772815/288230376151711744), (1649838116043/576460752303423488)), (213827/576460752303423488), by norm_num⟩
  | 5 => ⟨((74527086961763/9007199254740992), (2882813687541/144115188075855872)), (374395/144115188075855872), by norm_num⟩
  | 4 => ⟨((744210807027583/18014398509481984), (4315429577343/36028797018963968)), (561987/36028797018963968), by norm_num⟩
  | 3 => ⟨((23206986790809/140737488355328), (5378936666401/9007199254740992)), (87897/1125899906842624), by norm_num⟩
  | 2 => ⟨((2219954598424863/4503599627370496), (10711957577571/4503599627370496)), (1408439/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102091120417409/1125899906842624), (3988404677723/562949953421312)), (2117899/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078581882413083/1125899906842624), (1965799161699/140737488355328)), (266057/140737488355328), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078581882413083/1125899906842624), (1965799161699/140737488355328)), (1014926910937261537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1033032821616797/1125899906842624), (30130925101039/1125899906842624)), (8274935/2251799813685248), by norm_num⟩
  | 2 => ⟨((947019296662181/1125899906842624), (6911412459021/140737488355328)), (15627697/2251799813685248), by norm_num⟩
  | 3 => ⟨((1587687173609521/2251799813685248), (186026936884341/2251799813685248)), (27824511/2251799813685248), by norm_num⟩
  | 4 => ⟨((552034982170295/1125899906842624), (32790723651603/281474976710656)), (43834029/2251799813685248), by norm_num⟩
  | 5 => ⟨((1021543442257045/4503599627370496), (257239584959219/2251799813685248)), (831205/35184372088832), by norm_num⟩
  | 6 => ⟨((691768587424953/18014398509481984), (933587113763729/18014398509481984)), (290299277/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-730073143/8388608)), (1/8388608), by norm_num⟩, -14, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-184862727/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1076803038461/17592186044416), (-206147172427631/18014398509481984)), (83121905/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1692429331/8589934592), (158205545/4294967296)), (257/8589934592), by norm_num⟩
  | 2 => ⟨((1361929965/4294967296), (-127311001/2147483648)), (13/268435456), by norm_num⟩
  | 3 => ⟨((-91330905/268435456), (273198869/4294967296)), (225/4294967296), by norm_num⟩
  | 4 => ⟨((1175931369/4294967296), (-219848309/4294967296)), (183/4294967296), by norm_num⟩
  | 5 => ⟨((-757035411/4294967296), (283065763/8589934592)), (119/4294967296), by norm_num⟩
  | 6 => ⟨((812267661/8589934592), (-303717847/17179869184)), (257/17179869184), by norm_num⟩
  | 7 => ⟨((-1494050707/34359738368), (279322867/34359738368)), (119/17179869184), by norm_num⟩
  | 8 => ⟨((601145463/34359738368), (-112388203/34359738368)), (193/68719476736), by norm_num⟩
  | 9 => ⟨((-1720011199/274877906944), (160783853/137438953472)), (279/274877906944), by norm_num⟩
  | 10 => ⟨((553650247/274877906944), (-207017303/549755813888)), (181/549755813888), by norm_num⟩
  | 11 => ⟨((-1296095561/2199023255552), (242313815/2199023255552)), (107/1099511627776), by norm_num⟩
  | 12 => ⟨((695328445/4398046511104), (-129996347/4398046511104)), (29/1099511627776), by norm_num⟩
  | 13 => ⟨((-1377339029/35184372088832), (128751415/17592186044416)), (231/35184372088832), by norm_num⟩
  | 14 => ⟨((1266709515/140737488355328), (-29602487/17592186044416)), (215/140737488355328), by norm_num⟩
  | 15 => ⟨((-1087301503/562949953421312), (203278357/562949953421312)), (93/281474976710656), by norm_num⟩
  | 16 => ⟨((1749944261/4503599627370496), (-327163895/4503599627370496)), (151/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-60188180789/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444422001589385/158456325028528675187087900672), (-284588395725/633825300114114700748351602688)), (23057/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888526294886265/39614081257132168796771975168), (-80021413747/9903520314283042199192993792)), (207517/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944112891227765/1237940039285380274899124224), (-339994762139/2475880078570760549798248448)), (55123/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((6913642447197/604462909807314587353088), (-84971636115/38685626227668133590597632)), (13781/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548336804755867/9671406556917033397649408), (-318528702829/9671406556917033397649408)), (206721/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257724601841481/604462909807314587353088), (-278597737173/604462909807314587353088)), (90443/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943031888240523/37778931862957161709568), (-113126510853/18889465931478580854784)), (293949/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296244007455355/4722366482869645213696), (-21199454957/295147905179352825856)), (110235/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((404917025734869/147573952589676412928), (-466082315455/590295810358705651712)), (37895/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455312860255515/18446744073709551616), (-582144734977/73786976294838206464)), (378971/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820158329064767/9223372036854775808), (-654283476385/9223372036854775808)), (426371/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591409963551913/1152921504606846976), (-81687214403/144115188075855872)), (53301/144115188075855872), by norm_num⟩
  | 5 => ⟨((149041295909915/18014398509481984), (-570927792361/144115188075855872)), (93287/36028797018963968), by norm_num⟩
  | 4 => ⟨((372067206297749/9007199254740992), (-213657362187/9007199254740992)), (559805/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485059213566565/9007199254740992), (-532605013057/4503599627370496)), (699903/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109793900328787/2251799813685248), (-530304542159/1125899906842624)), (700127/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101827289014009/1125899906842624), (-3158921884885/2251799813685248)), (1050761/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078098759483267/1125899906842624), (-3113407946693/1125899906842624)), (4207743/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1078098759483267/1125899906842624), (-3113407946693/1125899906842624)), (16051265725142668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064636891479517/2251799813685248), (-11924901049181/2251799813685248)), (4040735/1125899906842624), by norm_num⟩
  | 2 => ⟨((1892967245350783/2251799813685248), (-21867477280841/2251799813685248)), (465785/70368744177664), by norm_num⟩
  | 3 => ⟨((1591103606827595/2251799813685248), (-36765628968891/2251799813685248)), (25349361/2251799813685248), by norm_num⟩
  | 4 => ⟨((280915177362651/562949953421312), (-25978297228807/1125899906842624)), (36651079/2251799813685248), by norm_num⟩
  | 5 => ⟨((1119028338663421/4503599627370496), (-25926631414599/1125899906842624)), (76539031/4503599627370496), by norm_num⟩
  | 6 => ⟨((1076803038461/17592186044416), (-206147172427631/18014398509481984)), (83121905/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-184862727/2097152)), (1/8388608), by norm_num⟩, -14, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1496921643/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((332787298987375/18014398509481984), (-516057478275001/9007199254740992)), (158086885/9007199254740992), by norm_num⟩
  | 1 => ⟨((-517012189/8589934592), (1603474697/8589934592)), (493/8589934592), by norm_num⟩
  | 2 => ⟨((210559453/2147483648), (-163258605/536870912)), (403/4294967296), by norm_num⟩
  | 3 => ⟨((-457348683/4294967296), (1418432789/4294967296)), (55/536870912), by norm_num⟩
  | 4 => ⟨((93130385/1073741824), (-288836935/1073741824)), (45/536870912), by norm_num⟩
  | 5 => ⟨((-60685557/1073741824), (1505693789/8589934592)), (471/8589934592), by norm_num⟩
  | 6 => ⟨((263625871/8589934592), (-408807977/4294967296)), (257/8589934592), by norm_num⟩
  | 7 => ⟨((-490810593/34359738368), (1522212405/34359738368)), (481/34359738368), by norm_num⟩
  | 8 => ⟨((199888537/34359738368), (-619939371/34359738368)), (197/34359738368), by norm_num⟩
  | 9 => ⟨((-144723589/68719476736), (112212351/17179869184)), (287/137438953472), by norm_num⟩
  | 10 => ⟨((377218739/549755813888), (-146239469/68719476736)), (47/68719476736), by norm_num⟩
  | 11 => ⟨((-223457285/1099511627776), (173259021/274877906944)), (447/2199023255552), by norm_num⟩
  | 12 => ⟨((485363605/8796093022208), (-752659489/4398046511104)), (61/1099511627776), by norm_num⟩
  | 13 => ⟨((-486572763/35184372088832), (1509069093/35184372088832)), (123/8796093022208), by norm_num⟩
  | 14 => ⟨((452943153/140737488355328), (-175596171/17592186044416)), (115/35184372088832), by norm_num⟩
  | 15 => ⟨((-12297771/17592186044416), (1220499791/562949953421312)), (201/281474976710656), by norm_num⟩
  | 16 => ⟨((320538601/2251799813685248), (-124265817/281474976710656)), (329/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-1639842810071/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777633947566753/633825300114114700748351602688), (-1938313071725/633825300114114700748351602688)), (92391/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944232692873711/19807040628566084398385987584), (-2180074259099/39614081257132168796771975168)), (207905/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118010058735157/154742504910672534362390528), (-144729070297/154742504910672534362390528)), (220927/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769827481411761/154742504910672534362390528), (-1157459374605/77371252455336267181195264)), (220959/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774137865057603/4835703278458516698824704), (-2169443621319/9671406556917033397649408)), (12949/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((628835505275493/302231454903657293676544), (-1897470820395/604462909807314587353088)), (22665/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885976407879965/75557863725914323419136), (-3081905190117/75557863725914323419136)), (294709/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296178233927773/4722366482869645213696), (-577532592683/1180591620717411303424)), (221087/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619577263462995/590295810358705651712), (-3174320584989/590295810358705651712)), (152043/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821137291452501/73786976294838206464), (-247796262999/4611686018427387904)), (95061/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820029087259997/9223372036854775808), (-4455991055631/9223372036854775808)), (427963/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591279694972341/1152921504606846976), (-4450570013529/1152921504606846976)), (214099/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192215230785707/144115188075855872), (-486019800845/18014398509481984)), (374939/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488093826544043/36028797018963968), (-5820077664769/36028797018963968)), (562939/36028797018963968), by norm_num⟩
  | 3 => ⟨((742418235631007/4503599627370496), (-1813465954809/2251799813685248)), (352303/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109565207564669/2251799813685248), (-14444214034125/4503599627370496)), (1412017/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202939029859085/2251799813685248), (-10754093461043/1125899906842624)), (1062533/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154650227143777/2251799813685248), (-10596930660427/562949953421312)), (66851/35184372088832), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154650227143777/2251799813685248), (-10596930660427/562949953421312)), (255016327038514603/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2060894069755283/2251799813685248), (-633734150005/17592186044416)), (260901/70368744177664), by norm_num⟩
  | 2 => ⟨((1883250995815893/2251799813685248), (-148481712079355/2251799813685248)), (15883561/2251799813685248), by norm_num⟩
  | 3 => ⟨((195653909430523/281474976710656), (-15522490633629/140737488355328)), (7165635/562949953421312), by norm_num⟩
  | 4 => ⟨((530301653804527/1125899906842624), (-345271016222817/2251799813685248)), (23084703/1125899906842624), by norm_num⟩
  | 5 => ⟨((893211994561697/4503599627370496), (-650494026337361/4503599627370496)), (28825113/1125899906842624), by norm_num⟩
  | 6 => ⟨((332787298987375/18014398509481984), (-516057478275001/9007199254740992)), (158086885/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1496921643/16777216)), (1/8388608), by norm_num⟩, -14, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1514261311/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-693436509926073/18014398509481984), (-394028158608123/9007199254740992)), (385991253/18014398509481984), by norm_num⟩
  | 1 => ⟨((544894603/4294967296), (619245783/4294967296)), (305/4294967296), by norm_num⟩
  | 2 => ⟨((-224485465/1073741824), (-255116635/1073741824)), (505/4294967296), by norm_num⟩
  | 3 => ⟨((493244981/2147483648), (1121097081/4294967296)), (557/4294967296), by norm_num⟩
  | 4 => ⟨((-101603437/536870912), (-28866821/134217728)), (461/4294967296), by norm_num⟩
  | 5 => ⟨((535789365/4294967296), (304449065/2147483648)), (153/2147483648), by norm_num⟩
  | 6 => ⟨((-588624781/8589934592), (-83617871/1073741824)), (169/4294967296), by norm_num⟩
  | 7 => ⟨((277144465/8589934592), (314960985/8589934592)), (5/268435456), by norm_num⟩
  | 8 => ⟨((-913422945/68719476736), (-519030013/34359738368)), (529/68719476736), by norm_num⟩
  | 9 => ⟨((41812403/8589934592), (760283667/137438953472)), (389/137438953472), by norm_num⟩
  | 10 => ⟨((-881963899/549755813888), (-1002308375/549755813888)), (515/549755813888), by norm_num⟩
  | 11 => ⟨((528510751/1099511627776), (75078293/137438953472)), (155/549755813888), by norm_num⟩
  | 12 => ⟨((-290314203/2199023255552), (-329927741/2199023255552)), (171/2199023255552), by norm_num⟩
  | 13 => ⟨((294408693/8796093022208), (669161853/17592186044416)), (349/17592186044416), by norm_num⟩
  | 14 => ⟨((-554470299/70368744177664), (-630128087/70368744177664)), (165/35184372088832), by norm_num⟩
  | 15 => ⟨((974636615/562949953421312), (34613323/17592186044416)), (291/281474976710656), by norm_num⟩
  | 16 => ⟨((-401530411/1125899906842624), (-57039933/140737488355328)), (481/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-1493062096375/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777579161003317/633825300114114700748351602688), (-3529443311525/633825300114114700748351602688)), (185095/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944201755893795/19807040628566084398385987584), (-992410399607/9903520314283042199192993792)), (208277/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888094874104771/2475880078570760549798248448), (-4216520382767/2475880078570760549798248448)), (221347/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769761051077449/154742504910672534362390528), (-2107572048131/77371252455336267181195264)), (221405/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774106532278341/4835703278458516698824704), (-987558946383/2417851639229258349412352)), (207629/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257615791459801/604462909807314587353088), (-3454995069469/604462909807314587353088)), (181737/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885885952576477/75557863725914323419136), (-5611628351107/75557863725914323419136)), (18465/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324027439884469/1180591620717411303424), (-4206326149399/4722366482869645213696)), (110841/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619482084254781/590295810358705651712), (-2889904315941/295147905179352825856)), (152489/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821016779786663/73786976294838206464), (-7218929967087/73786976294838206464)), (190735/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909945700893097/4611686018427387904), (-8113285186749/9223372036854775808)), (53687/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591139378816479/1152921504606846976), (-4051640465831/576460752303423488)), (107481/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192089503732347/144115188075855872), (-7079129120803/144115188075855872)), (188333/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487899357832737/36028797018963968), (-10596242999795/36028797018963968)), (565963/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484583149592063/9007199254740992), (-13206088582751/9007199254740992)), (709145/9007199254740992), by norm_num⟩
  | 2 => ⟨((554648316895723/1125899906842624), (-13147412717605/2251799813685248)), (1423375/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101028878018477/1125899906842624), (-4893735691507/281474976710656)), (1073909/1125899906842624), by norm_num⟩
  | 0 => ⟨((2152589693945473/2251799813685248), (-19284127212729/562949953421312)), (4346907/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152589693945473/2251799813685248), (-19284127212729/562949953421312)), (16582134255416106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2055108238910889/2251799813685248), (-18434504365163/281474976710656)), (538037/140737488355328), by norm_num⟩
  | 2 => ⟨((932969411229957/1125899906842624), (-134594208848729/1125899906842624)), (16840885/2251799813685248), by norm_num⟩
  | 3 => ⟨((1514017926558533/2251799813685248), (-111530589017193/562949953421312)), (3992077/281474976710656), by norm_num⟩
  | 4 => ⟨((464789345978877/1125899906842624), (-599908784450287/2251799813685248)), (27800095/1125899906842624), by norm_num⟩
  | 5 => ⟨((55980330913171/562949953421312), (-990607459427053/4503599627370496)), (4720657/140737488355328), by norm_num⟩
  | 6 => ⟨((-693436509926073/18014398509481984), (-394028158608123/9007199254740992)), (385991253/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1514261311/16777216)), (1/8388608), by norm_num⟩, -14, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile041Terms3
