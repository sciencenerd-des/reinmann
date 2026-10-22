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
namespace Reinmann.XiBand97.Tile032Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (63841/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (63841/2560))
  have he : value ((69/80), (63841/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1838586453/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-123665450830197/4503599627370496), (1331018828420493/9007199254740992)), (227953577/9007199254740992), by norm_num⟩
  | 1 => ⟨((129566559/2147483648), (-87158301/268435456)), (241/4294967296), by norm_num⟩
  | 2 => ⟨((-71171707/1073741824), (1532050889/4294967296)), (267/4294967296), by norm_num⟩
  | 3 => ⟨((208506965/4294967296), (-1122086623/4294967296)), (99/2147483648), by norm_num⟩
  | 4 => ⟨((-114534157/4294967296), (1232738153/8589934592)), (55/2147483648), by norm_num⟩
  | 5 => ⟨((50331453/4294967296), (-1083441027/17179869184)), (195/17179869184), by norm_num⟩
  | 6 => ⟨((-73726337/17179869184), (1587042169/68719476736)), (9/2147483648), by norm_num⟩
  | 7 => ⟨((185135223/137438953472), (-498155437/68719476736)), (183/137438953472), by norm_num⟩
  | 8 => ⟨((-203391831/549755813888), (547279685/274877906944)), (203/549755813888), by norm_num⟩
  | 9 => ⟨((49655281/549755813888), (-1068885667/2199023255552)), (201/2199023255552), by norm_num⟩
  | 10 => ⟨((-87283043/4398046511104), (939432743/8796093022208)), (179/8796093022208), by norm_num⟩
  | 11 => ⟨((139476689/35184372088832), (-750598077/35184372088832)), (9/2199023255552), by norm_num⟩
  | 12 => ⟨((-204307739/281474976710656), (549744181/140737488355328)), (213/281474976710656), by norm_num⟩
  | 13 => ⟨((276252299/2251799813685248), (-1486660217/2251799813685248)), (291/2251799813685248), by norm_num⟩
  | 14 => ⟨((-21678155/1125899906842624), (14582707/140737488355328)), (23/1125899906842624), by norm_num⟩
  | 15 => ⟨((203228907/72057594037927936), (-546841297/36028797018963968)), (109/36028797018963968), by norm_num⟩
  | 16 => ⟨((-223269775/576460752303423488), (600766569/288230376151711744)), (121/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (2285460218295/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779041943125281/633825300114114700748351602688), (1352762327053/316912650057057350374175801344)), (92467/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890048943970299/39614081257132168796771975168), (380400412515/4951760157141521099596496896)), (52021/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236230365735593/309485009821345068724781056), (3232777752079/2475880078570760549798248448)), (27641/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((55359651725345/4835703278458516698824704), (1616036958613/77371252455336267181195264)), (110587/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549851367683007/9671406556917033397649408), (47333150443/151115727451828646838272)), (103699/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629524521652903/302231454903657293676544), (1324954465299/302231454903657293676544)), (11345/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944107246336277/37778931862957161709568), (4304700832073/75557863725914323419136)), (147529/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297855731927701/4722366482869645213696), (403412495361/590295810358705651712)), (55343/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621882092625031/590295810358705651712), (4435546445997/590295810358705651712)), (2379/9223372036854775808), by norm_num⟩
  | 8 => ⟨((114000983361137/4611686018427387904), (5541447771631/73786976294838206464)), (190415/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823263770802481/9223372036854775808), (1557506488743/2305843009213693952)), (214347/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24914217620249/18014398509481984), (3112450219643/576460752303423488)), (107255/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195036683120023/144115188075855872), (5441025761463/144115188075855872)), (23485/18014398509481984), by norm_num⟩
  | 4 => ⟨((746158008558973/18014398509481984), (4075012299823/18014398509481984)), (282187/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490096763583667/9007199254740992), (10167404126093/9007199254740992)), (176689/4503599627370496), by norm_num⟩
  | 2 => ⟨((557399698461151/1125899906842624), (20274520153731/4503599627370496)), (177173/1125899906842624), by norm_num⟩
  | 1 => ⟨((2218511543588929/2251799813685248), (30261381041205/2251799813685248)), (533943/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092638897324197/1125899906842624), (59923090496379/2251799813685248)), (2155231/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092638897324197/1125899906842624), (59923090496379/2251799813685248)), (8221553811080168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((529781581160983/562949953421312), (14538214970599/281474976710656)), (4297831/2251799813685248), by norm_num⟩
  | 2 => ⟨((1988262603158161/2251799813685248), (218906237545929/2251799813685248)), (8533183/2251799813685248), by norm_num⟩
  | 3 => ⟨((1734287486190645/2251799813685248), (386573516051871/2251799813685248)), (16728109/2251799813685248), by norm_num⟩
  | 4 => ⟨((634673203202487/1125899906842624), (297730556378485/1125899906842624)), (15755395/1125899906842624), by norm_num⟩
  | 5 => ⟨((558071972033259/2251799813685248), (83915810259679/281474976710656)), (52190749/2251799813685248), by norm_num⟩
  | 6 => ⟨((-123665450830197/4503599627370496), (1331018828420493/9007199254740992)), (227953577/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1838586453/33554432)), (1/16777216), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1926749683/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((794348065521359/9007199254740992), (-947211082433033/9007199254740992)), (73832663/4503599627370496), by norm_num⟩
  | 1 => ⟨((-872160919/4294967296), (1039998111/4294967296)), (165/4294967296), by norm_num⟩
  | 2 => ⟨((502056183/2147483648), (-598671037/2147483648)), (97/2147483648), by norm_num⟩
  | 3 => ⟨((-385342361/2147483648), (229748501/1073741824)), (151/4294967296), by norm_num⟩
  | 4 => ⟨((110910447/1073741824), (-1058030947/8589934592)), (11/536870912), by norm_num⟩
  | 5 => ⟨((-408609187/8589934592), (974482515/17179869184)), (165/17179869184), by norm_num⟩
  | 6 => ⟨((313619141/17179869184), (-747942971/34359738368)), (1/268435456), by norm_num⟩
  | 7 => ⟨((-825296867/137438953472), (246028905/34359738368)), (171/137438953472), by norm_num⟩
  | 8 => ⟨((237539533/137438953472), (-566502489/274877906944)), (25/68719476736), by norm_num⟩
  | 9 => ⟨((-972364423/2199023255552), (579742305/1099511627776)), (207/2199023255552), by norm_num⟩
  | 10 => ⟨((447790365/4398046511104), (-133490599/1099511627776)), (193/8796093022208), by norm_num⟩
  | 11 => ⟨((-93734129/4398046511104), (223544337/8796093022208)), (41/8796093022208), by norm_num⟩
  | 12 => ⟨((287774411/70368744177664), (-686306477/140737488355328)), (1/1099511627776), by norm_num⟩
  | 13 => ⟨((-407769273/562949953421312), (15194991/17592186044416)), (23/140737488355328), by norm_num⟩
  | 14 => ⟨((536527685/4503599627370496), (-639776179/4503599627370496)), (123/4503599627370496), by norm_num⟩
  | 15 => ⟨((-329440173/18014398509481984), (785674183/36028797018963968)), (153/36028797018963968), by norm_num⟩
  | 16 => ⟨((758564031/288230376151711744), (-904540831/288230376151711744)), (89/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-284277879203/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889452385294543/316912650057057350374175801344), (-84119326403/39614081257132168796771975168)), (92333/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889894819689075/39614081257132168796771975168), (-189235526411/4951760157141521099596496896)), (103883/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889679418700981/2475880078570760549798248448), (-1608176091431/2475880078570760549798248448)), (55193/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771345628941763/154742504910672534362390528), (-1607809591921/154742504910672534362390528)), (27599/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193712330170907/1208925819614629174706176), (-376733049351/2417851639229258349412352)), (103509/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258915705911273/604462909807314587353088), (-329544125565/151115727451828646838272)), (45291/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887998378021261/75557863725914323419136), (-133831711633/4722366482869645213696)), (147217/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297694134345191/4722366482869645213696), (-401335638197/1180591620717411303424)), (110433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405415172223229/147573952589676412928), (-2206309777199/590295810358705651712)), (37969/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823740167276913/73786976294838206464), (-2756333739169/73786976294838206464)), (47473/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911477695090557/4611686018427387904), (-3098740826403/9223372036854775808)), (213693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49818861988873/36028797018963968), (-3096074649315/1152921504606846976)), (213775/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597385459515411/72057594037927936), (-1353034384333/72057594037927936)), (187145/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491921934449595/36028797018963968), (-4053117296331/36028797018963968)), (70225/9007199254740992), by norm_num⟩
  | 3 => ⟨((372403030710917/2251799813685248), (-2527968823521/4503599627370496)), (351447/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228653306459207/4503599627370496), (-315017605637/140737488355328)), (175965/1125899906842624), by norm_num⟩
  | 1 => ⟨((277144058832051/281474976710656), (-15042792373863/2251799813685248)), (529107/1125899906842624), by norm_num⟩
  | 0 => ⟨((545698581362683/562949953421312), (-3721841626567/281474976710656)), (1063083/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545698581362683/562949953421312), (-3721841626567/281474976710656)), (4055339817527389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2115509781794399/2251799813685248), (-57724596890529/2251799813685248)), (4178249/2251799813685248), by norm_num⟩
  | 2 => ⟨((1985988932321097/2251799813685248), (-54230819555935/1125899906842624)), (2016235/562949953421312), by norm_num⟩
  | 3 => ⟨((873165564772695/1125899906842624), (-191316842241899/2251799813685248)), (3750693/562949953421312), by norm_num⟩
  | 4 => ⟨((669035999910387/1125899906842624), (-148371340641763/1125899906842624)), (6454857/562949953421312), by norm_num⟩
  | 5 => ⟨((1512017584745199/4503599627370496), (-705325705356377/4503599627370496)), (18744997/1125899906842624), by norm_num⟩
  | 6 => ⟨((794348065521359/9007199254740992), (-947211082433033/9007199254740992)), (73832663/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1926749683/33554432)), (1/16777216), by norm_num⟩, -9, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1003251513/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-565994096468957/4503599627370496), (15368683921279/1125899906842624)), (11849983/562949953421312), by norm_num⟩
  | 1 => ⟨((647160801/2147483648), (-70290555/2147483648)), (219/4294967296), by norm_num⟩
  | 2 => ⟨((-1551823825/4294967296), (84274695/2147483648)), (265/4294967296), by norm_num⟩
  | 3 => ⟨((620185169/2147483648), (-67360631/2147483648)), (107/2147483648), by norm_num⟩
  | 4 => ⟨((-1487139085/8589934592), (161523739/8589934592)), (259/8589934592), by norm_num⟩
  | 5 => ⟨((1426401513/17179869184), (-38731701/4294967296)), (125/8589934592), by norm_num⟩
  | 6 => ⟨((-570060241/17179869184), (61916375/17179869184)), (101/17179869184), by norm_num⟩
  | 7 => ⟨((390555645/34359738368), (-84839419/68719476736)), (279/137438953472), by norm_num⟩
  | 8 => ⟨((-936511535/274877906944), (101718021/274877906944)), (337/549755813888), by norm_num⟩
  | 9 => ⟨((124758699/137438953472), (-13550509/137438953472)), (181/1099511627776), by norm_num⟩
  | 10 => ⟨((-1914613085/8796093022208), (207953289/8796093022208)), (175/4398046511104), by norm_num⟩
  | 11 => ⟨((1669469697/35184372088832), (-181327349/35184372088832)), (77/8796093022208), by norm_num⟩
  | 12 => ⟨((-667202249/70368744177664), (18116833/17592186044416)), (31/17592186044416), by norm_num⟩
  | 13 => ⟨((984542227/562949953421312), (-53467407/281474976710656)), (23/70368744177664), by norm_num⟩
  | 14 => ⟨((-674522615/2251799813685248), (146524849/4503599627370496)), (127/2251799813685248), by norm_num⟩
  | 15 => ⟨((1725263563/36028797018963968), (-187387329/36028797018963968)), (41/4503599627370496), by norm_num⟩
  | 16 => ⟨((-32320323/4503599627370496), (56166899/72057594037927936)), (199/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (3951346113529/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778767299853745/633825300114114700748351602688), (4676262350689/633825300114114700748351602688)), (92661/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889739584649283/39614081257132168796771975168), (1314952813343/9903520314283042199192993792)), (104273/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472378430996883/618970019642690137449562112), (5587366699499/2475880078570760549798248448)), (13853/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885589541354273/77371252455336267181195264), (5586036063203/154742504910672534362390528)), (55431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549541600124219/9671406556917033397649408), (81804611551/151115727451828646838272)), (103975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629388695668997/302231454903657293676544), (2289822361897/302231454903657293676544)), (91019/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887771924214109/75557863725914323419136), (3719636316579/37778931862957161709568)), (73991/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297522814351793/4722366482869645213696), (2788568000273/2361183241434822606848)), (55527/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621422722131379/590295810358705651712), (3832397534327/295147905179352825856)), (19101/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455859777697123/18446744073709551616), (9575344470299/73786976294838206464)), (191175/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455652940458257/2305843009213693952), (5382248167045/4611686018427387904)), (215297/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593853791791221/1152921504606846976), (10754791122217/1152921504606846976)), (215579/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74653620791425/9007199254740992), (4699763681433/72057594037927936)), (94475/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491438656475729/36028797018963968), (14077470080641/36028797018963968)), (284061/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488983964807905/9007199254740992), (2194833845423/1125899906842624)), (11131/281474976710656), by norm_num⟩
  | 2 => ⟨((556831288693903/1125899906842624), (17501460470359/2251799813685248)), (89467/562949953421312), by norm_num⟩
  | 1 => ⟨((553745465697283/562949953421312), (26109306032391/1125899906842624)), (135251/281474976710656), by norm_num⟩
  | 0 => ⟨((1088873409679943/1125899906842624), (51647929192061/1125899906842624)), (1098873/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1088873409679943/1125899906842624), (51647929192061/1125899906842624)), (4191867832664107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1050695347364969/1125899906842624), (49949428382117/562949953421312)), (139143/70368744177664), by norm_num⟩
  | 2 => ⟨((971650254825455/1125899906842624), (186452211908623/1125899906842624)), (4550235/1125899906842624), by norm_num⟩
  | 3 => ⟨((201913994496817/281474976710656), (160908032865755/562949953421312)), (9360759/1125899906842624), by norm_num⟩
  | 4 => ⟨((974762668121199/2251799813685248), (923409506371789/2251799813685248)), (4695229/281474976710656), by norm_num⟩
  | 5 => ⟨((43288547282291/2251799813685248), (799453937893663/2251799813685248)), (126652157/4503599627370496), by norm_num⟩
  | 6 => ⟨((-565994096468957/4503599627370496), (15368683921279/1125899906842624)), (11849983/562949953421312), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1003251513/16777216)), (1/16777216), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1039656061/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((343179516504893/4503599627370496), (802947999599581/9007199254740992)), (251653091/9007199254740992), by norm_num⟩
  | 1 => ⟨((-813263953/4294967296), (-237852433/1073741824)), (301/4294967296), by norm_num⟩
  | 2 => ⟨((505221251/2147483648), (147760273/536870912)), (189/2147483648), by norm_num⟩
  | 3 => ⟨((-209237941/1073741824), (-979121293/4294967296)), (315/4294967296), by norm_num⟩
  | 4 => ⟨((519936751/4294967296), (608256253/4294967296)), (197/4294967296), by norm_num⟩
  | 5 => ⟨((-129199429/2147483648), (-604584003/8589934592)), (197/8589934592), by norm_num⟩
  | 6 => ⟨((856129387/34359738368), (1001556539/34359738368)), (329/34359738368), by norm_num⟩
  | 7 => ⟨((-303914515/34359738368), (-355539215/34359738368)), (59/17179869184), by norm_num⟩
  | 8 => ⟨((755199199/274877906944), (883481759/274877906944)), (295/274877906944), by norm_num⟩
  | 9 => ⟨((-834044227/1099511627776), (-487859933/549755813888)), (41/137438953472), by norm_num⟩
  | 10 => ⟨((414504409/2199023255552), (969829113/4398046511104)), (41/549755813888), by norm_num⟩
  | 11 => ⟨((-187273593/4398046511104), (-876339931/17592186044416)), (299/17592186044416), by norm_num⟩
  | 12 => ⟨((620476529/70368744177664), (725874307/70368744177664)), (125/35184372088832), by norm_num⟩
  | 13 => ⟨((-948816155/562949953421312), (-554993813/281474976710656)), (385/562949953421312), by norm_num⟩
  | 14 => ⟨((168408541/562949953421312), (788061609/2251799813685248)), (69/562949953421312), by norm_num⟩
  | 15 => ⟨((-446378137/9007199254740992), (-261101271/4503599627370496)), (23/1125899906842624), by norm_num⟩
  | 16 => ⟨((17331375/2251799813685248), (162203071/18014398509481984)), (231/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (1124834947499/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444665592852863/158456325028528675187087900672), (1331032941091/633825300114114700748351602688)), (92331/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889622171356863/39614081257132168796771975168), (748565878203/19807040628566084398385987584)), (103881/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889389792428401/2475880078570760549798248448), (397588685271/618970019642690137449562112)), (110383/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771056073051655/154742504910672534362390528), (794981831967/77371252455336267181195264)), (55197/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549427257481487/9671406556917033397649408), (1490175544319/9671406556917033397649408)), (51753/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258678319749745/604462909807314587353088), (651744177819/302231454903657293676544)), (181159/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235951595699413/9444732965739290427392), (2117390300293/75557863725914323419136)), (294427/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297405047553251/4722366482869645213696), (793681020065/2361183241434822606848)), (220859/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621263393570917/590295810358705651712), (545379317199/147573952589676412928)), (303743/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911621923245903/36893488147419103232), (681309822601/18446744073709551616)), (379773/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911198719648207/4611686018427387904), (3063617058797/9223372036854775808)), (427373/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593646144872691/1152921504606846976), (3060773086091/1152921504606846976)), (213767/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194283735704943/144115188075855872), (2674980354903/144115188075855872)), (187137/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491192309337973/36028797018963968), (4006086767081/36028797018963968)), (280887/18014398509481984), by norm_num⟩
  | 3 => ⟨((186087762596283/1125899906842624), (4996455802199/9007199254740992)), (702855/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226839278398181/4503599627370496), (9959529240035/4503599627370496)), (1407627/4503599627370496), by norm_num⟩
  | 1 => ⟨((553611606830023/562949953421312), (3714025502083/562949953421312)), (264531/281474976710656), by norm_num⟩
  | 0 => ⟨((2177441985522055/2251799813685248), (14690508245165/1125899906842624)), (4251823/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177441985522055/2251799813685248), (14690508245165/1125899906842624)), (16219417580611418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2105156207658709/2251799813685248), (56821621970613/2251799813685248)), (8333797/2251799813685248), by norm_num⟩
  | 2 => ⟨((983314310403355/1125899906842624), (53121236396635/1125899906842624)), (8001371/1125899906842624), by norm_num⟩
  | 3 => ⟨((1712559280675873/2251799813685248), (185575544034331/2251799813685248)), (29462319/2251799813685248), by norm_num⟩
  | 4 => ⟨((1287157494938207/2251799813685248), (282271202147715/2251799813685248)), (24835003/1125899906842624), by norm_num⟩
  | 5 => ⟨((700371931656145/2251799813685248), (322699638965717/2251799813685248)), (69236647/2251799813685248), by norm_num⟩
  | 6 => ⟨((343179516504893/4503599627370496), (802947999599581/9007199254740992)), (251653091/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1039656061/16777216)), (1/8388608), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-134143125/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((418329341195669/9007199254740992), (-223174993971909/2251799813685248)), (269579495/9007199254740992), by norm_num⟩
  | 1 => ⟨((-511643207/4294967296), (136478557/536870912)), (83/1073741824), by norm_num⟩
  | 2 => ⟨((328084729/2147483648), (-1400242349/4294967296)), (429/4294967296), by norm_num⟩
  | 3 => ⟨((-280506905/2147483648), (1197183571/4294967296)), (369/4294967296), by norm_num⟩
  | 4 => ⟨((359743003/4294967296), (-95959851/536870912)), (119/2147483648), by norm_num⟩
  | 5 => ⟨((-184544517/4294967296), (393811453/4294967296)), (123/4294967296), by norm_num⟩
  | 6 => ⟨((631129787/34359738368), (-673404289/17179869184)), (423/34359738368), by norm_num⟩
  | 7 => ⟨((-462518841/68719476736), (986998799/68719476736)), (39/8589934592), by norm_num⟩
  | 8 => ⟨((296584351/137438953472), (-158225121/34359738368)), (201/137438953472), by norm_num⟩
  | 9 => ⟨((-676198969/1099511627776), (1442984613/1099511627776)), (461/1099511627776), by norm_num⟩
  | 10 => ⟨((173441611/1099511627776), (-740236491/2199023255552)), (119/1099511627776), by norm_num⟩
  | 11 => ⟨((-647082107/17592186044416), (1380850263/17592186044416)), (447/17592186044416), by norm_num⟩
  | 12 => ⟨((276622139/35184372088832), (-1180603665/70368744177664)), (3/549755813888), by norm_num⟩
  | 13 => ⟨((-218314393/140737488355328), (465875171/140737488355328)), (305/281474976710656), by norm_num⟩
  | 14 => ⟨((319980207/1125899906842624), (-170706603/281474976710656)), (449/2251799813685248), by norm_num⟩
  | 15 => ⟨((-437724281/9007199254740992), (934088089/9007199254740992)), (309/9007199254740992), by norm_num⟩
  | 16 => ⟨((561370307/72057594037927936), (-598972161/36028797018963968)), (199/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-737651682747/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444638820252717/158456325028528675187087900672), (-872774100167/316912650057057350374175801344)), (23093/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889501679263671/39614081257132168796771975168), (-1963362169035/39614081257132168796771975168)), (207859/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472315436918237/618970019642690137449562112), (-260700188305/309485009821345068724781056)), (55219/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((3458843757213/302231454903657293676544), (-2085072047041/154742504910672534362390528)), (27613/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549307166348075/9671406556917033397649408), (-1954192667301/9671406556917033397649408)), (25891/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629286606966661/302231454903657293676544), (-427339100659/151115727451828646838272)), (45317/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235930239978497/9444732965739290427392), (-1388325239913/37778931862957161709568)), (147309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648638435294203/2361183241434822606848), (-130097894371/295147905179352825856)), (110507/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621087081094563/590295810358705651712), (-1430328467845/295147905179352825856)), (37997/73786976294838206464), by norm_num⟩
  | 8 => ⟨((113938959525953/4611686018427387904), (-893394354995/18446744073709551616)), (95023/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822149241568829/9223372036854775808), (-4017191652117/9223372036854775808)), (106943/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593397770372537/1152921504606846976), (-4013341283619/1152921504606846976)), (427983/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74629138122527/9007199254740992), (-3507346510397/144115188075855872)), (374723/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490865626633943/36028797018963968), (-5252376907965/36028797018963968)), (4395/281474976710656), by norm_num⟩
  | 3 => ⟨((744146531142821/4503599627370496), (-3275185840049/4503599627370496)), (704035/9007199254740992), by norm_num⟩
  | 2 => ⟨((139126197765655/281474976710656), (-3263886755199/1125899906842624)), (352645/1125899906842624), by norm_num⟩
  | 1 => ⟨((2213211226369059/2251799813685248), (-19470686057067/2251799813685248)), (2122163/2251799813685248), by norm_num⟩
  | 0 => ⟨((543737960488297/562949953421312), (-38492966763127/2251799813685248)), (2134803/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543737960488297/562949953421312), (-38492966763127/2251799813685248)), (8143627171043014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525017119371067/562949953421312), (-74358607239327/2251799813685248)), (8393765/2251799813685248), by norm_num⟩
  | 2 => ⟨((1956105680834827/2251799813685248), (-138696314071879/2251799813685248)), (16210705/2251799813685248), by norm_num⟩
  | 3 => ⟨((845348850266249/1125899906842624), (-240966933399681/2251799813685248)), (30160957/2251799813685248), by norm_num⟩
  | 4 => ⟨((310906151001359/562949953421312), (-45230734735747/281474976710656)), (51746035/2251799813685248), by norm_num⟩
  | 5 => ⟨((314341822870069/1125899906842624), (-199840338320521/1125899906842624)), (36893481/1125899906842624), by norm_num⟩
  | 6 => ⟨((418329341195669/9007199254740992), (-223174993971909/2251799813685248)), (269579495/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-134143125/2097152)), (1/8388608), by norm_num⟩, -10, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-552075457/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-912865156618277/9007199254740992), (-296364139010453/18014398509481984)), (39192477/1125899906842624), by norm_num⟩
  | 1 => ⟨((574375029/2147483648), (186472405/4294967296)), (99/1073741824), by norm_num⟩
  | 2 => ⟨((-757904315/2147483648), (-61513921/1073741824)), (525/4294967296), by norm_num⟩
  | 3 => ⟨((1333435291/4294967296), (216451685/4294967296)), (29/268435456), by norm_num⟩
  | 4 => ⟨((-1759506089/8589934592), (-285614203/8589934592)), (615/8589934592), by norm_num⟩
  | 5 => ⟨((7255371/67108864), (150750451/8589934592)), (163/4294967296), by norm_num⟩
  | 6 => ⟨((-408476587/8589934592), (-265226055/34359738368)), (9/536870912), by norm_num⟩
  | 7 => ⟨((1231992149/68719476736), (99992395/34359738368)), (109/17179869184), by norm_num⟩
  | 8 => ⟨((-1625648955/274877906944), (-263885663/274877906944)), (577/274877906944), by norm_num⟩
  | 9 => ⟨((953373509/549755813888), (154757643/549755813888)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((-503201469/1099511627776), (-163365717/2199023255552)), (361/2199023255552), by norm_num⟩
  | 11 => ⟨((241450459/2199023255552), (9798443/549755813888)), (87/2199023255552), by norm_num⟩
  | 12 => ⟨((-424801069/17592186044416), (-137912815/35184372088832)), (307/35184372088832), by norm_num⟩
  | 13 => ⟨((689891923/140737488355328), (223975277/281474976710656)), (501/281474976710656), by norm_num⟩
  | 14 => ⟨((-260094905/281474976710656), (-42220257/281474976710656)), (95/281474976710656), by norm_num⟩
  | 15 => ⟨((732165723/4503599627370496), (237699581/9007199254740992)), (537/9007199254740992), by norm_num⟩
  | 16 => ⟨((-966113659/36028797018963968), (-156825705/36028797018963968)), (89/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-1941327692321/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778447104197419/633825300114114700748351602688), (-4593392235101/633825300114114700748351602688)), (23163/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889379462376331/39614081257132168796771975168), (-5166512105567/39614081257132168796771975168)), (104263/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236141401172723/309485009821345068724781056), (-1372035305919/618970019642690137449562112)), (110813/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885398348937191/77371252455336267181195264), (-2743351838285/77371252455336267181195264)), (221701/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387295813057629/2417851639229258349412352), (-5142257535293/9671406556917033397649408)), (103963/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258463974826247/604462909807314587353088), (-4497948442573/604462909807314587353088)), (711/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((943631440475323/37778931862957161709568), (-7306303834533/75557863725914323419136)), (147963/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648570629082839/2361183241434822606848), (-684652980521/590295810358705651712)), (222077/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405224612519239/147573952589676412928), (-3763557387733/295147905179352825856)), (152785/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822784322318467/73786976294838206464), (-4701396639091/36893488147419103232)), (191143/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56933621353891/288230376151711744), (-10569757643211/9223372036854775808)), (430515/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796559430770065/576460752303423488), (-10559281108351/1152921504606846976)), (431071/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596907967813027/72057594037927936), (-9227591009059/144115188075855872)), (94453/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490477795133209/36028797018963968), (-13817841975729/36028797018963968)), (283985/18014398509481984), by norm_num⟩
  | 3 => ⟨((743893311874875/4503599627370496), (-8615567113559/4503599627370496)), (178039/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112470841175527/2251799813685248), (-17169451473643/2251799813685248)), (715453/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105717343787699/1125899906842624), (-12800107458033/562949953421312)), (270361/281474976710656), by norm_num⟩
  | 0 => ⟨((1085382326036635/1125899906842624), (-12646513941269/281474976710656)), (274509/140737488355328), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085382326036635/1125899906842624), (-12646513941269/281474976710656)), (1047168732226324037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((522025020825913/562949953421312), (-97531246849977/1125899906842624)), (2215711/562949953421312), by norm_num⟩
  | 2 => ⟨((959701780588301/1125899906842624), (-5652561881679/35184372088832)), (8986285/1125899906842624), by norm_num⟩
  | 3 => ⟨((394488538234901/562949953421312), (-616725367619085/2251799813685248)), (36413933/2251799813685248), by norm_num⟩
  | 4 => ⟨((468422884861585/1125899906842624), (-432171789491837/1125899906842624)), (70980479/2251799813685248), by norm_num⟩
  | 5 => ⟨((57993687060561/2251799813685248), (-1438416720060047/4503599627370496)), (227105953/4503599627370496), by norm_num⟩
  | 6 => ⟨((-912865156618277/9007199254740992), (-296364139010453/18014398509481984)), (39192477/1125899906842624), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-552075457/8388608)), (1/8388608), by norm_num⟩, -10, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-566508365/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-4871969353597/4503599627370496), (435666241822323/4503599627370496)), (282415287/18014398509481984), by norm_num⟩
  | 1 => ⟨((6291169/2147483648), (-281287683/1073741824)), (23/536870912), by norm_num⟩
  | 2 => ⟨((-17036801/4294967296), (1523482333/4294967296)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((15378837/4294967296), (-1375222213/4294967296)), (229/4294967296), by norm_num⟩
  | 4 => ⟨((-20823331/8589934592), (1862085395/8589934592)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((11278125/8589934592), (-2017048291/17179869184)), (85/4294967296), by norm_num⟩
  | 6 => ⟨((-318143/536870912), (910378005/17179869184)), (309/34359738368), by norm_num⟩
  | 7 => ⟨((7877003/34359738368), (-1408771051/68719476736)), (241/68719476736), by norm_num⟩
  | 8 => ⟨((-2666415/34359738368), (476877841/68719476736)), (329/274877906944), by norm_num⟩
  | 9 => ⟨((1604619/68719476736), (-1147919229/549755813888)), (25/68719476736), by norm_num⟩
  | 10 => ⟨((-3476311/549755813888), (1243449159/2199023255552)), (219/2199023255552), by norm_num⟩
  | 11 => ⟨((13693127/8796093022208), (-612240499/4398046511104)), (217/8796093022208), by norm_num⟩
  | 12 => ⟨((-6180279/17592186044416), (1105318671/35184372088832)), (99/17592186044416), by norm_num⟩
  | 13 => ⟨((2574847/35184372088832), (-1842005199/281474976710656)), (83/70368744177664), by norm_num⟩
  | 14 => ⟨((-15937863/1125899906842624), (1425212157/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | 15 => ⟨((23018951/9007199254740992), (-1029212285/4503599627370496)), (377/9007199254740992), by norm_num⟩
  | 16 => ⟨((-15584119/36028797018963968), (1393579267/36028797018963968)), (257/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (515175959267/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444590880976461/158456325028528675187087900672), (2437685079673/633825300114114700748351602688)), (11555/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944642954494073/19807040628566084398385987584), (2741835414771/39614081257132168796771975168)), (104011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472258107659397/618970019642690137449562112), (1456252885375/1237940039285380274899124224)), (55265/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770698618007961/154742504910672534362390528), (2911724881151/154742504910672534362390528)), (110549/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193636505551101/1208925819614629174706176), (1364456316189/4835703278458516698824704)), (51831/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258384909467997/604462909807314587353088), (298371174065/75557863725914323419136)), (45363/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471783947206057/18889465931478580854784), (3877271187283/75557863725914323419136)), (36867/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297047153312073/4722366482869645213696), (2906594175097/4722366482869645213696)), (110637/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620771026788153/590295810358705651712), (3994359391761/590295810358705651712)), (76091/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822627995587481/73786976294838206464), (1247409952693/18446744073709551616)), (190313/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821704068864975/9223372036854775808), (5608797521245/9223372036854775808)), (53555/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592952103865341/1152921504606846976), (700389779297/144115188075855872)), (214367/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193675698348255/144115188075855872), (4896345846447/144115188075855872)), (93869/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490278757644129/36028797018963968), (3665885005555/18014398509481984)), (140969/18014398509481984), by norm_num⟩
  | 3 => ⟨((743778780057705/4503599627370496), (1142804897487/1125899906842624)), (353005/9007199254740992), by norm_num⟩
  | 2 => ⟨((556135614808241/1125899906842624), (18218206138907/4503599627370496)), (707761/4503599627370496), by norm_num⟩
  | 1 => ⟨((552745520353987/562949953421312), (13580572511239/1125899906842624)), (533015/1125899906842624), by norm_num⟩
  | 0 => ⟨((2170438182664045/2251799813685248), (53660724563769/2251799813685248)), (1074845/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170438182664045/2251799813685248), (53660724563769/2251799813685248)), (4100208286765670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1045368776299081/1125899906842624), (103443729584483/2251799813685248)), (1061623/562949953421312), by norm_num⟩
  | 2 => ⟨((1936443409468771/2251799813685248), (192089624227421/2251799813685248)), (2068917/562949953421312), by norm_num⟩
  | 3 => ⟨((1648865335086217/2251799813685248), (330376336832325/2251799813685248)), (15645293/2251799813685248), by norm_num⟩
  | 4 => ⟨((1158898918745093/2251799813685248), (241915860381953/1125899906842624)), (27503171/2251799813685248), by norm_num⟩
  | 5 => ⟨((246237157297809/1125899906842624), (996024699247521/4503599627370496)), (20064085/1125899906842624), by norm_num⟩
  | 6 => ⟨((-4871969353597/4503599627370496), (435666241822323/4503599627370496)), (282415287/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-566508365/8388608)), (1/16777216), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile032Terms1
