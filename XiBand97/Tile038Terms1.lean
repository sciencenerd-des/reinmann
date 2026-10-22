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
namespace Reinmann.XiBand97.Tile038Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33979/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33979/1280))
  have he : value ((69/80), (33979/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-978576919/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-34989598049641/1125899906842624), (-662274544720453/4503599627370496)), (21490345/562949953421312), by norm_num⟩
  | 1 => ⟨((36659243/536870912), (86734647/268435456)), (363/4294967296), by norm_num⟩
  | 2 => ⟨((-322194359/4294967296), (-1524603985/4294967296)), (401/4294967296), by norm_num⟩
  | 3 => ⟨((58994447/1073741824), (1116632449/4294967296)), (37/536870912), by norm_num⟩
  | 4 => ⟨((-129624049/4294967296), (-1226746131/8589934592)), (327/8589934592), by norm_num⟩
  | 5 => ⟨((227850517/17179869184), (269543675/4294967296)), (289/17179869184), by norm_num⟩
  | 6 => ⟨((-333759171/68719476736), (-1579327967/68719476736)), (213/34359738368), by norm_num⟩
  | 7 => ⟨((209526815/137438953472), (30983377/4294967296)), (135/68719476736), by norm_num⟩
  | 8 => ⟨((-115094367/274877906944), (-1089238999/549755813888)), (299/549755813888), by norm_num⟩
  | 9 => ⟨((112394743/1099511627776), (1063690089/2199023255552)), (147/1099511627776), by norm_num⟩
  | 10 => ⟨((-197565193/8796093022208), (-934866403/8796093022208)), (261/8796093022208), by norm_num⟩
  | 11 => ⟨((157852763/35184372088832), (1493899227/70368744177664)), (105/17592186044416), by norm_num⟩
  | 12 => ⟨((-115612657/140737488355328), (-1094144033/281474976710656)), (155/140737488355328), by norm_num⟩
  | 13 => ⟨((78162145/562949953421312), (1479433945/2251799813685248)), (211/1125899906842624), by norm_num⟩
  | 14 => ⟨((-196274041/9007199254740992), (-464378375/4503599627370496)), (267/9007199254740992), by norm_num⟩
  | 15 => ⟨((230004345/72057594037927936), (272091621/18014398509481984)), (315/72057594037927936), by norm_num⟩
  | 16 => ⟨((-7896425/18014398509481984), (-597846397/288230376151711744)), (87/144115188075855872), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-2317426729093/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779041832816363/633825300114114700748351602688), (-2743366565497/633825300114114700748351602688)), (138705/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890048813590901/39614081257132168796771975168), (-385721012299/4951760157141521099596496896)), (156069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889842779244589/2475880078570760549798248448), (-3277994075341/2475880078570760549798248448)), (165853/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771508699451129/154742504910672534362390528), (-1638640183915/77371252455336267181195264)), (165887/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774925605986997/4835703278458516698824704), (-3071692186531/9671406556917033397649408)), (155555/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629524448691335/302231454903657293676544), (-2686972680225/604462909807314587353088)), (136147/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236026779676895/9444732965739290427392), (-4364909759789/75557863725914323419136)), (110653/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324463881158093/1180591620717411303424), (-3272439452465/4722366482869645213696)), (166039/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621881781859245/590295810358705651712), (-2248792643017/295147905179352825856)), (228399/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824015306763067/73786976294838206464), (-702369298491/9223372036854775808)), (285643/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911631618732543/4611686018427387904), (-6317163245043/9223372036854775808)), (321547/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594509328284315/1152921504606846976), (-6311965671315/1152921504606846976)), (321795/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597518042224509/72057594037927936), (-5517126786039/144115188075855872)), (140925/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492314971108505/36028797018963968), (-8264014059571/36028797018963968)), (211667/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490095197895227/9007199254740992), (-10309607384689/9007199254740992)), (132537/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114797445622955/2251799813685248), (-20558076249951/4503599627370496)), (1063239/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218503773188323/2251799813685248), (-1917786882915/140737488355328)), (801117/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092627328468849/1125899906842624), (-60761014557751/2251799813685248)), (3234063/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092627328468849/1125899906842624), (-60761014557751/2251799813685248)), (12336971291548918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2119036508386877/2251799813685248), (-14741351475343/281474976710656)), (6451513/2251799813685248), by norm_num⟩
  | 2 => ⟨((993962256391255/1125899906842624), (-13872219799189/140737488355328)), (12818035/2251799813685248), by norm_num⟩
  | 3 => ⟨((1733093498530185/2251799813685248), (-391891685829857/2251799813685248)), (25158827/2251799813685248), by norm_num⟩
  | 4 => ⟨((1265669338768051/2251799813685248), (-603237400333753/2251799813685248)), (11870979/562949953421312), by norm_num⟩
  | 5 => ⟨((274896442039847/1125899906842624), (-678123407738499/2251799813685248)), (78819629/2251799813685248), by norm_num⟩
  | 6 => ⟨((-34989598049641/1125899906842624), (-662274544720453/4503599627370496)), (21490345/562949953421312), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-978576919/16777216)), (3/33554432), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-256375321/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-2626820704051/140737488355328), (1224718138137723/9007199254740992)), (206094311/9007199254740992), by norm_num⟩
  | 1 => ⟨((92292453/2147483648), (-168086155/536870912)), (57/1073741824), by norm_num⟩
  | 2 => ⟨((-212511227/4294967296), (387032675/1073741824)), (265/4294967296), by norm_num⟩
  | 3 => ⟨((81554197/2147483648), (-74264639/268435456)), (103/2147483648), by norm_num⟩
  | 4 => ⟨((-93892739/4294967296), (684002603/4294967296)), (239/8589934592), by norm_num⟩
  | 5 => ⟨((172956817/17179869184), (-629989679/8589934592)), (111/8589934592), by norm_num⟩
  | 6 => ⟨((-132749263/34359738368), (120883737/4294967296)), (43/8589934592), by norm_num⟩
  | 7 => ⟨((174666557/137438953472), (-1272434701/137438953472)), (57/34359738368), by norm_num⟩
  | 8 => ⟨((-201092305/549755813888), (1464944587/549755813888)), (265/549755813888), by norm_num⟩
  | 9 => ⟨((3215501/34359738368), (-749591015/1099511627776)), (137/1099511627776), by norm_num⟩
  | 10 => ⟨((-23692687/1099511627776), (690398839/4398046511104)), (255/8796093022208), by norm_num⟩
  | 11 => ⟨((79351895/17592186044416), (-289036741/8796093022208)), (27/4398046511104), by norm_num⟩
  | 12 => ⟨((-243619321/281474976710656), (1774751177/281474976710656)), (167/140737488355328), by norm_num⟩
  | 13 => ⟨((86300649/562949953421312), (-1257389417/1125899906842624)), (239/1125899906842624), by norm_num⟩
  | 14 => ⟨((-113551193/4503599627370496), (1654426359/9007199254740992)), (317/9007199254740992), by norm_num⟩
  | 15 => ⟨((69723009/18014398509481984), (-507927663/18014398509481984)), (49/9007199254740992), by norm_num⟩
  | 16 => ⟨((-160543161/288230376151711744), (1169546665/288230376151711744)), (57/72057594037927936), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (2223835963613/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778902032382263/633825300114114700748351602688), (329022405497/79228162514264337593543950336)), (23115/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944945792000091/19807040628566084398385987584), (370085179967/4951760157141521099596496896)), (52017/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889675779494511/2475880078570760549798248448), (3145086168721/2475880078570760549798248448)), (110555/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885670881730451/77371252455336267181195264), (786092184669/38685626227668133590597632)), (6911/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549694777208903/9671406556917033397649408), (2947083598199/9671406556917033397649408)), (12961/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314728021166875/151115727451828646838272), (1288968125517/302231454903657293676544)), (90751/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887992043652939/75557863725914323419136), (4187718268721/75557863725914323419136)), (18439/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648844495151271/2361183241434822606848), (1569769749031/2361183241434822606848)), (6917/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405413244357991/147573952589676412928), (2157418819203/295147905179352825856)), (38059/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823729571493701/73786976294838206464), (5390504662971/73786976294838206464)), (190387/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822942156657951/9223372036854775808), (6060136695557/9223372036854775808)), (26789/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594188711326171/1152921504606846976), (6054913725469/1152921504606846976)), (214471/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149344508242429/18014398509481984), (5292178263217/144115188075855872)), (187841/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491895984748539/36028797018963968), (1981634096013/9007199254740992)), (282119/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489573284583771/9007199254740992), (9887667033893/9007199254740992)), (353275/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228556512263709/4503599627370496), (2464240869587/562949953421312)), (708435/4503599627370496), by norm_num⟩
  | 1 => ⟨((554239946091153/562949953421312), (14708866833899/1125899906842624)), (533687/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182220761254587/2251799813685248), (58225004038951/2251799813685248)), (2153697/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182220761254587/2251799813685248), (58225004038951/2251799813685248)), (8215702065474700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2113286123763919/2251799813685248), (14106472949519/281474976710656)), (1071419/562949953421312), by norm_num⟩
  | 2 => ⟨((7725144683377/8796093022208), (211819991161161/2251799813685248)), (1059209/281474976710656), by norm_num⟩
  | 3 => ⟨((1716929065209573/2251799813685248), (186030328967673/1125899906842624)), (16478145/2251799813685248), by norm_num⟩
  | 4 => ⟨((1247631456714753/2251799813685248), (567369935593647/2251799813685248)), (30573479/2251799813685248), by norm_num⟩
  | 5 => ⟨((274153057581969/1125899906842624), (314356798032759/1125899906842624)), (49285827/2251799813685248), by norm_num⟩
  | 6 => ⟨((-2626820704051/140737488355328), (1224718138137723/9007199254740992)), (206094311/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-256375321/4194304)), (1/16777216), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-33373423/524288)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((193597728086285/2251799813685248), (-834764970718309/9007199254740992)), (33092943/1125899906842624), by norm_num⟩
  | 1 => ⟨((-885442881/4294967296), (954474915/4294967296)), (305/4294967296), by norm_num⟩
  | 2 => ⟨((530799825/2147483648), (-286091361/1073741824)), (185/2147483648), by norm_num⟩
  | 3 => ⟨((-848534927/4294967296), (114336187/536870912)), (149/2147483648), by norm_num⟩
  | 4 => ⟨((1017348945/8589934592), (-1096664809/8589934592)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((-487899245/8589934592), (1051874945/17179869184)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((779954195/34359738368), (-420380993/17179869184)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((-133589177/17179869184), (36001057/4294967296)), (193/68719476736), by norm_num⟩
  | 8 => ⟨((40041607/17179869184), (-690614115/274877906944)), (233/274877906944), by norm_num⟩
  | 9 => ⟨((-682777459/1099511627776), (92001129/137438953472)), (125/549755813888), by norm_num⟩
  | 10 => ⟨((654891537/4398046511104), (-705949031/4398046511104)), (121/2199023255552), by norm_num⟩
  | 11 => ⟨((-17845015/549755813888), (615560671/17592186044416)), (213/17592186044416), by norm_num⟩
  | 12 => ⟨((114107939/17592186044416), (-984033349/140737488355328)), (343/140737488355328), by norm_num⟩
  | 13 => ⟨((-673523415/562949953421312), (726033513/562949953421312)), (1/2199023255552), by norm_num⟩
  | 14 => ⟨((922879207/4503599627370496), (-497414951/2251799813685248)), (353/4503599627370496), by norm_num⟩
  | 15 => ⟨((-590124717/18014398509481984), (318066389/9007199254740992)), (57/4503599627370496), by norm_num⟩
  | 16 => ⟨((707528635/144115188075855872), (-762689891/144115188075855872)), (69/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-1071918683759/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889389071774387/316912650057057350374175801344), (-1268573503773/633825300114114700748351602688)), (92325/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236219049479215/4951760157141521099596496896), (-1426886996507/39614081257132168796771975168)), (207747/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944764066313403/1237940039285380274899124224), (-1515747595025/2475880078570760549798248448)), (110375/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885597193515947/77371252455336267181195264), (-757693950713/77371252455336267181195264)), (220771/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387389224746461/2417851639229258349412352), (-1420294097669/9671406556917033397649408)), (206995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629395864109603/302231454903657293676544), (-1242375404403/604462909807314587353088)), (181143/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887797002156523/75557863725914323419136), (-1009072092575/37778931862957161709568)), (147199/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297543179308909/4722366482869645213696), (-756491023173/2361183241434822606848)), (55209/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405363312637473/147573952589676412928), (-2079333426163/590295810358705651712)), (75927/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823481056474675/73786976294838206464), (-2597642348229/73786976294838206464)), (94931/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455666036907669/2305843009213693952), (-1460126500425/4611686018427387904)), (26707/576460752303423488), by norm_num⟩
  | 6 => ⟨((1593912662175937/1152921504606846976), (-91176152589/36028797018963968)), (213733/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194516723558571/144115188075855872), (-1274996069469/72057594037927936)), (187103/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491541361853025/36028797018963968), (-3819115431469/36028797018963968)), (561655/36028797018963968), by norm_num⟩
  | 3 => ⟨((186142208236617/1125899906842624), (-2381816880541/4503599627370496)), (175669/2251799813685248), by norm_num⟩
  | 2 => ⟨((2227708159854329/4503599627370496), (-4748276577799/2251799813685248)), (175897/562949953421312), by norm_num⟩
  | 1 => ⟨((553936034311473/562949953421312), (-14168278598283/2251799813685248)), (132209/140737488355328), by norm_num⟩
  | 0 => ⟨((545003753666163/562949953421312), (-3503969686501/281474976710656)), (2124547/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((545003753666163/562949953421312), (-3503969686501/281474976710656)), (8104503635886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263771209581833/281474976710656), (-27138137168599/1125899906842624)), (8333067/2251799813685248), by norm_num⟩
  | 2 => ⟨((1976139318989621/2251799813685248), (-101724982453661/2251799813685248)), (2002451/281474976710656), by norm_num⟩
  | 3 => ⟨((216203645875355/281474976710656), (-178544057361137/2251799813685248)), (57743/4398046511104), by norm_num⟩
  | 4 => ⟨((657194093573557/1125899906842624), (-68570706714255/562949953421312)), (50105723/2251799813685248), by norm_num⟩
  | 5 => ⟨((1467612908892589/4503599627370496), (-320200850330629/2251799813685248)), (70700345/2251799813685248), by norm_num⟩
  | 6 => ⟨((193597728086285/2251799813685248), (-834764970718309/9007199254740992)), (33092943/1125899906842624), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-33373423/524288)), (1/8388608), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1106701753/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1056279418788321/9007199254740992), (-9380922093355/9007199254740992)), (682499189/18014398509481984), by norm_num⟩
  | 1 => ⟨((1251581073/4294967296), (11115415/4294967296)), (407/4294967296), by norm_num⟩
  | 2 => ⟨((-1555031065/4294967296), (-863149/268435456)), (127/1073741824), by norm_num⟩
  | 3 => ⟨((644017839/2147483648), (2859793/1073741824)), (423/4294967296), by norm_num⟩
  | 4 => ⟨((-800162105/4294967296), (-14212637/8589934592)), (33/536870912), by norm_num⟩
  | 5 => ⟨((397665627/4294967296), (7063415/8589934592)), (527/17179869184), by norm_num⟩
  | 6 => ⟨((-1317549281/34359738368), (-11701285/34359738368)), (219/17179869184), by norm_num⟩
  | 7 => ⟨((1870849697/137438953472), (16615201/137438953472)), (625/137438953472), by norm_num⟩
  | 8 => ⟨((-1162221713/274877906944), (-5160903/137438953472)), (195/137438953472), by norm_num⟩
  | 9 => ⟨((641780547/549755813888), (11399433/1099511627776)), (433/1099511627776), by norm_num⟩
  | 10 => ⟨((-1275811799/4398046511104), (-11330611/4398046511104)), (27/274877906944), by norm_num⟩
  | 11 => ⟨((576413313/8796093022208), (10238367/17592186044416)), (393/17592186044416), by norm_num⟩
  | 12 => ⟨((-1909777699/140737488355328), (-4240231/35184372088832)), (653/140737488355328), by norm_num⟩
  | 13 => ⟨((1460190555/562949953421312), (405253/17592186044416)), (501/562949953421312), by norm_num⟩
  | 14 => ⟨((-2073392697/4503599627370496), (-18414005/4503599627370496)), (357/2251799813685248), by norm_num⟩
  | 15 => ⟨((1373916613/18014398509481984), (12201889/18014398509481984)), (475/18014398509481984), by norm_num⟩
  | 16 => ⟨((-26672301/2251799813685248), (-7580139/72057594037927936)), (593/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-4080706873051/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778650835905763/633825300114114700748351602688), (-2414378786437/316912650057057350374175801344)), (92675/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889608545375297/39614081257132168796771975168), (-5431300090637/39614081257132168796771975168)), (52145/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889374467539073/2475880078570760549798248448), (-5769490653171/2475880078570760549798248448)), (221687/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885519897854489/77371252455336267181195264), (-1442016677153/38685626227668133590597632)), (221767/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549410986158763/9671406556917033397649408), (-2703024873087/4835703278458516698824704)), (207991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258663071779151/604462909807314587353088), (-4728780900549/604462909807314587353088)), (182077/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943793047215885/37778931862957161709568), (-7681433140005/75557863725914323419136)), (148017/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162172923651833/590295810358705651712), (-5758593863093/4722366482869645213696)), (55541/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405307731755711/147573952589676412928), (-3957017807097/295147905179352825856)), (152851/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823199239032297/73786976294838206464), (-9886499261695/73786976294838206464)), (191233/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455585432752717/2305843009213693952), (-5557000670559/4611686018427387904)), (107685/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593583543185489/1152921504606846976), (-11103616287975/1152921504606846976)), (431325/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194221221618721/144115188075855872), (-9703985010553/144115188075855872)), (189033/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491083106606183/36028797018963968), (-7266314467665/18014398509481984)), (284207/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488538690052851/9007199254740992), (-4531237138531/2251799813685248)), (712823/9007199254740992), by norm_num⟩
  | 2 => ⟨((556608031593537/1125899906842624), (-18063737233623/2251799813685248)), (716287/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106818119665325/1125899906842624), (-3367842094097/140737488355328)), (1083111/1125899906842624), by norm_num⟩
  | 0 => ⟨((543757986015521/562949953421312), (-26637481527147/562949953421312)), (2201083/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((543757986015521/562949953421312), (-26637481527147/562949953421312)), (8396465305808639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((130989970840621/140737488355328), (-102917449195609/1125899906842624)), (4460389/1125899906842624), by norm_num⟩
  | 2 => ⟨((965932965740973/1125899906842624), (-11973669761577/70368744177664)), (2279591/281474976710656), by norm_num⟩
  | 3 => ⟨((1592191427253145/2251799813685248), (-328718736670995/1125899906842624)), (37497519/2251799813685248), by norm_num⟩
  | 4 => ⟨((933852777180325/2251799813685248), (-464857623065955/1125899906842624)), (37461369/1125899906842624), by norm_num⟩
  | 5 => ⟨((3424181186279/2251799813685248), (-1542263498399119/4503599627370496)), (1937667/35184372088832), by norm_num⟩
  | 6 => ⟨((-1056279418788321/9007199254740992), (-9380922093355/9007199254740992)), (682499189/18014398509481984), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1106701753/16777216)), (1/8388608), by norm_num⟩, -10, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-571175169/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((127801796890155/2251799813685248), (421479506038363/4503599627370496)), (256183975/9007199254740992), by norm_num⟩
  | 1 => ⟨((-78154835/536870912), (-1030992115/4294967296)), (79/1073741824), by norm_num⟩
  | 2 => ⟨((801852775/4294967296), (661110641/2147483648)), (51/536870912), by norm_num⟩
  | 3 => ⟨((-685570587/4294967296), (-282619219/1073741824)), (351/4294967296), by norm_num⟩
  | 4 => ⟨((439613459/4294967296), (45306499/268435456)), (227/4294967296), by norm_num⟩
  | 5 => ⟨((-56379313/1073741824), (-743736803/8589934592)), (235/8589934592), by norm_num⟩
  | 6 => ⟨((385626887/17179869184), (158970603/4294967296)), (405/34359738368), by norm_num⟩
  | 7 => ⟨((-282603839/34359738368), (-466001767/34359738368)), (299/68719476736), by norm_num⟩
  | 8 => ⟨((724864535/274877906944), (1195270933/274877906944)), (193/137438953472), by norm_num⟩
  | 9 => ⟨((-413164627/549755813888), (-170322745/137438953472)), (111/274877906944), by norm_num⟩
  | 10 => ⟨((211949269/1099511627776), (698990745/2199023255552)), (115/1099511627776), by norm_num⟩
  | 11 => ⟨((-395373921/8796093022208), (-651954859/8796093022208)), (431/17592186044416), by norm_num⟩
  | 12 => ⟨((676076057/70368744177664), (557410399/35184372088832)), (371/70368744177664), by norm_num⟩
  | 13 => ⟨((-133392373/70368744177664), (-879833505/281474976710656)), (295/281474976710656), by norm_num⟩
  | 14 => ⟨((391022493/1125899906842624), (322389769/562949953421312)), (435/2251799813685248), by norm_num⟩
  | 15 => ⟨((-534908209/9007199254740992), (-882040993/9007199254740992)), (299/9007199254740992), by norm_num⟩
  | 16 => ⟨((343003117/36028797018963968), (1131195239/72057594037927936)), (193/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (167003325103/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778555574556469/633825300114114700748351602688), (395189708641/158456325028528675187087900672)), (23089/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((59046938310829/1237940039285380274899124224), (1778010258773/39614081257132168796771975168)), (51955/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889262137579821/2475880078570760549798248448), (944354790969/1237940039285380274899124224)), (6901/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((885464208914413/77371252455336267181195264), (1888230149603/154742504910672534362390528)), (110429/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774653790163055/4835703278458516698824704), (1769706528457/9671406556917033397649408)), (103541/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258573601870205/604462909807314587353088), (773992077845/302231454903657293676544)), (181225/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471860649595657/18889465931478580854784), (1257260077101/37778931862957161709568)), (147271/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297277421600265/4722366482869645213696), (1885055661579/4722366482869645213696)), (27619/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621087907063541/590295810358705651712), (2590596263403/590295810358705651712)), (303883/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823024487231401/73786976294838206464), (3236213675703/73786976294838206464)), (379965/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822150658753321/9223372036854775808), (1818974448459/4611686018427387904)), (213807/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796699681435137/576460752303423488), (3634462587401/1152921504606846976)), (427805/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194067800167303/144115188075855872), (3176236856893/144115188075855872)), (374545/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490868404348803/36028797018963968), (2378264968921/18014398509481984)), (70281/4503599627370496), by norm_num⟩
  | 3 => ⟨((186037152322725/1125899906842624), (2965995791797/4503599627370496)), (703567/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226029519106153/4503599627370496), (738941535993/281474976710656)), (11011/35184372088832), by norm_num⟩
  | 1 => ⟨((2213231828752567/2251799813685248), (17632628435803/2251799813685248)), (2119817/2251799813685248), by norm_num⟩
  | 0 => ⟨((271876639342869/281474976710656), (34859345977149/2251799813685248)), (4262557/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((271876639342869/281474976710656), (34859345977149/2251799813685248)), (16260364541060637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1050152603832429/1125899906842624), (67341274487075/2251799813685248)), (4183191/1125899906842624), by norm_num⟩
  | 2 => ⟨((978494422841831/1125899906842624), (62810747490257/1125899906842624)), (16107435/2251799813685248), by norm_num⟩
  | 3 => ⟨((846883581513221/1125899906842624), (109174831155455/1125899906842624)), (931075/70368744177664), by norm_num⟩
  | 4 => ⟨((1252851434825499/2251799813685248), (82119530748799/562949953421312)), (25299929/1125899906842624), by norm_num⟩
  | 5 => ⟨((20285701458315/70368744177664), (731031746609499/4503599627370496)), (142135287/4503599627370496), by norm_num⟩
  | 6 => ⟨((127801796890155/2251799813685248), (421479506038363/4503599627370496)), (256183975/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-571175169/8388608)), (1/8388608), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-293838943/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((136057473970963/2251799813685248), (-747726246909175/9007199254740992)), (115201315/4503599627370496), by norm_num⟩
  | 1 => ⟨((-342429613/2147483648), (235234789/1073741824)), (73/1073741824), by norm_num⟩
  | 2 => ⟨((225922845/1073741824), (-310399047/1073741824)), (97/1073741824), by norm_num⟩
  | 3 => ⟨((-794964453/4294967296), (1092214507/4294967296)), (43/536870912), by norm_num⟩
  | 4 => ⟨((524489191/4294967296), (-720604175/4294967296)), (229/4294967296), by norm_num⟩
  | 5 => ⟨((-553662817/8589934592), (190171573/2147483648)), (61/2147483648), by norm_num⟩
  | 6 => ⟨((487049305/17179869184), (-669164911/17179869184)), (27/2147483648), by norm_num⟩
  | 7 => ⟨((-734486307/68719476736), (1009122607/68719476736)), (41/8589934592), by norm_num⟩
  | 8 => ⟨((121146967/34359738368), (-665783103/137438953472)), (109/68719476736), by norm_num⟩
  | 9 => ⟨((-568380073/549755813888), (97613321/68719476736)), (129/274877906944), by norm_num⟩
  | 10 => ⟨((599995039/2199023255552), (-824342881/2199023255552)), (137/1099511627776), by norm_num⟩
  | 11 => ⟨((-575789565/8796093022208), (395543295/4398046511104)), (265/8796093022208), by norm_num⟩
  | 12 => ⟨((253256945/17592186044416), (-695907621/35184372088832)), (235/35184372088832), by norm_num⟩
  | 13 => ⟨((-822596427/281474976710656), (35318079/8796093022208)), (3/2199023255552), by norm_num⟩
  | 14 => ⟨((155062795/281474976710656), (-426086561/562949953421312)), (291/1125899906842624), by norm_num⟩
  | 15 => ⟨((-873001825/9007199254740992), (1199431319/9007199254740992)), (103/2251799813685248), by norm_num⟩
  | 16 => ⟨((287987733/18014398509481984), (-791342003/36028797018963968)), (137/18014398509481984), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-306642889933/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889228638985359/316912650057057350374175801344), (-1451100785445/633825300114114700748351602688)), (184685/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889391475888149/39614081257132168796771975168), (-408041179779/9903520314283042199192993792)), (103895/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472286180137285/618970019642690137449562112), (-6772548445/9671406556917033397649408)), (110399/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885405524240095/77371252455336267181195264), (-1733319639175/154742504910672534362390528)), (110411/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549197597202301/9671406556917033397649408), (-406126564809/2417851639229258349412352)), (103523/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258477417253065/604462909807314587353088), (-710481126019/302231454903657293676544)), (181191/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887286393233431/75557863725914323419136), (-2308162678027/75557863725914323419136)), (294483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297160350683635/4722366482869645213696), (-432583506739/1180591620717411303424)), (27613/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620927069242395/590295810358705651712), (-1188964762027/295147905179352825856)), (303811/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227852955227431/9223372036854775808), (-2970493497117/73786976294838206464)), (189933/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455481246238389/2305843009213693952), (-834792345341/2305843009213693952)), (427489/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593174035269283/1152921504606846976), (-833969409349/288230376151711744)), (427665/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596935513712037/72057594037927936), (-22774951993/1125899906842624)), (374405/144115188075855872), by norm_num⟩
  | 4 => ⟨((186321752704521/4503599627370496), (-4365402951543/36028797018963968)), (140501/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487930595720621/9007199254740992), (-5443848181993/9007199254740992)), (703201/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112650163650721/2251799813685248), (-5424536234319/2251799813685248)), (352123/1125899906842624), by norm_num⟩
  | 1 => ⟨((553037032901565/562949953421312), (-16177372435143/2251799813685248)), (1058993/1125899906842624), by norm_num⟩
  | 0 => ⟨((2172885818218103/2251799813685248), (-7992933710879/562949953421312)), (4257069/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172885818218103/2251799813685248), (-7992933710879/562949953421312)), (16239429482466887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096283407830613/2251799813685248), (-61702580134431/2251799813685248)), (1042081/281474976710656), by norm_num⟩
  | 2 => ⟨((1949816715885203/2251799813685248), (-114882410212533/2251799813685248)), (15978659/2251799813685248), by norm_num⟩
  | 3 => ⟨((1682470721573067/2251799813685248), (-198951649637971/2251799813685248)), (29302005/2251799813685248), by norm_num⟩
  | 4 => ⟨((619754463317285/1125899906842624), (-148650125775051/1125899906842624)), (48964787/2251799813685248), by norm_num⟩
  | 5 => ⟨((1286077857218819/4503599627370496), (-654598714232887/4503599627370496)), (133670027/4503599627370496), by norm_num⟩
  | 6 => ⟨((136057473970963/2251799813685248), (-747726246909175/9007199254740992)), (115201315/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-293838943/4194304)), (1/8388608), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-150760387/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-812897009670845/9007199254740992), (-313868910636341/9007199254740992)), (77235303/4503599627370496), by norm_num⟩
  | 1 => ⟨((1049693065/4294967296), (405298599/4294967296)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((-710655379/2147483648), (-137196119/1073741824)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((320748407/1073741824), (495378637/4294967296)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-217150697/1073741824), (-167688777/2147483648)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((470443991/4294967296), (363287701/8589934592)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((-849323963/17179869184), (-327933777/17179869184)), (171/17179869184), by norm_num⟩
  | 7 => ⟨((1314292531/68719476736), (507463503/68719476736)), (267/68719476736), by norm_num⟩
  | 8 => ⟨((-444896269/68719476736), (-42944895/17179869184)), (91/68719476736), by norm_num⟩
  | 9 => ⟨((1070934605/549755813888), (413500201/549755813888)), (221/549755813888), by norm_num⟩
  | 10 => ⟨((-1160057869/2199023255552), (-447911721/2199023255552)), (241/2199023255552), by norm_num⟩
  | 11 => ⟨((571180899/4398046511104), (55134883/1099511627776)), (239/8796093022208), by norm_num⟩
  | 12 => ⟨((-128898879/4398046511104), (-398154749/35184372088832)), (109/17592186044416), by norm_num⟩
  | 13 => ⟨((859236025/140737488355328), (165880469/70368744177664)), (183/140737488355328), by norm_num⟩
  | 14 => ⟨((-1329631023/1125899906842624), (-513385871/1125899906842624)), (285/1125899906842624), by norm_num⟩
  | 15 => ⟨((480094341/2251799813685248), (370739923/4503599627370496)), (13/281474976710656), by norm_num⟩
  | 16 => ⟨((-1300119577/36028797018963968), (-501991161/36028797018963968)), (71/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-903073344091/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778356924961001/633825300114114700748351602688), (-534139932469/79228162514264337593543950336)), (92621/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236159764737093/4951760157141521099596496896), (-4806259348573/39614081257132168796771975168)), (52113/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236127958542517/309485009821345068724781056), (-2552715659525/1237940039285380274899124224)), (27693/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770689311400631/154742504910672534362390528), (-5104059842355/154742504910672534362390528)), (55403/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774541370775375/4835703278458516698824704), (-1195899796931/2417851639229258349412352)), (103919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314594048005213/151115727451828646838272), (-4184192688649/604462909807314587353088)), (45483/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943560270626669/37778931862957161709568), (-3398291330067/37778931862957161709568)), (73945/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648517386060797/2361183241434822606848), (-5095048511033/4722366482869645213696)), (110979/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810376234026335/295147905179352825856), (-3500905834081/295147905179352825856)), (19087/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822602498521041/73786976294838206464), (-4373223362871/36893488147419103232)), (191021/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821672229303583/9223372036854775808), (-614484785893/576460752303423488)), (3361/144115188075855872), by norm_num⟩
  | 6 => ⟨((1592916328011303/1152921504606846976), (-9821766934617/1152921504606846976)), (107681/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193639977009633/144115188075855872), (-8582815086087/144115188075855872)), (188733/144115188075855872), by norm_num⟩
  | 4 => ⟨((46569261494471/1125899906842624), (-200809048293/562949953421312)), (141841/18014398509481984), by norm_num⟩
  | 3 => ⟨((185933027510197/1125899906842624), (-16025489176063/9007199254740992)), (355623/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112154982018479/2251799813685248), (-7983360137505/1125899906842624)), (89289/562949953421312), by norm_num⟩
  | 1 => ⟨((1105259824738655/1125899906842624), (-23803449652973/1125899906842624)), (539579/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084531817822699/1125899906842624), (-734720773297/17592186044416)), (1094595/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084531817822699/1125899906842624), (-734720773297/17592186044416)), (4175548557761764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042719851092445/1125899906842624), (-11323607734765/140737488355328)), (2200185/1125899906842624), by norm_num⟩
  | 2 => ⟨((239599084121051/281474976710656), (-167792543536271/1125899906842624)), (4429327/1125899906842624), by norm_num⟩
  | 3 => ⟨((1581613418224443/2251799813685248), (-571318135962885/2251799813685248)), (34613/4398046511104), by norm_num⟩
  | 4 => ⟨((965936926989875/2251799813685248), (-802561954594939/2251799813685248)), (16943755/1125899906842624), by norm_num⟩
  | 5 => ⟨((64155004855103/1125899906842624), (-344268714931505/1125899906842624)), (106457109/4503599627370496), by norm_num⟩
  | 6 => ⟨((-812897009670845/9007199254740992), (-313868910636341/9007199254740992)), (77235303/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-150760387/2097152)), (1/16777216), by norm_num⟩, -11, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile038Terms1
