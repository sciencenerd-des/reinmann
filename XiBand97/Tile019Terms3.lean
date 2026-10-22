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
namespace Reinmann.XiBand97.Tile019Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (5507/256)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (5507/256))
  have he : value ((69/80), (5507/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-278894523/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1086831362106311/18014398509481984), (311276309511769/9007199254740992)), (227561025/9007199254740992), by norm_num⟩
  | 1 => ⟨((50059585/268435456), (-57349699/536870912)), (337/4294967296), by norm_num⟩
  | 2 => ⟨((-1237890419/4294967296), (709081417/4294967296)), (523/4294967296), by norm_num⟩
  | 3 => ⟨((1275457279/4294967296), (-365300127/2147483648)), (541/4294967296), by norm_num⟩
  | 4 => ⟨((-985623149/4294967296), (141144775/1073741824)), (105/1073741824), by norm_num⟩
  | 5 => ⟨((1218641199/8589934592), (-698055187/8589934592)), (261/4294967296), by norm_num⟩
  | 6 => ⟨((-627811947/8589934592), (359619703/8589934592)), (135/4294967296), by norm_num⟩
  | 7 => ⟨((1108910503/34359738368), (-158799967/8589934592)), (479/34359738368), by norm_num⟩
  | 8 => ⟨((-107115295/8589934592), (15339295/2147483648)), (93/17179869184), by norm_num⟩
  | 9 => ⟨((147154633/34359738368), (-674338305/274877906944)), (513/274877906944), by norm_num⟩
  | 10 => ⟨((-727777949/549755813888), (208440833/274877906944)), (319/549755813888), by norm_num⟩
  | 11 => ⟨((409016825/1099511627776), (-117145357/549755813888)), (45/274877906944), by norm_num⟩
  | 12 => ⟨((-842858913/8796093022208), (15087553/274877906944)), (373/8796093022208), by norm_num⟩
  | 13 => ⟨((801634671/35184372088832), (-229593929/17592186044416)), (357/35184372088832), by norm_num⟩
  | 14 => ⟨((-707967657/140737488355328), (405534047/140737488355328)), (317/140737488355328), by norm_num⟩
  | 15 => ⟨((1167124311/1125899906842624), (-83568197/140737488355328)), (525/1125899906842624), by norm_num⟩
  | 16 => ⟨((-450953849/2251799813685248), (516625689/4503599627370496)), (51/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (3414669419263/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777849095199009/633825300114114700748351602688), (4037139484345/633825300114114700748351602688)), (185195/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944353499734057/19807040628566084398385987584), (141897428191/1237940039285380274899124224)), (52099/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888417087432553/2475880078570760549798248448), (4823198790195/2475880078570760549798248448)), (27685/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770082991956267/154742504910672534362390528), (4821721175433/154742504910672534362390528)), (221547/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96782162175997/604462909807314587353088), (4518794073171/9671406556917033397649408)), (207771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257879341304581/604462909807314587353088), (3952375776145/604462909807314587353088)), (90935/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886313679339349/75557863725914323419136), (3209834866691/37778931862957161709568)), (36959/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162053760122449/590295810358705651712), (4812180053171/4722366482869645213696)), (221871/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619921757314081/590295810358705651712), (1653142406935/147573952589676412928)), (152631/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910782609498361/36893488147419103232), (4129724269537/36893488147419103232)), (381861/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455126703450997/2305843009213693952), (4641636430585/4611686018427387904)), (13437/288230376151711744), by norm_num⟩
  | 6 => ⟨((1591752816310111/1152921504606846976), (4636261385361/576460752303423488)), (430473/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192624044448467/144115188075855872), (8101375040767/144115188075855872)), (188607/72057594037927936), by norm_num⟩
  | 4 => ⟨((744348372668275/18014398509481984), (12127926461317/36028797018963968)), (566923/36028797018963968), by norm_num⟩
  | 3 => ⟨((185696520821109/1125899906842624), (15117734395279/9007199254740992)), (355293/4503599627370496), by norm_num⟩
  | 2 => ⟨((277568530569699/562949953421312), (7527301419275/1125899906842624)), (356745/1125899906842624), by norm_num⟩
  | 1 => ⟨((2204932911676795/2251799813685248), (44849053290415/2251799813685248)), (2155035/2251799813685248), by norm_num⟩
  | 0 => ⟨((539528189059419/562949953421312), (88444499373981/2251799813685248)), (4368587/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539528189059419/562949953421312), (88444499373981/2251799813685248)), (16664836892134856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((516212432706971/562949953421312), (84764729598971/1125899906842624)), (4358417/1125899906842624), by norm_num⟩
  | 2 => ⟨((940328742285787/1125899906842624), (19431837150045/140737488355328)), (17298797/2251799813685248), by norm_num⟩
  | 3 => ⟨((190969902266661/281474976710656), (259665213599249/1125899906842624)), (33672151/2251799813685248), by norm_num⟩
  | 4 => ⟨((916752956204663/2251799813685248), (704691280803619/2251799813685248)), (61222061/2251799813685248), by norm_num⟩
  | 5 => ⟨((76349189519341/1125899906842624), (1147575927419751/4503599627370496)), (44083919/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1086831362106311/18014398509481984), (311276309511769/9007199254740992)), (227561025/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-278894523/4194304)), (1/8388608), by norm_num⟩, -11, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1131621033/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-56793611488183/9007199254740992), (600015803223629/9007199254740992)), (201077947/18014398509481984), by norm_num⟩
  | 1 => ⟨((84913273/4294967296), (-1794191437/8589934592)), (151/4294967296), by norm_num⟩
  | 2 => ⟨((-66561269/2147483648), (703209609/2147483648)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((139134983/4294967296), (-734969887/2147483648)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-54532117/2147483648), (1152246915/4294967296)), (199/4294967296), by norm_num⟩
  | 5 => ⟨((68394055/4294967296), (-1445145415/8589934592)), (251/8589934592), by norm_num⟩
  | 6 => ⟨((-142966109/17179869184), (755207515/8589934592)), (33/2147483648), by norm_num⟩
  | 7 => ⟨((64038487/17179869184), (-1353113597/34359738368)), (119/17179869184), by norm_num⟩
  | 8 => ⟨((-100396153/68719476736), (265167491/17179869184)), (47/17179869184), by norm_num⟩
  | 9 => ⟨((139907359/274877906944), (-739049897/137438953472)), (33/34359738368), by norm_num⟩
  | 10 => ⟨((-87735743/549755813888), (926914671/549755813888)), (333/1099511627776), by norm_num⟩
  | 11 => ⟨((50017257/1099511627776), (-1056849305/2199023255552)), (3/34359738368), by norm_num⟩
  | 12 => ⟨((-104552547/8796093022208), (1104581627/8796093022208)), (203/8796093022208), by norm_num⟩
  | 13 => ⟨((50434447/17592186044416), (-1065664401/35184372088832)), (99/17592186044416), by norm_num⟩
  | 14 => ⟨((-180727905/281474976710656), (1909362609/281474976710656)), (357/281474976710656), by norm_num⟩
  | 15 => ⟨((151112347/1125899906842624), (-798239389/562949953421312)), (301/1125899906842624), by norm_num⟩
  | 16 => ⟨((-29613243/1125899906842624), (1251437493/4503599627370496)), (119/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (2169068131411/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777795265559971/633825300114114700748351602688), (2564311473913/633825300114114700748351602688)), (92453/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888646742022475/39614081257132168796771975168), (1442087000223/19807040628566084398385987584)), (52013/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944176732661081/1237940039285380274899124224), (382948676673/309485009821345068724781056)), (55273/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770019820972935/154742504910672534362390528), (3062638671471/154742504910672534362390528)), (13821/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193556981370241/1208925819614629174706176), (2870213956631/9671406556917033397649408)), (405/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((314457104737005/151115727451828646838272), (1255213912629/302231454903657293676544)), (45371/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471557956704947/18889465931478580854784), (4077553489003/75557863725914323419136)), (73749/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296369474954571/4722366482869645213696), (1528255364201/2361183241434822606848)), (110661/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404959923824739/147573952589676412928), (4200015506185/590295810358705651712)), (152219/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821464545412445/73786976294838206464), (5245992125515/73786976294838206464)), (47591/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910198084555883/4611686018427387904), (2948104154157/4611686018427387904)), (214283/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591645430759315/1152921504606846976), (5889299230493/1152921504606846976)), (107219/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192533738710875/144115188075855872), (5145373679921/144115188075855872)), (187809/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488568575225111/36028797018963968), (7702558114633/36028797018963968)), (282063/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485424653240737/9007199254740992), (9601122110725/9007199254740992)), (353193/9007199254740992), by norm_num⟩
  | 2 => ⟨((69384096693953/140737488355328), (2390153996319/562949953421312)), (708233/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204641103873145/2251799813685248), (28480065925537/2251799813685248)), (533493/1125899906842624), by norm_num⟩
  | 0 => ⟨((2157900194522115/2251799813685248), (56157482393819/2251799813685248)), (2152605/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157900194522115/2251799813685248), (56157482393819/2251799813685248)), (8211536416060637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066515663785471/2251799813685248), (107631452356477/2251799813685248)), (1058263/562949953421312), by norm_num⟩
  | 2 => ⟨((945666313952729/1125899906842624), (197550493484257/2251799813685248)), (8174153/2251799813685248), by norm_num⟩
  | 3 => ⟨((196404720925963/281474976710656), (165926691935425/1125899906842624)), (15165515/2251799813685248), by norm_num⟩
  | 4 => ⟨((523728050559183/1125899906842624), (463114497843909/2251799813685248)), (6408509/562949953421312), by norm_num⟩
  | 5 => ⟨((783985539293817/4503599627370496), (215424170183707/1125899906842624)), (68784129/4503599627370496), by norm_num⟩
  | 6 => ⟨((-56793611488183/9007199254740992), (600015803223629/9007199254740992)), (201077947/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1131621033/16777216)), (1/16777216), by norm_num⟩, -11, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1146981085/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((850472623241763/18014398509481984), (395861400824171/9007199254740992)), (261434337/18014398509481984), by norm_num⟩
  | 1 => ⟨((-644409127/4294967296), (-599893971/4294967296)), (25/536870912), by norm_num⟩
  | 2 => ⟨((1023983447/4294967296), (476623833/2147483648)), (319/4294967296), by norm_num⟩
  | 3 => ⟨((-271189543/1073741824), (-252456033/1073741824)), (85/1073741824), by norm_num⟩
  | 4 => ⟨((430927483/2147483648), (802318863/4294967296)), (17/268435456), by norm_num⟩
  | 5 => ⟨((-547804295/4294967296), (-509962507/4294967296)), (87/2147483648), by norm_num⟩
  | 6 => ⟨((580317179/8589934592), (540229433/8589934592)), (93/4294967296), by norm_num⟩
  | 7 => ⟨((-131734231/4294967296), (-245268317/8589934592)), (85/8589934592), by norm_num⟩
  | 8 => ⟨((837316955/68719476736), (389737957/34359738368)), (17/4294967296), by norm_num⟩
  | 9 => ⟨((-591341857/137438953472), (-68811567/17179869184)), (97/68719476736), by norm_num⟩
  | 10 => ⟨((751726501/549755813888), (699797965/549755813888)), (31/68719476736), by norm_num⟩
  | 11 => ⟨((-868737195/2199023255552), (-404362837/1099511627776)), (289/2199023255552), by norm_num⟩
  | 12 => ⟨((920297857/8796093022208), (856724575/8796093022208)), (77/2199023255552), by norm_num⟩
  | 13 => ⟨((-899924963/35184372088832), (-837759021/35184372088832)), (303/35184372088832), by norm_num⟩
  | 14 => ⟨((817145707/140737488355328), (190174519/35184372088832)), (277/140737488355328), by norm_num⟩
  | 15 => ⟨((-346257739/281474976710656), (-322338591/281474976710656)), (237/562949953421312), by norm_num⟩
  | 16 => ⟨((550212867/2251799813685248), (512204697/2251799813685248)), (379/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (976487509649/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777741550929151/633825300114114700748351602688), (288587785097/158456325028528675187087900672)), (184627/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888586481507815/39614081257132168796771975168), (649169382159/19807040628566084398385987584)), (207721/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888289663335931/2475880078570760549798248448), (344774856777/618970019642690137449562112)), (220721/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769956271612259/154742504910672534362390528), (1378665953479/154742504910672534362390528)), (55185/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387099135409619/2417851639229258349412352), (323009738435/2417851639229258349412352)), (51741/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628888395626463/302231454903657293676544), (1130073918577/604462909807314587353088)), (90557/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943074216868855/37778931862957161709568), (458876939041/18889465931478580854784)), (73587/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81019210551097/295147905179352825856), (1375876700145/4722366482869645213696)), (220795/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809877505627917/295147905179352825856), (1890605864581/590295810358705651712)), (303647/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821359756539313/73786976294838206464), (2361421905861/73786976294838206464)), (47455/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820279744930483/9223372036854775808), (663519581319/2305843009213693952)), (427207/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795765415831951/576460752303423488), (2650930258581/1152921504606846976)), (427349/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192435512178203/144115188075855872), (1158013660093/72057594037927936)), (374089/144115188075855872), by norm_num⟩
  | 4 => ⟨((372106329235591/9007199254740992), (3466979947385/36028797018963968)), (561451/36028797018963968), by norm_num⟩
  | 3 => ⟨((742626345995533/4503599627370496), (270087231573/562949953421312)), (702373/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109984191359145/2251799813685248), (8605913788495/4503599627370496)), (1406429/4503599627370496), by norm_num⟩
  | 1 => ⟨((34440775510269/35184372088832), (6408530370201/1125899906842624)), (1056939/1125899906842624), by norm_num⟩
  | 0 => ⟨((2157245061353183/2251799813685248), (25269177477699/2251799813685248)), (4244831/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157245061353183/2251799813685248), (25269177477699/2251799813685248)), (16192745217330168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066377168664557/2251799813685248), (12104052941769/562949953421312)), (8228445/2251799813685248), by norm_num⟩
  | 2 => ⟨((947590999803855/1125899906842624), (88858835479679/2251799813685248)), (15455603/2251799813685248), by norm_num⟩
  | 3 => ⟨((99470956998867/140737488355328), (149572501501885/2251799813685248)), (13617795/1125899906842624), by norm_num⟩
  | 4 => ⟨((1114936017323355/2251799813685248), (52857699959599/562949953421312)), (42117509/2251799813685248), by norm_num⟩
  | 5 => ⟨((532187334025629/2251799813685248), (418743819905587/4503599627370496)), (49616549/2251799813685248), by norm_num⟩
  | 6 => ⟨((850472623241763/18014398509481984), (395861400824171/9007199254740992)), (261434337/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1146981085/16777216)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1161714019/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1112500649194061/18014398509481984), (-2246299596629/281474976710656)), (9875685/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1707554553/8589934592), (220659163/8589934592)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((687050759/2147483648), (-177568611/4294967296)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((-1474354053/4294967296), (95261885/2147483648)), (111/4294967296), by norm_num⟩
  | 4 => ⟨((1186440655/4294967296), (-153318089/4294967296)), (91/4294967296), by norm_num⟩
  | 5 => ⟨((-1527602057/8589934592), (49351189/2147483648)), (119/8589934592), by norm_num⟩
  | 6 => ⟨((1639053777/17179869184), (-52951783/4294967296)), (65/8589934592), by norm_num⟩
  | 7 => ⟨((-1507403023/34359738368), (194794531/34359738368)), (61/17179869184), by norm_num⟩
  | 8 => ⟨((1213035787/68719476736), (-39188713/17179869184)), (25/17179869184), by norm_num⟩
  | 9 => ⟨((-216922865/34359738368), (112127645/137438953472)), (145/274877906944), by norm_num⟩
  | 10 => ⟨((558598213/274877906944), (-72184993/274877906944)), (95/549755813888), by norm_num⟩
  | 11 => ⟨((-40864961/68719476736), (21123139/274877906944)), (113/2199023255552), by norm_num⟩
  | 12 => ⟨((701542587/4398046511104), (-181314031/8796093022208)), (123/8796093022208), by norm_num⟩
  | 13 => ⟨((-347412073/8796093022208), (179577647/35184372088832)), (31/8796093022208), by norm_num⟩
  | 14 => ⟨((319507521/35184372088832), (-41288439/35184372088832)), (29/35184372088832), by norm_num⟩
  | 15 => ⟨((-68563669/35184372088832), (141762515/562949953421312)), (51/281474976710656), by norm_num⟩
  | 16 => ⟨((1765583493/4503599627370496), (-114078983/2251799813685248)), (83/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-167402601537/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444422007200529/158456325028528675187087900672), (-6183839427/19807040628566084398385987584)), (23055/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944263160678321/19807040628566084398385987584), (-222565175319/39614081257132168796771975168)), (103749/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888225812224283/2475880078570760549798248448), (-59102144041/618970019642690137449562112)), (110235/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884946249049151/77371252455336267181195264), (-236333329573/154742504910672534362390528)), (110237/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48385526136145/302231454903657293676544), (-221482580847/9671406556917033397649408)), (103349/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257724631451175/604462909807314587353088), (-96858690373/302231454903657293676544)), (1413/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((117878989266623/4722366482869645213696), (-314641054395/75557863725914323419136)), (146955/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296244049500587/4722366482869645213696), (-235849893579/4722366482869645213696)), (27555/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404917041488709/147573952589676412928), (-162040523669/295147905179352825856)), (151557/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227656440947871/9223372036854775808), (-404782739829/73786976294838206464)), (189453/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910079218569113/4611686018427387904), (-454942979933/9223372036854775808)), (26643/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591410084959229/1152921504606846976), (-227198310979/576460752303423488)), (106579/576460752303423488), by norm_num⟩
  | 5 => ⟨((596165244233913/72057594037927936), (-99245819299/36028797018963968)), (5829/4503599627370496), by norm_num⟩
  | 4 => ⟨((1488269036779503/36028797018963968), (-297124796269/18014398509481984)), (279821/36028797018963968), by norm_num⟩
  | 3 => ⟨((46408110311529/281474976710656), (-185168159919/2251799813685248)), (349829/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109794294121343/2251799813685248), (-737473518743/2251799813685248)), (699819/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203656142978111/2251799813685248), (-2196494076477/2251799813685248)), (525073/1125899906842624), by norm_num⟩
  | 0 => ⟨((269525270376349/281474976710656), (-2164847638159/1125899906842624)), (2102025/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((269525270376349/281474976710656), (-2164847638159/1125899906842624)), (8018589028365325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064654679006509/2251799813685248), (-1036470722579/281474976710656)), (504207/281474976710656), by norm_num⟩
  | 2 => ⟨((1893032481953809/2251799813685248), (-7602644299091/1125899906842624)), (928319/281474976710656), by norm_num⟩
  | 3 => ⟨((198915371781341/281474976710656), (-25565421081311/2251799813685248)), (6293467/1125899906842624), by norm_num⟩
  | 4 => ⟨((1124280765207039/2251799813685248), (-36133622239273/2251799813685248)), (18075913/2251799813685248), by norm_num⟩
  | 5 => ⟨((560752155979569/2251799813685248), (-72163317918367/4503599627370496)), (18630031/2251799813685248), by norm_num⟩
  | 6 => ⟨((1112500649194061/18014398509481984), (-2246299596629/281474976710656)), (9875685/2251799813685248), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1161714019/16777216)), (1/16777216), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1175869039/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((38190466302751/1125899906842624), (-895896015449119/18014398509481984)), (276868445/18014398509481984), by norm_num⟩
  | 1 => ⟨((-237328007/2147483648), (695923735/4294967296)), (217/4294967296), by norm_num⟩
  | 2 => ⟨((386618779/2147483648), (-283423339/1073741824)), (355/4294967296), by norm_num⟩
  | 3 => ⟨((-419880435/2147483648), (615613733/2147483648)), (97/1073741824), by norm_num⟩
  | 4 => ⟨((85500687/536870912), (-501432243/2147483648)), (159/2147483648), by norm_num⟩
  | 5 => ⟨((-111427797/1073741824), (326742931/2147483648)), (209/4294967296), by norm_num⟩
  | 6 => ⟨((484056693/8589934592), (-709706675/8589934592)), (57/2147483648), by norm_num⟩
  | 7 => ⟨((-225300491/8589934592), (660655103/17179869184)), (107/8589934592), by norm_num⟩
  | 8 => ⟨((367025375/34359738368), (-269059763/17179869184)), (175/34359738368), by norm_num⟩
  | 9 => ⟨((-531468491/137438953472), (389610081/68719476736)), (255/137438953472), by norm_num⟩
  | 10 => ⟨((173157565/137438953472), (-1015509805/549755813888)), (167/274877906944), by norm_num⟩
  | 11 => ⟨((-410301137/1099511627776), (1203137811/2199023255552)), (199/1099511627776), by norm_num⟩
  | 12 => ⟨((222800119/2199023255552), (-326661595/2199023255552)), (109/2199023255552), by norm_num⟩
  | 13 => ⟨((-6979849/274877906944), (654950777/17592186044416)), (55/4398046511104), by norm_num⟩
  | 14 => ⟨((831671657/140737488355328), (-304841837/35184372088832)), (103/35184372088832), by norm_num⟩
  | 15 => ⟨((-361288873/281474976710656), (1059417743/562949953421312)), (45/70368744177664), by norm_num⟩
  | 16 => ⟨((588557013/2251799813685248), (-107865165/281474976710656)), (295/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-1266422484585/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888817380590265/316912650057057350374175801344), (-1496925949927/633825300114114700748351602688)), (184695/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888466345215513/39614081257132168796771975168), (-1683634742039/39614081257132168796771975168)), (207801/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888162018780273/2475880078570760549798248448), (-1788349379027/2475880078570760549798248448)), (220811/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769828627375203/154742504910672534362390528), (-446943269781/38685626227668133590597632)), (55209/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387069218881127/2417851639229258349412352), (-1675425195499/9671406556917033397649408)), (51765/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257672083783753/604462909807314587353088), (-732692632019/302231454903657293676544)), (45301/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885978284861117/75557863725914323419136), (-2380104566281/75557863725914323419136)), (147253/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324044939468261/1180591620717411303424), (-1784075851059/4722366482869645213696)), (220923/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619579547454075/590295810358705651712), (-612869060795/147573952589676412928)), (303839/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56910638400375/2305843009213693952), (-3061905202201/73786976294838206464)), (371/72057594037927936), by norm_num⟩
  | 7 => ⟨((455008251068003/2305843009213693952), (-430161427641/1152921504606846976)), (427537/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591284095173849/1152921504606846976), (-859276578717/288230376151711744)), (53465/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192219622953101/144115188075855872), (-46918224747/2251799813685248)), (374461/144115188075855872), by norm_num⟩
  | 4 => ⟨((372025373698395/9007199254740992), (-4494762775277/36028797018963968)), (281051/18014398509481984), by norm_num⟩
  | 3 => ⟨((742423968816379/4503599627370496), (-5602063588735/9007199254740992)), (351675/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109579477708759/2251799813685248), (-5577552643587/2251799813685248)), (704437/2251799813685248), by norm_num⟩
  | 1 => ⟨((275374466876311/281474976710656), (-8305309423625/1125899906842624)), (1059387/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154818475874447/2251799813685248), (-16368081680553/1125899906842624)), (4259557/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154818475874447/2251799813685248), (-16368081680553/1125899906842624)), (16248920449263762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2061538054744303/2251799813685248), (-62652540613111/2251799813685248)), (8276059/2251799813685248), by norm_num⟩
  | 2 => ⟨((1885608918034641/2251799813685248), (-57358827332417/1125899906842624)), (15614113/2251799813685248), by norm_num⟩
  | 3 => ⟨((1573124231537535/2251799813685248), (-48031053066395/562949953421312)), (27740767/2251799813685248), by norm_num⟩
  | 4 => ⟨((270651072099769/562949953421312), (-134219415040013/1125899906842624)), (21746759/1125899906842624), by norm_num⟩
  | 5 => ⟨((122121495112519/562949953421312), (-258116220501729/2251799813685248)), (104381605/4503599627370496), by norm_num⟩
  | 6 => ⟨((38190466302751/1125899906842624), (-895896015449119/18014398509481984)), (276868445/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1175869039/16777216)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-594744889/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-222189251119899/18014398509481984), (-1025923432371863/18014398509481984)), (361251389/18014398509481984), by norm_num⟩
  | 1 => ⟨((43648453/1073741824), (201539771/1073741824)), (285/4294967296), by norm_num⟩
  | 2 => ⟨((-287716361/4294967296), (-664242207/2147483648)), (59/536870912), by norm_num⟩
  | 3 => ⟨((158044365/2147483648), (729744651/2147483648)), (521/4294967296), by norm_num⟩
  | 4 => ⟨((-130222111/2147483648), (-601279831/2147483648)), (431/4294967296), by norm_num⟩
  | 5 => ⟨((343352667/8589934592), (1585376187/8589934592)), (285/4294967296), by norm_num⟩
  | 6 => ⟨((-377211459/17179869184), (-1741713761/17179869184)), (157/4294967296), by norm_num⟩
  | 7 => ⟨((177603919/17179869184), (820057775/17179869184)), (297/17179869184), by norm_num⟩
  | 8 => ⟨((-73169193/17179869184), (-337847081/17179869184)), (491/68719476736), by norm_num⟩
  | 9 => ⟨((107179433/68719476736), (123720985/17179869184)), (181/68719476736), by norm_num⟩
  | 10 => ⟨((-282596741/549755813888), (-1304845387/549755813888)), (479/549755813888), by norm_num⟩
  | 11 => ⟨((338688275/2199023255552), (781919551/1099511627776)), (9/34359738368), by norm_num⟩
  | 12 => ⟨((-372087101/8796093022208), (-1718052855/8796093022208)), (635/8796093022208), by norm_num⟩
  | 13 => ⟨((47166861/4398046511104), (1742283673/35184372088832)), (323/17592186044416), by norm_num⟩
  | 14 => ⟨((-355324067/140737488355328), (-1640652217/140737488355328)), (305/70368744177664), by norm_num⟩
  | 15 => ⟨((312290709/562949953421312), (720976275/281474976710656)), (269/281474976710656), by norm_num⟩
  | 16 => ⟨((-32164351/281474976710656), (-1188110093/2251799813685248)), (445/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-2323959879997/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888790898522439/316912650057057350374175801344), (-2746799572041/633825300114114700748351602688)), (184941/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472101655033429/9903520314283042199192993792), (-3089389767987/39614081257132168796771975168)), (104047/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236012296215345/309485009821345068724781056), (-1640762356767/1237940039285380274899124224)), (55285/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221220595444317/19342813113834066795298816), (-820113571755/38685626227668133590597632)), (221185/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548216775215653/9671406556917033397649408), (-3074288995955/9671406556917033397649408)), (103705/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628809634135883/302231454903657293676544), (-84027076785/18889465931478580854784)), (45383/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942946016568931/37778931862957161709568), (-4367278243557/75557863725914323419136)), (36885/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296114696377885/4722366482869645213696), (-818399044805/1180591620717411303424)), (110695/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809744741595511/295147905179352825856), (-281135631453/36893488147419103232)), (304539/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910513471528083/36893488147419103232), (-2809089515455/36893488147419103232)), (380867/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819904090485847/9223372036854775808), (-3157111589669/4611686018427387904)), (428741/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49723551014679/36028797018963968), (-3153223042645/576460752303423488)), (429075/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298025932750901/36028797018963968), (-2754701174975/72057594037927936)), (46977/18014398509481984), by norm_num⟩
  | 4 => ⟨((1487924196295029/36028797018963968), (-2061663921013/9007199254740992)), (564475/36028797018963968), by norm_num⟩
  | 3 => ⟨((371155072250769/2251799813685248), (-2569462260037/2251799813685248)), (22091/281474976710656), by norm_num⟩
  | 2 => ⟨((2218685703211131/4503599627370496), (-5116134643741/1125899906842624)), (1417785/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101120696472225/1125899906842624), (-30469789797451/2251799813685248)), (534155/562949953421312), by norm_num⟩
  | 0 => ⟨((2153134463294423/2251799813685248), (-7504596978489/281474976710656)), (1078303/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153134463294423/2251799813685248), (-7504596978489/281474976710656)), (4113399507762718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1028595786894815/1125899906842624), (-57406191400559/1125899906842624)), (8478443/2251799813685248), by norm_num⟩
  | 2 => ⟨((468387027832871/562949953421312), (-209779808160321/2251799813685248)), (16355995/2251799813685248), by norm_num⟩
  | 3 => ⟨((769645449052889/1125899906842624), (-349083041028431/2251799813685248)), (30264593/2251799813685248), by norm_num⟩
  | 4 => ⟨((249529008506681/562949953421312), (-238627050447593/1125899906842624)), (25380085/1125899906842624), by norm_num⟩
  | 5 => ⟨((170633316489691/1125899906842624), (-846176409667431/4503599627370496)), (33257859/1125899906842624), by norm_num⟩
  | 6 => ⟨((-222189251119899/18014398509481984), (-1025923432371863/18014398509481984)), (361251389/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-594744889/8388608)), (1/8388608), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile019Terms3
