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
namespace Reinmann.XiBand97.Tile019Terms0
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

private def J_log2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-2001291981/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-432683776812949/1125899906842624), (-27687371711811/70368744177664)), (55023797/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117265/4194304), (292837885/1073741824)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((-793015383/8589934592), (-811919017/8589934592)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((183225459/8589934592), (750372503/34359738368)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((-1016017683/274877906944), (-520118585/137438953472)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((281699917/549755813888), (576829969/1099511627776)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((-1041384017/17592186044416), (-533104089/8796093022208)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((824951309/140737488355328), (211154055/35184372088832)), (17/35184372088832), by norm_num⟩
  | 8 => ⟨((-285906337/562949953421312), (-73180419/140737488355328)), (49/1125899906842624), by norm_num⟩
  | 9 => ⟨((44038927/1125899906842624), (721419393/18014398509481984)), (63/18014398509481984), by norm_num⟩
  | 10 => ⟨((-781451727/288230376151711744), (-800079709/288230376151711744)), (9/36028797018963968), by norm_num⟩
  | 11 => ⟨((787870635/4611686018427387904), (201662907/1152921504606846976)), (75/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-728147079/73786976294838206464), (-372752201/36893488147419103232)), (71/73786976294838206464), by norm_num⟩
  | 13 => ⟨((155296337/295147905179352825856), (635992953/1180591620717411303424)), (31/590295810358705651712), by norm_num⟩
  | 14 => ⟨((-492083283/18889465931478580854784), (-503813397/18889465931478580854784)), (25/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((5684769/4722366482869645213696), (186248979/151115727451828646838272)), (19/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((-1008737691/19342813113834066795298816), (-1032783637/19342813113834066795298816)), (27/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1526932180709/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890520716089291/316912650057057350374175801344), (-3622898068687/633825300114114700748351602688)), (5785/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892297918489789/39614081257132168796771975168), (-4075524576415/39614081257132168796771975168)), (26037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892231927609801/2475880078570760549798248448), (-4329978633111/2475880078570760549798248448)), (3459/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1773897256439955/154742504910672534362390528), (-4329678991719/154742504910672534362390528)), (27679/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552089855797795/9671406556917033397649408), (-507344445877/1208925819614629174706176)), (25957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315251770589349/151115727451828646838272), (-3551092499917/604462909807314587353088)), (22721/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945697554882779/37778931862957161709568), (-5769927614003/75557863725914323419136)), (36935/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650120073951705/2361183241434822606848), (-2163461220501/2361183241434822606848)), (13857/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812579481712895/295147905179352825856), (-2974333756147/295147905179352825856)), (2383/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1828109270454157/73786976294838206464), (-7434557195321/73786976294838206464)), (47691/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827865490682063/9223372036854775808), (-8362119193145/9223372036854775808)), (839/144115188075855872), by norm_num⟩
  | 6 => ⟨((1599107261296219/1152921504606846976), (-4179959933983/576460752303423488)), (53751/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199054415217673/144115188075855872), (-3656226269155/72057594037927936)), (23547/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498332745083135/36028797018963968), (-10963716361153/36028797018963968)), (35381/18014398509481984), by norm_num⟩
  | 3 => ⟨((374400099870331/2251799813685248), (-6847971874807/4503599627370496)), (88667/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122277119384861/2251799813685248), (-13682856419605/2251799813685248)), (88989/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120407564298781/1125899906842624), (-20491444873425/1125899906842624)), (67145/562949953421312), by norm_num⟩
  | 0 => ⟨((1114683276849663/1125899906842624), (-20425402227349/562949953421312)), (271811/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114683276849663/1125899906842624), (-20425402227349/562949953421312)), (1036876682761764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((68881013085759/70368744177664), (-40443833678967/562949953421312)), (557931/1125899906842624), by norm_num⟩
  | 2 => ⟨((536492290584541/562949953421312), (-19794386481061/140737488355328)), (586219/562949953421312), by norm_num⟩
  | 3 => ⟨((250070980881089/281474976710656), (-150912679600027/562949953421312)), (2564473/1125899906842624), by norm_num⟩
  | 4 => ⟨((807771076876163/1125899906842624), (-268150883293375/562949953421312)), (2965827/562949953421312), by norm_num⟩
  | 5 => ⟨((648147362969111/2251799813685248), (-384766934337193/562949953421312)), (28324277/2251799813685248), by norm_num⟩
  | 6 => ⟨((-432683776812949/1125899906842624), (-27687371711811/70368744177664)), (55023797/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-2001291981/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-396496593/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((124024582464419/4503599627370496), (1741583242045739/4503599627370496)), (67474401/2251799813685248), by norm_num⟩
  | 1 => ⟨((-32485707/1073741824), (-1824688675/4294967296)), (9/268435456), by norm_num⟩
  | 2 => ⟨((35689197/2147483648), (1002312701/4294967296)), (161/8589934592), by norm_num⟩
  | 3 => ⟨((-104556241/17179869184), (-367051017/4294967296)), (15/2147483648), by norm_num⟩
  | 4 => ⟨((114866771/68719476736), (201623379/8589934592)), (67/34359738368), by norm_num⟩
  | 5 => ⟨((-100955237/274877906944), (-354409475/68719476736)), (15/34359738368), by norm_num⟩
  | 6 => ⟨((73940443/1099511627776), (259572403/274877906944)), (45/549755813888), by norm_num⟩
  | 7 => ⟨((-46418217/4398046511104), (-162953961/1099511627776)), (115/8796093022208), by norm_num⟩
  | 8 => ⟨((101991247/70368744177664), (1432185793/70368744177664)), (129/70368744177664), by norm_num⟩
  | 9 => ⟨((-99598967/562949953421312), (-1398592811/562949953421312)), (1/4398046511104), by norm_num⟩
  | 10 => ⟨((87536519/4503599627370496), (153651125/562949953421312)), (115/4503599627370496), by norm_num⟩
  | 11 => ⟨((-139881739/72057594037927936), (-1964253255/72057594037927936)), (187/72057594037927936), by norm_num⟩
  | 12 => ⟨((25612633/144115188075855872), (179829397/72057594037927936)), (139/576460752303423488), by norm_num⟩
  | 13 => ⟨((-69263639/4611686018427387904), (-486308395/2305843009213693952)), (95/4611686018427387904), by norm_num⟩
  | 14 => ⟨((10870555/9223372036854775808), (1221175723/73786976294838206464)), (121/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-101909549/1180591620717411303424), (-1431038567/1180591620717411303424)), (9/73786976294838206464), by norm_num⟩
  | 16 => ⟨((111959083/18889465931478580854784), (393039139/4722366482869645213696)), (161/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (976765071041/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780505295316699/633825300114114700748351602688), (1158100832859/316912650057057350374175801344)), (23107/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945847530280407/19807040628566084398385987584), (2605501740855/39614081257132168796771975168)), (25999/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891591747991835/2475880078570760549798248448), (1384038691823/1237940039285380274899124224)), (6907/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((55414296198703/4835703278458516698824704), (1383887819173/77371252455336267181195264)), (27633/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551490490430923/9671406556917033397649408), (648617266121/2417851639229258349412352)), (51823/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315120766047967/151115727451828646838272), (567459960965/151115727451828646838272)), (45355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890544379876363/75557863725914323419136), (230493041471/4722366482869645213696)), (9215/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324900700011897/1180591620717411303424), (345673821155/590295810358705651712)), (55307/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406070936673731/147573952589676412928), (3801557434705/590295810358705651712)), (76073/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456754238504667/18446744073709551616), (4750664958955/73786976294838206464)), (23783/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913319488866975/4611686018427387904), (1335683914615/2305843009213693952)), (107079/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199735459528175/144115188075855872), (5340532786467/1152921504606846976)), (26787/288230376151711744), by norm_num⟩
  | 5 => ⟨((598993535434097/72057594037927936), (145952755281/4503599627370496)), (93833/144115188075855872), by norm_num⟩
  | 4 => ⟨((748369155269921/18014398509481984), (7000776747173/36028797018963968)), (70453/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495618867560567/9007199254740992), (2185575000423/2251799813685248)), (88203/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120312839881097/2251799813685248), (8729296027645/2251799813685248)), (88409/1125899906842624), by norm_num⟩
  | 1 => ⟨((1117504225196101/1125899906842624), (13061442667179/1125899906842624)), (133129/562949953421312), by norm_num⟩
  | 0 => ⟨((277262152995825/281474976710656), (25992931805431/1125899906842624)), (536643/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277262152995825/281474976710656), (25992931805431/1125899906842624)), (2047130589011764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((272962361877625/281474976710656), (12801948363701/281474976710656)), (1082001/1125899906842624), by norm_num⟩
  | 2 => ⟨((264124939235105/281474976710656), (24829561070243/281474976710656)), (549245/281474976710656), by norm_num⟩
  | 3 => ⟨((491308159830389/562949953421312), (46598147981401/281474976710656)), (4405/1099511627776), by norm_num⟩
  | 4 => ⟨((826709930147505/1125899906842624), (325344023170917/1125899906842624)), (9366859/1125899906842624), by norm_num⟩
  | 5 => ⟨((1026024732182859/2251799813685248), (955556113060883/2251799813685248)), (38337785/2251799813685248), by norm_num⟩
  | 6 => ⟨((124024582464419/4503599627370496), (1741583242045739/4503599627370496)), (67474401/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-396496593/16777216)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-2001291981/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-8021965912651/1125899906842624), (680977141331097/2251799813685248)), (108806627/4503599627370496), by norm_num⟩
  | 1 => ⟨((42422509/4294967296), (-900301715/2147483648)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-29405043/4294967296), (1248083191/4294967296)), (103/4294967296), by norm_num⟩
  | 3 => ⟨((13588015/4294967296), (-1153473793/8589934592)), (97/8589934592), by norm_num⟩
  | 4 => ⟨((-37673977/34359738368), (1599054215/34359738368)), (17/4294967296), by norm_num⟩
  | 5 => ⟨((20890889/68719476736), (-1773407873/137438953472)), (153/137438953472), by norm_num⟩
  | 6 => ⟨((-19307281/274877906944), (819488445/274877906944)), (9/34359738368), by norm_num⟩
  | 7 => ⟨((7647307/549755813888), (-1298345383/2199023255552)), (29/549755813888), by norm_num⟩
  | 8 => ⟨((-21202837/8796093022208), (1799888883/17592186044416)), (163/17592186044416), by norm_num⟩
  | 9 => ⟨((26127443/70368744177664), (-554483513/35184372088832)), (51/35184372088832), by norm_num⟩
  | 10 => ⟨((-14488131/281474976710656), (307470947/140737488355328)), (115/562949953421312), by norm_num⟩
  | 11 => ⟨((29214275/4503599627370496), (-1239986153/4503599627370496)), (59/2251799813685248), by norm_num⟩
  | 12 => ⟨((-26999723/36028797018963968), (1145990541/36028797018963968)), (111/36028797018963968), by norm_num⟩
  | 13 => ⟨((46067155/576460752303423488), (-977649369/288230376151711744)), (3/9007199254740992), by norm_num⟩
  | 14 => ⟨((-4561617/576460752303423488), (774462747/2305843009213693952)), (77/2305843009213693952), by norm_num⟩
  | 15 => ⟨((26981307/36893488147419103232), (-1145208895/36893488147419103232)), (29/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-18702017/295147905179352825856), (793798317/295147905179352825856)), (163/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (2076821661049/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780121785556547/633825300114114700748351602688), (1230687849707/316912650057057350374175801344)), (23111/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945631816697861/19807040628566084398385987584), (2768747995497/39614081257132168796771975168)), (52007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891133379469057/2475880078570760549798248448), (2941435225367/2475880078570760549798248448)), (27633/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886399567778501/77371252455336267181195264), (1470515391443/77371252455336267181195264)), (55277/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387765205351171/2417851639229258349412352), (2756786671191/9671406556917033397649408)), (6479/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315026782792007/151115727451828646838272), (2411758685925/604462909807314587353088)), (11341/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472483385022493/18889465931478580854784), (122446948303/2361183241434822606848)), (9217/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1299144715213819/4722366482869645213696), (2938022007627/4722366482869645213696)), (6915/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811826976639273/295147905179352825856), (4038635184311/590295810358705651712)), (76093/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913114911129923/36893488147419103232), (5046576620477/73786976294838206464)), (11895/9223372036854775808), by norm_num⟩
  | 7 => ⟨((456438401510425/2305843009213693952), (2837518870897/4611686018427387904)), (53557/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399249623589707/288230376151711744), (5672087167501/1152921504606846976)), (26797/288230376151711744), by norm_num⟩
  | 5 => ⟨((598606375422577/72057594037927936), (1239939432567/36028797018963968)), (93873/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495577260114253/36028797018963968), (7433001652455/36028797018963968)), (140975/36028797018963968), by norm_num⟩
  | 3 => ⟨((373542077365573/2251799813685248), (9279645736985/9007199254740992)), (176511/9007199254740992), by norm_num⟩
  | 2 => ⟨((559431710201945/1125899906842624), (2315561476411/562949953421312)), (176949/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115332964234889/1125899906842624), (13849903178027/1125899906842624)), (33315/140737488355328), by norm_num⟩
  | 0 => ⟨((276179423183209/281474976710656), (13763073839975/562949953421312)), (134359/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276179423183209/281474976710656), (13763073839975/562949953421312)), (512538910985851199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((541630514585939/562949953421312), (3376035268545/70368744177664)), (1080929/1125899906842624), by norm_num⟩
  | 2 => ⟨((1039645408077745/1125899906842624), (51970906718063/562949953421312)), (2183705/1125899906842624), by norm_num⟩
  | 3 => ⟨((475201511010659/562949953421312), (191957790189687/1125899906842624)), (4436021/1125899906842624), by norm_num⟩
  | 4 => ⟨((1539067737348791/2251799813685248), (648147362969143/2251799813685248)), (18003507/2251799813685248), by norm_num⟩
  | 5 => ⟨((432683776812953/1125899906842624), (442997947389003/1125899906842624)), (34974285/2251799813685248), by norm_num⟩
  | 6 => ⟨((-8021965912651/1125899906842624), (680977141331097/2251799813685248)), (108806627/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-2001291981/67108864)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-1161714019/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-8761752437181/35184372088832), (36081658959187/2251799813685248)), (91345617/4503599627370496), by norm_num⟩
  | 1 => ⟨((1721374091/4294967296), (-110762005/4294967296)), (71/2147483648), by norm_num⟩
  | 2 => ⟨((-692611181/2147483648), (89132285/4294967296)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((743143129/4294967296), (-23908813/2147483648)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((-598021363/8589934592), (19239875/4294967296)), (103/17179869184), by norm_num⟩
  | 5 => ⟨((1539965207/68719476736), (-49544615/34359738368)), (135/68719476736), by norm_num⟩
  | 6 => ⟨((-826159463/137438953472), (53159321/137438953472)), (147/274877906944), by norm_num⟩
  | 7 => ⟨((1519602699/1099511627776), (-48889501/549755813888)), (137/1099511627776), by norm_num⟩
  | 8 => ⟨((-611426549/2199023255552), (9835577/549755813888)), (7/274877906944), by norm_num⟩
  | 9 => ⟨((874713839/17592186044416), (-112567115/35184372088832)), (81/17592186044416), by norm_num⟩
  | 10 => ⟨((-281559523/35184372088832), (72467913/140737488355328)), (53/70368744177664), by norm_num⟩
  | 11 => ⟨((1318262025/1125899906842624), (-42411857/562949953421312)), (63/562949953421312), by norm_num⟩
  | 12 => ⟨((-353610147/2251799813685248), (45506167/4503599627370496)), (137/9007199254740992), by norm_num⟩
  | 13 => ⟨((1400894959/72057594037927936), (-90140739/72057594037927936)), (69/36028797018963968), by norm_num⟩
  | 14 => ⟨((-1288373405/576460752303423488), (82900527/576460752303423488)), (129/576460752303423488), by norm_num⟩
  | 15 => ⟨((1105897069/4611686018427387904), (-71159067/4611686018427387904)), (113/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-889936335/36893488147419103232), (28631525/18446744073709551616)), (23/9223372036854775808), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (4008573891175/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444953974018843/158456325028528675187087900672), (2374656702407/316912650057057350374175801344)), (23167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472729758229135/9903520314283042199192993792), (333892763837/2475880078570760549798248448)), (52141/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472691659718079/618970019642690137449562112), (1418842190637/618970019642690137449562112)), (55417/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886215858668407/77371252455336267181195264), (2837229627495/77371252455336267181195264)), (13859/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550715647186927/9671406556917033397649408), (2659419536407/4835703278458516698824704)), (6499/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314951096117907/151115727451828646838272), (4653017567117/604462909807314587353088)), (22757/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472360057228015/18889465931478580854784), (3779670414021/37778931862957161709568)), (73999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298773553317117/4722366482869645213696), (1416979797475/1180591620717411303424)), (55533/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811570846051171/295147905179352825856), (1947702592443/147573952589676412928)), (38207/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912793314044917/36893488147419103232), (4867322100111/36893488147419103232)), (5975/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1825026073823587/9223372036854775808), (10946153577689/9223372036854775808)), (107665/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596266045134829/1152921504606846976), (5469749875987/576460752303423488)), (107807/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196566335031657/144115188075855872), (4782286727405/72057594037927936)), (94493/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494596613130289/36028797018963968), (14331874381501/36028797018963968)), (142061/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492923260014347/9007199254740992), (17888599614019/9007199254740992)), (178141/9007199254740992), by norm_num⟩
  | 2 => ⟨((34924675307957/70368744177664), (8924599214671/1125899906842624)), (89495/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113350695518789/1125899906842624), (26675169462027/1125899906842624)), (135305/562949953421312), by norm_num⟩
  | 0 => ⟨((1100469042443235/1125899906842624), (26477542513345/562949953421312)), (137437/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100469042443235/1125899906842624), (26477542513345/562949953421312)), (524280549169444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((536560961148845/562949953421312), (103517961690297/1125899906842624)), (140797/140737488355328), by norm_num⟩
  | 2 => ⟨((1013300280770735/1125899906842624), (197330852176645/1125899906842624)), (588569/281474976710656), by norm_num⟩
  | 3 => ⟨((877376388243513/1125899906842624), (355192156425451/1125899906842624)), (2531451/562949953421312), by norm_num⟩
  | 4 => ⟨((1143312748761129/2251799813685248), (1107157783540157/2251799813685248)), (11085131/1125899906842624), by norm_num⟩
  | 5 => ⟨((9033405559819/562949953421312), (562140382603527/1125899906842624)), (22157175/1125899906842624), by norm_num⟩
  | 6 => ⟨((-8761752437181/35184372088832), (36081658959187/2251799813685248)), (91345617/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1161714019/33554432)), (1/33554432), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-1293316181/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((9962230800003/70368744177664), (-718089982953203/4503599627370496)), (28028919/2251799813685248), by norm_num⟩
  | 1 => ⟨((-272368185/1073741824), (38344995/134217728)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((976036549/4294967296), (-549640063/2147483648)), (45/2147483648), by norm_num⟩
  | 3 => ⟨((-291470455/2147483648), (656548525/4294967296)), (55/4294967296), by norm_num⟩
  | 4 => ⟨((130561237/2147483648), (-294094259/4294967296)), (51/8589934592), by norm_num⟩
  | 5 => ⟨((-748589865/34359738368), (421556939/17179869184)), (75/34359738368), by norm_num⟩
  | 6 => ⟨((111774415/17179869184), (-503552425/68719476736)), (23/34359738368), by norm_num⟩
  | 7 => ⟨((-57220819/34359738368), (64446059/34359738368)), (3/17179869184), by norm_num⟩
  | 8 => ⟨((410103777/1099511627776), (-230943673/549755813888)), (11/274877906944), by norm_num⟩
  | 9 => ⟨((-653162067/8796093022208), (183909117/2199023255552)), (9/1099511627776), by norm_num⟩
  | 10 => ⟨((936247455/70368744177664), (-527233443/35184372088832)), (105/70368744177664), by norm_num⟩
  | 11 => ⟨((-305005499/140737488355328), (343518369/140737488355328)), (35/140737488355328), by norm_num⟩
  | 12 => ⟨((182165497/562949953421312), (-820669721/2251799813685248)), (85/2251799813685248), by norm_num⟩
  | 13 => ⟨((-200859541/4503599627370496), (452443921/9007199254740992)), (3/562949953421312), by norm_num⟩
  | 14 => ⟨((822610251/144115188075855872), (-926480777/144115188075855872)), (25/36028797018963968), by norm_num⟩
  | 15 => ⟨((-393045255/576460752303423488), (442674855/576460752303423488)), (49/576460752303423488), by norm_num⟩
  | 16 => ⟨((352121279/4611686018427387904), (-793166863/9223372036854775808)), (45/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-1100334209631/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222448046978229/79228162514264337593543950336), (-1303325685885/633825300114114700748351602688)), (11541/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890659259351019/39614081257132168796771975168), (-1466040591973/39614081257132168796771975168)), (51939/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945245746987877/1237940039285380274899124224), (-778711235069/1237940039285380274899124224)), (55191/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443039386161969/38685626227668133590597632), (-1557146166795/154742504910672534362390528)), (55195/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387614910708381/2417851639229258349412352), (-729765510807/4835703278458516698824704)), (6469/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157447676590463/75557863725914323419136), (-319199051129/151115727451828646838272)), (45289/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472269958478547/18889465931478580854784), (-2074243782949/75557863725914323419136)), (18401/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298504948377279/4722366482869645213696), (-1555201693431/4722366482869645213696)), (55213/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622775106769665/590295810358705651712), (-1068810374965/295147905179352825856)), (18983/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825132512759233/73786976294838206464), (-2670854059615/73786976294838206464)), (47469/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912260424293817/4611686018427387904), (-1501550140515/4611686018427387904)), (26709/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595767879863525/1152921504606846976), (-1500544152155/576460752303423488)), (106875/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196138371641651/144115188075855872), (-2623690432349/144115188075855872)), (11695/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493970502399985/36028797018963968), (-491377009699/4503599627370496)), (140429/36028797018963968), by norm_num⟩
  | 3 => ⟨((746084134266107/4503599627370496), (-4905870058205/9007199254740992)), (175691/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233751924841539/4503599627370496), (-4894038401449/2251799813685248)), (175923/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224766284836959/2251799813685248), (-913942847329/140737488355328)), (66117/281474976710656), by norm_num⟩
  | 0 => ⟨((2197885914454299/2251799813685248), (-14505411480879/1125899906842624)), (1062551/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197885914454299/2251799813685248), (-14505411480879/1125899906842624)), (4053310402877043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2144889095271415/2251799813685248), (-56632457971495/2251799813685248)), (2101601/2251799813685248), by norm_num⟩
  | 2 => ⟨((1020814987144533/1125899906842624), (-107887335990743/2251799813685248)), (2054677/1125899906842624), by norm_num⟩
  | 3 => ⟨((922953552395443/1125899906842624), (-195635524673407/2251799813685248)), (3922697/1125899906842624), by norm_num⟩
  | 4 => ⟨((46755651864117/70368744177664), (-320743436205481/2251799813685248)), (7112847/1125899906842624), by norm_num⟩
  | 5 => ⟨((474216402350643/1125899906842624), (-426228110681111/2251799813685248)), (22956757/2251799813685248), by norm_num⟩
  | 6 => ⟨((9962230800003/70368744177664), (-718089982953203/4503599627370496)), (28028919/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1293316181/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-1404584223/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-220306039549291/2251799813685248), (358018163344947/2251799813685248)), (37498049/1125899906842624), by norm_num⟩
  | 1 => ⟨((204418067/1073741824), (-664397409/2147483648)), (281/4294967296), by norm_num⟩
  | 2 => ⟨((-795558383/4294967296), (1292857661/4294967296)), (69/1073741824), by norm_num⟩
  | 3 => ⟨((516028377/4294967296), (-209648737/1073741824)), (45/1073741824), by norm_num⟩
  | 4 => ⟨((-125518107/2147483648), (407957605/4294967296)), (177/8589934592), by norm_num⟩
  | 5 => ⟨((781590267/34359738368), (-635079075/17179869184)), (139/17179869184), by norm_num⟩
  | 6 => ⟨((-31685509/4294967296), (205967803/17179869184)), (91/34359738368), by norm_num⟩
  | 7 => ⟨((563722547/274877906944), (-916102487/274877906944)), (51/68719476736), by norm_num⟩
  | 8 => ⟨((-548476713/1099511627776), (222831641/274877906944)), (25/137438953472), by norm_num⟩
  | 9 => ⟨((59293689/549755813888), (-3011183/17179869184)), (175/4398046511104), by norm_num⟩
  | 10 => ⟨((-92304153/4398046511104), (18750373/549755813888)), (137/17592186044416), by norm_num⟩
  | 11 => ⟨((522518075/140737488355328), (-849141321/140737488355328)), (49/35184372088832), by norm_num⟩
  | 12 => ⟨((-677848817/1125899906842624), (275392119/281474976710656)), (1/4398046511104), by norm_num⟩
  | 13 => ⟨((811712549/9007199254740992), (-1319109709/9007199254740992)), (309/9007199254740992), by norm_num⟩
  | 14 => ⟨((-451291339/36028797018963968), (366695567/18014398509481984)), (87/18014398509481984), by norm_num⟩
  | 15 => ⟨((117089653/72057594037927936), (-761127067/288230376151711744)), (91/144115188075855872), by norm_num⟩
  | 16 => ⟨((-28480743/144115188075855872), (370271221/1152921504606846976)), (179/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (1382347971885/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779374436856341/633825300114114700748351602688), (3274013697835/633825300114114700748351602688)), (46261/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945211416725103/19807040628566084398385987584), (3682709392839/39614081257132168796771975168)), (104109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945119988392735/1237940039285380274899124224), (3912207434641/2475880078570760549798248448)), (110639/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771905673680987/154742504910672534362390528), (977863070311/38685626227668133590597632)), (55333/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775111569062243/4835703278458516698824704), (1833092130261/4835703278458516698824704)), (51889/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259374095661975/604462909807314587353088), (400888635525/75557863725914323419136)), (45417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472185560059567/18889465931478580854784), (2605024237415/37778931862957161709568)), (147659/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298251138102713/4722366482869645213696), (3906220775163/4722366482869645213696)), (13849/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405606279794665/147573952589676412928), (5368916183267/590295810358705651712)), (152415/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824693532219667/73786976294838206464), (209623122485/2305843009213693952)), (190633/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456006235270315/2305843009213693952), (3771013175849/4611686018427387904)), (214619/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595269408360799/1152921504606846976), (1884130161345/288230376151711744)), (214817/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195699330080075/144115188075855872), (3294132106603/72057594037927936)), (188187/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493306195798109/36028797018963968), (9870020044595/36028797018963968)), (282725/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491327863688049/9007199254740992), (12315881057287/9007199254740992)), (44273/1125899906842624), by norm_num⟩
  | 2 => ⟨((1116020586816349/2251799813685248), (6141722038673/1125899906842624)), (177677/1125899906842624), by norm_num⟩
  | 1 => ⟨((555531433685089/562949953421312), (18344175458675/1125899906842624)), (535961/1125899906842624), by norm_num⟩
  | 0 => ⟨((274038712155345/281474976710656), (9091250219135/281474976710656)), (135459/140737488355328), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274038712155345/281474976710656), (9091250219135/281474976710656)), (516735077441167787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1066021083733135/1125899906842624), (35404276871045/562949953421312)), (272511/140737488355328), by norm_num⟩
  | 2 => ⟨((1004873606263353/1125899906842624), (134085473742329/1125899906842624)), (550313/140737488355328), by norm_num⟩
  | 3 => ⟨((1761776591806117/2251799813685248), (119672230833409/562949953421312)), (17814273/2251799813685248), by norm_num⟩
  | 4 => ⟨((638314662041153/1125899906842624), (374519499806635/1125899906842624)), (35449213/2251799813685248), by norm_num⟩
  | 5 => ⟨((59326044530583/281474976710656), (849316307760595/2251799813685248)), (63778627/2251799813685248), by norm_num⟩
  | 6 => ⟨((-220306039549291/2251799813685248), (358018163344947/2251799813685248)), (37498049/1125899906842624), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1404584223/33554432)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-750484493/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1096415128299273/9007199254740992), (-510774240444647/4503599627370496)), (166121757/9007199254740992), by norm_num⟩
  | 1 => ⟨((-543577949/2147483648), (1012921499/4294967296)), (21/536870912), by norm_num⟩
  | 2 => ⟨((141292321/536870912), (-526577761/2147483648)), (89/2147483648), by norm_num⟩
  | 3 => ⟨((-48968187/268435456), (729991781/4294967296)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((407305929/4294967296), (-758987617/8589934592)), (133/8589934592), by norm_num⟩
  | 5 => ⟨((-677575095/17179869184), (78913519/2147483648)), (113/17179869184), by norm_num⟩
  | 6 => ⟨((939318533/68719476736), (-875178931/68719476736)), (5/2147483648), by norm_num⟩
  | 7 => ⟨((-139518427/34359738368), (519966693/137438953472)), (97/137438953472), by norm_num⟩
  | 8 => ⟨((290120413/274877906944), (-540620171/549755813888)), (103/549755813888), by norm_num⟩
  | 9 => ⟨((-268128195/1099511627776), (999278259/4398046511104)), (97/2199023255552), by norm_num⟩
  | 10 => ⟨((223022763/4398046511104), (-831176289/17592186044416)), (41/4398046511104), by norm_num⟩
  | 11 => ⟨((-337282035/35184372088832), (628502729/70368744177664)), (63/35184372088832), by norm_num⟩
  | 12 => ⟨((935144367/562949953421312), (-871289789/562949953421312)), (177/562949953421312), by norm_num⟩
  | 13 => ⟨((-299165853/1125899906842624), (139368937/562949953421312)), (115/2251799813685248), by norm_num⟩
  | 14 => ⟨((88871129/2251799813685248), (-662421845/18014398509481984)), (139/18014398509481984), by norm_num⟩
  | 15 => ⟨((-24640309/4503599627370496), (734649335/144115188075855872)), (39/36028797018963968), by norm_num⟩
  | 16 => ⟨((409904657/576460752303423488), (-763830173/1152921504606846976)), (41/288230376151711744), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-977042710075/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779201808009583/633825300114114700748351602688), (-1156815671311/633825300114114700748351602688)), (46157/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890228945495111/39614081257132168796771975168), (-1301212188625/39614081257132168796771975168)), (103861/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945017188805457/1237940039285380274899124224), (-691142487191/1237940039285380274899124224)), (110361/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442925132969059/38685626227668133590597632), (-1382000458773/154742504910672534362390528)), (55185/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550031303400805/9671406556917033397649408), (-161915401299/1208925819614629174706176)), (103483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629603362865153/302231454903657293676544), (-35409552415/18889465931478580854784)), (90557/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888471173754381/75557863725914323419136), (-460182603787/18889465931478580854784)), (73587/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298048633621629/4722366482869645213696), (-43126639887/147573952589676412928)), (110397/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202768495868901/73786976294838206464), (-1896767585517/590295810358705651712)), (151823/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824349027229847/73786976294838206464), (-2369753239539/73786976294838206464)), (189819/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823640030982539/9223372036854775808), (-2664314805059/9223372036854775808)), (106801/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797443908130551/576460752303423488), (-665561077017/288230376151711744)), (26709/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195369163532545/144115188075855872), (-2327136507381/144115188075855872)), (93521/72057594037927936), by norm_num⟩
  | 4 => ⟨((373204595887149/9007199254740992), (-1743027674743/18014398509481984)), (17545/2251799813685248), by norm_num⟩
  | 3 => ⟨((745365539638439/4503599627370496), (-4349444207767/9007199254740992)), (43897/1125899906842624), by norm_num⟩
  | 2 => ⟨((2230886408324139/4503599627370496), (-8674559380315/4503599627370496)), (175795/1125899906842624), by norm_num⟩
  | 1 => ⟨((2220490109352937/2251799813685248), (-6475588428939/1125899906842624)), (1056851/2251799813685248), by norm_num⟩
  | 0 => ⟨((547355406778669/562949953421312), (-25660664867689/2251799813685248)), (1061029/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547355406778669/562949953421312), (-25660664867689/2251799813685248)), (4047504429343795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2128478989307691/2251799813685248), (-49899652967387/2251799813685248)), (4174913/2251799813685248), by norm_num⟩
  | 2 => ⟨((2010806113864849/2251799813685248), (-94333752289469/2251799813685248)), (1009697/281474976710656), by norm_num⟩
  | 3 => ⟨((447913081151357/562949953421312), (-84237899254925/1125899906842624)), (15102967/2251799813685248), by norm_num⟩
  | 4 => ⟨((1412929310254053/2251799813685248), (-134048352879969/1125899906842624)), (26293413/2251799813685248), by norm_num⟩
  | 5 => ⟨((854646749875193/2251799813685248), (-336443489557657/2251799813685248)), (39257409/2251799813685248), by norm_num⟩
  | 6 => ⟨((1096415128299273/9007199254740992), (-510774240444647/4503599627370496)), (166121757/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-750484493/16777216)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile019Terms0
