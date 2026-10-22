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
namespace Reinmann.XiBand97.Tile038Terms0
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
  | 0 => ⟨((-20060163/33554432), (-308706647/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((278904837494953/562949953421312), (537813345299773/2251799813685248)), (13744325/562949953421312), by norm_num⟩
  | 1 => ⟨((-737465293/2147483648), (-355514339/2147483648)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((1022343977/8589934592), (492847523/8589934592)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((-236211615/8589934592), (-113871957/8589934592)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((163729415/34359738368), (39465013/17179869184)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((-726326927/1099511627776), (-10942025/34359738368)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((1342537231/17592186044416), (80900627/2199023255552)), (83/17592186044416), by norm_num⟩
  | 7 => ⟨((-531757655/70368744177664), (-512695237/140737488355328)), (17/35184372088832), by norm_num⟩
  | 8 => ⟨((737172639/1125899906842624), (177686629/562949953421312)), (49/1125899906842624), by norm_num⟩
  | 9 => ⟨((-113548697/2251799813685248), (-437912839/18014398509481984)), (31/9007199254740992), by norm_num⟩
  | 10 => ⟨((503718139/144115188075855872), (30353805/18014398509481984)), (71/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1015711441/4611686018427387904), (-244825069/2305843009213693952)), (73/4611686018427387904), by norm_num⟩
  | 12 => ⟨((117339587/9223372036854775808), (452532817/73786976294838206464)), (35/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-800823177/1180591620717411303424), (-386057657/1180591620717411303424)), (61/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((158596665/4722366482869645213696), (611645203/37778931862957161709568)), (99/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-469038213/302231454903657293676544), (-226112079/302231454903657293676544)), (75/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((325112515/4835703278458516698824704), (78364475/2417851639229258349412352)), (53/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (585140822309/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445262041804793/158456325028528675187087900672), (173542870947/158456325028528675187087900672)), (46135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946152952277091/19807040628566084398385987584), (780900702333/39614081257132168796771975168)), (811/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1892240911172149/2475880078570760549798248448), (207414086831/618970019642690137449562112)), (27575/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773906800596683/154742504910672534362390528), (829599371291/154742504910672534362390528)), (55153/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552099398966207/9671406556917033397649408), (194422219513/2417851639229258349412352)), (51709/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261016028027487/604462909807314587353088), (340208620413/302231454903657293676544)), (45249/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891410762587155/75557863725914323419136), (552782269049/37778931862957161709568)), (36767/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300252863850711/4722366482869645213696), (414537060435/2361183241434822606848)), (13789/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625178033897811/590295810358705651712), (569907800987/295147905179352825856)), (37923/295147905179352825856), by norm_num⟩
  | 8 => ⟨((114258467921675/4611686018427387904), (1424527566433/73786976294838206464)), (23705/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827898252635013/9223372036854775808), (200282613443/1152921504606846976)), (106689/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199893013365037/144115188075855872), (1601845237697/1152921504606846976)), (53355/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199091246367545/144115188075855872), (700573536333/72057594037927936)), (93395/144115188075855872), by norm_num⟩
  | 4 => ⟨((374599291751645/9007199254740992), (1050392941977/18014398509481984)), (140139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497696967134253/9007199254740992), (2624347251051/9007199254740992)), (175255/9007199254740992), by norm_num⟩
  | 2 => ⟨((2244795429344161/4503599627370496), (5243791849431/4503599627370496)), (87689/1125899906842624), by norm_num⟩
  | 1 => ⟨((560324205773833/562949953421312), (1963360111409/562949953421312)), (131687/562949953421312), by norm_num⟩
  | 0 => ⟨((557702049279887/562949953421312), (15657947369515/2251799813685248)), (1055961/2251799813685248), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557702049279887/562949953421312), (15657947369515/2251799813685248)), (4028171547896575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1104951694812493/1125899906842624), (31023963257919/2251799813685248)), (2106921/2251799813685248), by norm_num⟩
  | 2 => ⟨((1084179525085943/1125899906842624), (15223369578993/562949953421312)), (4193497/2251799813685248), by norm_num⟩
  | 3 => ⟨((260795438287215/281474976710656), (117274123570329/2251799813685248)), (1037877/281474976710656), by norm_num⟩
  | 4 => ⟨((1926973896161023/2251799813685248), (108658172082247/1125899906842624)), (8125429/1125899906842624), by norm_num⟩
  | 5 => ⟨((1628031932840989/2251799813685248), (11623005958087/70368744177664)), (30949961/2251799813685248), by norm_num⟩
  | 6 => ⟨((278904837494953/562949953421312), (537813345299773/2251799813685248)), (13744325/562949953421312), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-308706647/16777216)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-978576919/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-68724110509961/281474976710656), (339061703869235/1125899906842624)), (58311353/1125899906842624), by norm_num⟩
  | 1 => ⟨((576028079/2147483648), (-44405145/134217728)), (31/536870912), by norm_num⟩
  | 2 => ⟨((-316415763/2147483648), (24392019/134217728)), (69/2147483648), by norm_num⟩
  | 3 => ⟨((231745497/4294967296), (-1143354531/17179869184)), (205/17179869184), by norm_num⟩
  | 4 => ⟨((-254598451/17179869184), (628051669/34359738368)), (57/17179869184), by norm_num⟩
  | 5 => ⟨((447527979/137438953472), (-1103976451/274877906944)), (203/274877906944), by norm_num⟩
  | 6 => ⟨((-655546317/1099511627776), (808561397/1099511627776)), (151/1099511627776), by norm_num⟩
  | 7 => ⟨((823075703/8796093022208), (-507597421/4398046511104)), (3/137438953472), by norm_num⟩
  | 8 => ⟨((-452120541/35184372088832), (1115305529/70368744177664)), (213/70368744177664), by norm_num⟩
  | 9 => ⟨((883031435/562949953421312), (-1089145209/562949953421312)), (211/562949953421312), by norm_num⟩
  | 10 => ⟨((-776087349/4503599627370496), (957238649/4503599627370496)), (47/1125899906842624), by norm_num⟩
  | 11 => ⟨((620086617/36028797018963968), (-764824831/36028797018963968)), (153/36028797018963968), by norm_num⟩
  | 12 => ⟨((-908313037/576460752303423488), (140040993/72057594037927936)), (227/576460752303423488), by norm_num⟩
  | 13 => ⟨((307041189/2305843009213693952), (-378709553/2305843009213693952)), (39/1152921504606846976), by norm_num⟩
  | 14 => ⟨((-96376921/9223372036854775808), (475491393/36893488147419103232)), (99/36893488147419103232), by norm_num⟩
  | 15 => ⟨((903516755/1180591620717411303424), (-557206067/590295810358705651712)), (235/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-496307305/9444732965739290427392), (612153433/9444732965739290427392)), (131/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (2933561827397/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1780501704644871/633825300114114700748351602688), (3478175557537/633825300114114700748351602688)), (69407/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891690806605847/39614081257132168796771975168), (3912601529265/39614081257132168796771975168)), (78099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891586962922109/2475880078570760549798248448), (1039183848611/618970019642690137449562112)), (82999/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443313098740613/38685626227668133590597632), (4156281105201/154742504910672534362390528)), (20755/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193935675983515/1208925819614629174706176), (1948015396563/4835703278458516698824704)), (38927/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260478300174619/604462909807314587353088), (3408544132745/604462909807314587353088)), (34073/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890536044617067/75557863725914323419136), (5537978799771/75557863725914323419136)), (110779/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20306187957965/73786976294838206464), (4152691716189/4722366482869645213696)), (41561/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812136796747039/295147905179352825856), (5708663215403/590295810358705651712)), (114353/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827002998090113/73786976294838206464), (1783474176071/18446744073709551616)), (17879/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1826621539908089/9223372036854775808), (8022976091251/9223372036854775808)), (40259/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597864068414441/1152921504606846976), (2004913203821/288230376151711744)), (161193/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197967475238379/144115188075855872), (7013455950983/144115188075855872)), (141221/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496704045601329/36028797018963968), (10512699470811/36028797018963968)), (26523/4503599627370496), by norm_num⟩
  | 3 => ⟨((1495567524995255/9007199254740992), (6563883864033/4503599627370496)), (33231/1125899906842624), by norm_num⟩
  | 2 => ⟨((560124378841275/1125899906842624), (6554045132443/1125899906842624)), (266777/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117376348957177/1125899906842624), (4903220169097/281474976710656)), (201245/562949953421312), by norm_num⟩
  | 0 => ⟨((1108666424983279/1125899906842624), (4878547364357/140737488355328)), (814301/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108666424983279/1125899906842624), (4878547364357/140737488355328)), (3106311802390670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((34073244990065/35184372088832), (38430994674977/562949953421312)), (1660129/1125899906842624), by norm_num⟩
  | 2 => ⟨((1050663488056561/1125899906842624), (148869355231497/1125899906842624)), (3442069/1125899906842624), by norm_num⟩
  | 3 => ⟨((960770734266825/1125899906842624), (277842808373407/1125899906842624)), (1833589/281474976710656), by norm_num⟩
  | 4 => ⟨((375647858445479/562949953421312), (474186448350045/1125899906842624)), (16137195/1125899906842624), by norm_num⟩
  | 5 => ⟨((301618700166867/1125899906842624), (316417334692009/562949953421312)), (70257915/2251799813685248), by norm_num⟩
  | 6 => ⟨((-68724110509961/281474976710656), (339061703869235/1125899906842624)), (58311353/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-978576919/33554432)), (3/67108864), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-308706647/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((848533101264723/4503599627370496), (1065805176903165/4503599627370496)), (162995533/4503599627370496), by norm_num⟩
  | 1 => ⟨((-280455745/1073741824), (-352268149/1073741824)), (55/1073741824), by norm_num⟩
  | 2 => ⟨((194397109/1073741824), (976694697/4294967296)), (155/4294967296), by norm_num⟩
  | 3 => ⟨((-718644309/8589934592), (-902657567/8589934592)), (73/4294967296), by norm_num⟩
  | 4 => ⟨((498126277/17179869184), (156418637/4294967296)), (103/17179869184), by norm_num⟩
  | 5 => ⟨((-552439719/68719476736), (-346947639/34359738368)), (29/17179869184), by norm_num⟩
  | 6 => ⟨((63820339/34359738368), (641295407/274877906944)), (109/274877906944), by norm_num⟩
  | 7 => ⟨((-101112887/274877906944), (-1016027665/2199023255552)), (175/2199023255552), by norm_num⟩
  | 8 => ⟨((140172225/2199023255552), (704256711/8796093022208)), (123/8796093022208), by norm_num⟩
  | 9 => ⟨((-86364429/8796093022208), (-216957135/17592186044416)), (77/35184372088832), by norm_num⟩
  | 10 => ⟨((383124867/281474976710656), (962452649/562949953421312)), (173/562949953421312), by norm_num⟩
  | 11 => ⟨((-772543771/4503599627370496), (-970358313/4503599627370496)), (11/281474976710656), by norm_num⟩
  | 12 => ⟨((713982049/36028797018963968), (896801505/36028797018963968)), (41/9007199254740992), by norm_num⟩
  | 13 => ⟨((-609101101/288230376151711744), (-382532575/144115188075855872)), (71/144115188075855872), by norm_num⟩
  | 14 => ⟨((482510527/2305843009213693952), (2367423/9007199254740992)), (57/1152921504606846976), by norm_num⟩
  | 15 => ⟨((-89186883/4611686018427387904), (-7001483/288230376151711744)), (171/36893488147419103232), by norm_num⟩
  | 16 => ⟨((123639273/73786976294838206464), (310595725/147573952589676412928)), (15/36893488147419103232), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (1170281644617/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780123992382945/633825300114114700748351602688), (1386976482167/633825300114114700748351602688)), (92337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891266246271633/39614081257132168796771975168), (1560181617687/39614081257132168796771975168)), (6493/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((945568159241155/1237940039285380274899124224), (828745306805/1237940039285380274899124224)), (55195/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772802257686221/154742504910672534362390528), (828631498715/77371252455336267181195264)), (55201/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387765985722519/2417851639229258349412352), (388360563469/2417851639229258349412352)), (51757/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260110056876619/604462909807314587353088), (1359020206393/604462909807314587353088)), (90587/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944969329356155/37778931862957161709568), (68998581581/2361183241434822606848)), (73613/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299148872812497/4722366482869645213696), (1655569472215/4722366482869645213696)), (13805/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811830093716801/295147905179352825856), (2275763896151/590295810358705651712)), (75943/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826238390579151/73786976294838206464), (2843738959955/73786976294838206464)), (94953/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825764310976593/9223372036854775808), (3197878661499/9223372036854775808)), (213711/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798505264949931/576460752303423488), (799054940735/288230376151711744)), (106897/576460752303423488), by norm_num⟩
  | 5 => ⟨((299306194250425/36028797018963968), (698706744009/36028797018963968)), (46791/36028797018963968), by norm_num⟩
  | 4 => ⟨((747799142391935/18014398509481984), (8180687873/70368744177664)), (280933/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494199804284951/9007199254740992), (653640133555/1125899906842624)), (43937/1125899906842624), by norm_num⟩
  | 2 => ⟨((1118902715174683/2251799813685248), (10438705844583/4503599627370496)), (351989/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115411332746209/1125899906842624), (7804646123763/1125899906842624)), (529219/1125899906842624), by norm_num⟩
  | 0 => ⟨((2209903389624987/2251799813685248), (484749425905/35184372088832)), (1063393/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2209903389624987/2251799813685248), (484749425905/35184372088832)), (4056522373679732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((135522440635743/140737488355328), (30446739157987/1125899906842624)), (4233035/2251799813685248), by norm_num⟩
  | 2 => ⟨((2086363506297723/2251799813685248), (117274123570333/2251799813685248)), (8381301/2251799813685248), by norm_num⟩
  | 3 => ⟨((481743474040257/562949953421312), (108658172082251/1125899906842624)), (16404079/2251799813685248), by norm_num⟩
  | 4 => ⟨((407007983210249/562949953421312), (185968095329399/1125899906842624)), (7810443/562949953421312), by norm_num⟩
  | 5 => ⟨((557809674989909/1125899906842624), (134453336324949/562949953421312)), (13873913/562949953421312), by norm_num⟩
  | 6 => ⟨((848533101264723/4503599627370496), (1065805176903165/4503599627370496)), (162995533/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-308706647/8388608)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-716794637/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((86453895180747/1125899906842624), (1069294650844725/4503599627370496)), (10008231/562949953421312), by norm_num⟩
  | 1 => ⟨((-518345/4194304), (-410309637/1073741824)), (63/2147483648), by norm_num⟩
  | 2 => ⟨((427132977/4294967296), (1320735771/4294967296)), (13/536870912), by norm_num⟩
  | 3 => ⟨((-458296005/8589934592), (-1417094815/8589934592)), (57/4294967296), by norm_num⟩
  | 4 => ⟨((368799483/17179869184), (1140363061/17179869184)), (47/8589934592), by norm_num⟩
  | 5 => ⟨((-59355987/8589934592), (-367068709/17179869184)), (123/68719476736), by norm_num⟩
  | 6 => ⟨((254746069/137438953472), (1575398125/274877906944)), (67/137438953472), by norm_num⟩
  | 7 => ⟨((-234284561/549755813888), (-1448860269/1099511627776)), (63/549755813888), by norm_num⟩
  | 8 => ⟨((377066455/4398046511104), (291481331/1099511627776)), (103/4398046511104), by norm_num⟩
  | 9 => ⟨((-269717799/17592186044416), (-833993075/17592186044416)), (19/4398046511104), by norm_num⟩
  | 10 => ⟨((347275241/140737488355328), (1073808059/140737488355328)), (99/140737488355328), by norm_num⟩
  | 11 => ⟨((-203242887/562949953421312), (-1256892655/1125899906842624)), (59/562949953421312), by norm_num⟩
  | 12 => ⟨((218071205/4503599627370496), (674296897/4503599627370496)), (129/9007199254740992), by norm_num⟩
  | 13 => ⟨((-215982809/36028797018963968), (-1335678757/72057594037927936)), (65/36028797018963968), by norm_num⟩
  | 14 => ⟨((49658703/72057594037927936), (614197723/288230376151711744)), (121/576460752303423488), by norm_num⟩
  | 15 => ⟨((-170501545/2305843009213693952), (-1054413975/4611686018427387904)), (53/2305843009213693952), by norm_num⟩
  | 16 => ⟨((274411651/36893488147419103232), (424253457/18446744073709551616)), (87/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (204836892663/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779825929511485/633825300114114700748351602688), (242688453933/79228162514264337593543950336)), (11549/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((118183181676111/2475880078570760549798248448), (136495310515/2475880078570760549798248448)), (6497/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945389997232909/1237940039285380274899124224), (1160045676631/1237940039285380274899124224)), (863/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1772445904627553/154742504910672534362390528), (2319721366061/154742504910672534362390528)), (6905/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550729831071487/9671406556917033397649408), (2174345730091/9671406556917033397649408)), (12949/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314954419561099/151115727451828646838272), (951079765817/302231454903657293676544)), (22665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889463485776519/75557863725914323419136), (3090272542615/75557863725914323419136)), (73677/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298792442734109/4722366482869645213696), (2317059943023/4722366482869645213696)), (6909/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1623170014353691/590295810358705651712), (398113805025/73786976294838206464)), (76021/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456406387972623/18446744073709551616), (3979568054789/73786976294838206464)), (23765/18446744073709551616), by norm_num⟩
  | 7 => ⟨((57033584363529/288230376151711744), (4474856092465/9223372036854775808)), (53495/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596320709377359/1152921504606846976), (4472159792715/1152921504606846976)), (13381/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196620949535349/144115188075855872), (3910108078501/144115188075855872)), (93733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494692076606089/36028797018963968), (91548478585/562949953421312)), (70365/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493066231434021/9007199254740992), (7313283161921/9007199254740992)), (176143/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235535865059859/4503599627370496), (14594816856873/4503599627370496)), (352977/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227412332478561/2251799813685248), (170413884727/17592186044416)), (265599/1125899906842624), by norm_num⟩
  | 0 => ⟨((2203059165376869/2251799813685248), (43309715693211/2251799813685248)), (1069341/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203059165376869/2251799813685248), (43309715693211/2251799813685248)), (4079212197310637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((538635131461529/562949953421312), (84744536817101/2251799813685248)), (2133525/2251799813685248), by norm_num⟩
  | 2 => ⟨((2058292754455643/2251799813685248), (162168535414955/2251799813685248)), (530417/281474976710656), by norm_num⟩
  | 3 => ⟨((934867834071699/1125899906842624), (148232680106235/1125899906842624)), (8368563/2251799813685248), by norm_num⟩
  | 4 => ⟨((189183100236619/281474976710656), (492327830377657/2251799813685248)), (16100891/2251799813685248), by norm_num⟩
  | 5 => ⟨((454789320426419/1125899906842624), (661800252172025/2251799813685248)), (14341883/1125899906842624), by norm_num⟩
  | 6 => ⟨((86453895180747/1125899906842624), (1069294650844725/4503599627370496)), (10008231/562949953421312), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-716794637/16777216)), (1/33554432), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1595990213/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-434347401779797/2251799813685248), (409309604111003/4503599627370496)), (84942485/4503599627370496), by norm_num⟩
  | 1 => ⟨((742193289/2147483648), (-174852457/1073741824)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((-664915927/2147483648), (626587091/4294967296)), (135/4294967296), by norm_num⟩
  | 3 => ⟨((6205049/33554432), (-187115559/2147483648)), (41/2147483648), by norm_num⟩
  | 4 => ⟨((-1423098279/17179869184), (670532149/17179869184)), (149/17179869184), by norm_num⟩
  | 5 => ⟨((1019939927/34359738368), (-480572931/34359738368)), (27/8589934592), by norm_num⟩
  | 6 => ⟨((-609162341/68719476736), (71755925/17179869184)), (131/137438953472), by norm_num⟩
  | 7 => ⟨((1247397021/549755813888), (-587745637/549755813888)), (17/68719476736), by norm_num⟩
  | 8 => ⟨((-69844857/137438953472), (526549405/2199023255552)), (31/549755813888), by norm_num⟩
  | 9 => ⟨((222480327/2199023255552), (-419311059/8796093022208)), (25/2199023255552), by norm_num⟩
  | 10 => ⟨((-1275619945/70368744177664), (601043649/70368744177664)), (73/35184372088832), by norm_num⟩
  | 11 => ⟨((831128769/281474976710656), (-391609327/281474976710656)), (97/281474976710656), by norm_num⟩
  | 12 => ⟨((-496394281/1125899906842624), (467779813/2251799813685248)), (59/1125899906842624), by norm_num⟩
  | 13 => ⟨((34208429/562949953421312), (-64472993/2251799813685248)), (33/4503599627370496), by norm_num⟩
  | 14 => ⟨((-70049459/9007199254740992), (264045933/72057594037927936)), (137/144115188075855872), by norm_num⟩
  | 15 => ⟨((1071033869/1152921504606846976), (-252323627/576460752303423488)), (133/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-479758769/4611686018427387904), (28256453/576460752303423488)), (121/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (3518702649705/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779576001324043/633825300114114700748351602688), (2083919369321/316912650057057350374175801344)), (23153/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945324676272923/19807040628566084398385987584), (2344077173229/19807040628566084398385987584)), (52107/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890480351139199/2475880078570760549798248448), (2490187892585/1237940039285380274899124224)), (55379/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443036427047897/38685626227668133590597632), (311218059641/9671406556917033397649408)), (13849/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775223904767761/4835703278458516698824704), (4667328635225/9671406556917033397649408)), (3247/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259570322362033/604462909807314587353088), (2041485147279/302231454903657293676544)), (11369/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944530216245305/37778931862957161709568), (1658264996287/18889465931478580854784)), (18483/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298489191009503/4722366482869645213696), (4973249085035/4722366482869645213696)), (55479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25355491901895/9223372036854775808), (6835705392921/590295810358705651712)), (76333/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456275011548445/18446744073709551616), (8540863585033/73786976294838206464)), (95489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824480292187493/9223372036854775808), (9603290309187/9223372036854775808)), (107525/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595722290760441/1152921504606846976), (4798406885301/576460752303423488)), (53825/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196092828579233/144115188075855872), (2097481485053/36028797018963968)), (737/1125899906842624), by norm_num⟩
  | 4 => ⟨((1493890905582195/36028797018963968), (12570316710335/36028797018963968)), (141787/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492049080263077/9007199254740992), (490231082821/281474976710656)), (2777/140737488355328), by norm_num⟩
  | 2 => ⟨((139590917372187/281474976710656), (15649143196883/2251799813685248)), (178473/2251799813685248), by norm_num⟩
  | 1 => ⟨((556043490039189/562949953421312), (11689044186915/562949953421312)), (134787/562949953421312), by norm_num⟩
  | 0 => ⟨((1098059884983441/1125899906842624), (23186845362907/562949953421312)), (546631/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098059884983441/1125899906842624), (23186845362907/562949953421312)), (2085231785300826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((534499108003989/562949953421312), (11306753201411/140737488355328)), (277815/281474976710656), by norm_num⟩
  | 2 => ⟨((503852628543445/562949953421312), (171765165662675/1125899906842624)), (2288753/1125899906842624), by norm_num⟩
  | 3 => ⟨((437857134117005/562949953421312), (76866806441113/281474976710656)), (2397653/562949953421312), by norm_num⟩
  | 4 => ⟨((74644666522221/140737488355328), (14946568239541/35184372088832)), (10078547/1125899906842624), by norm_num⟩
  | 5 => ⟨((56770312709929/562949953421312), (1014706505786451/2251799813685248)), (38507681/2251799813685248), by norm_num⟩
  | 6 => ⟨((-434347401779797/2251799813685248), (409309604111003/4503599627370496)), (84942485/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1595990213/33554432)), (1/33554432), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-866649125/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((75244585819371/2251799813685248), (-1654327699830491/9007199254740992)), (253329049/9007199254740992), by norm_num⟩
  | 1 => ⟨((-279272467/4294967296), (767510667/2147483648)), (237/4294967296), by norm_num⟩
  | 2 => ⟨((67929891/1073741824), (-1493506797/4294967296)), (29/536870912), by norm_num⟩
  | 3 => ⟨((-88123643/2147483648), (968743345/4294967296)), (19/536870912), by norm_num⟩
  | 4 => ⟨((171480691/8589934592), (-471271877/4294967296)), (75/4294967296), by norm_num⟩
  | 5 => ⟨((-133474407/17179869184), (733642183/17179869184)), (59/8589934592), by norm_num⟩
  | 6 => ⟨((86576401/34359738368), (-951734513/68719476736)), (77/34359738368), by norm_num⟩
  | 7 => ⟨((-96268513/137438953472), (1058279913/274877906944)), (173/274877906944), by norm_num⟩
  | 8 => ⟨((187329877/1099511627776), (-257414703/274877906944)), (85/549755813888), by norm_num⟩
  | 9 => ⟨((-324024097/8796093022208), (222624837/1099511627776)), (37/1099511627776), by norm_num⟩
  | 10 => ⟨((31526089/4398046511104), (-1386265375/35184372088832)), (29/4398046511104), by norm_num⟩
  | 11 => ⟨((-178463815/140737488355328), (30653953/4398046511104)), (83/70368744177664), by norm_num⟩
  | 12 => ⟨((115758183/562949953421312), (-1272529883/1125899906842624)), (217/1125899906842624), by norm_num⟩
  | 13 => ⟨((-34654619/1125899906842624), (1523833117/9007199254740992)), (131/4503599627370496), by norm_num⟩
  | 14 => ⟨((38534157/9007199254740992), (-423606047/18014398509481984)), (147/36028797018963968), by norm_num⟩
  | 15 => ⟨((-79982941/144115188075855872), (879252593/288230376151711744)), (307/576460752303423488), by norm_num⟩
  | 16 => ⟨((311279233/4611686018427387904), (-106934159/288230376151711744)), (301/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-226464047755/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111211106653821/39614081257132168796771975168), (-1072734809899/316912650057057350374175801344)), (92411/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890426700029143/39614081257132168796771975168), (-2413293403637/39614081257132168796771975168)), (12997/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890244325714599/2475880078570760549798248448), (-640921216463/618970019642690137449562112)), (55245/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771910293229089/154742504910672534362390528), (-1281595332855/77371252455336267181195264)), (27627/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550227756335087/9671406556917033397649408), (-1201233132841/4835703278458516698824704)), (25905/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629689211906811/302231454903657293676544), (-525408279069/151115727451828646838272)), (90687/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888749811662751/75557863725914323419136), (-3414169938903/75557863725914323419136)), (18425/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649128643611243/2361183241434822606848), (-1279883406271/2361183241434822606848)), (110581/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622434338200187/590295810358705651712), (-1759140645719/295147905179352825856)), (152099/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912353100403759/36893488147419103232), (-2197877658701/36893488147419103232)), (190199/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824040765470711/9223372036854775808), (-2471171825431/4611686018427387904)), (214077/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398821798801697/288230376151711744), (-2469372144657/576460752303423488)), (107103/576460752303423488), by norm_num⟩
  | 5 => ⟨((597858548723743/72057594037927936), (-4317354706725/144115188075855872)), (23447/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493337244896189/36028797018963968), (-6467945802843/36028797018963968)), (281655/36028797018963968), by norm_num⟩
  | 3 => ⟨((372843587456297/2251799813685248), (-4035398338051/4503599627370496)), (176289/4503599627370496), by norm_num⟩
  | 2 => ⟨((558039270762449/1125899906842624), (-16099248073751/4503599627370496)), (706689/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222356637234595/2251799813685248), (-6010805959129/562949953421312)), (16623/35184372088832), by norm_num⟩
  | 0 => ⟨((137062364568219/140737488355328), (-23832571386713/1125899906842624)), (2143143/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((137062364568219/140737488355328), (-23832571386713/1125899906842624)), (8175441750533293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((533680603055189/562949953421312), (-92840894808539/2251799813685248)), (33321/17592186044416), by norm_num⟩
  | 2 => ⟨((2019904397294049/2251799813685248), (-176027671477657/2251799813685248)), (8438365/2251799813685248), by norm_num⟩
  | 3 => ⟨((899064829936067/1125899906842624), (-78949972706777/562949953421312)), (16458015/2251799813685248), by norm_num⟩
  | 4 => ⟨((1391571614679715/2251799813685248), (-252175680462143/1125899906842624)), (7725173/562949953421312), by norm_num⟩
  | 5 => ⟨((373501510501335/1125899906842624), (-155840015933455/562949953421312)), (52034229/2251799813685248), by norm_num⟩
  | 6 => ⟨((75244585819371/2251799813685248), (-1654327699830491/9007199254740992)), (253329049/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-866649125/16777216)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-926119941/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((1295615348483/35184372088832), (1461395719504765/9007199254740992)), (166951623/4503599627370496), by norm_num⟩
  | 1 => ⟨((-328876511/4294967296), (-724527113/2147483648)), (333/4294967296), by norm_num⟩
  | 2 => ⟨((85484935/1073741824), (1506611777/4294967296)), (349/4294967296), by norm_num⟩
  | 3 => ⟨((-237014567/4294967296), (-1044303705/4294967296)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((30803621/1073741824), (1085784253/8589934592)), (1/33554432), by norm_num⟩
  | 5 => ⟨((-204973853/17179869184), (-28222811/536870912)), (215/17179869184), by norm_num⟩
  | 6 => ⟨((284154097/68719476736), (156500495/8589934592)), (75/17179869184), by norm_num⟩
  | 7 => ⟨((-168823381/137438953472), (-1487696597/274877906944)), (359/274877906944), by norm_num⟩
  | 8 => ⟨((21941147/68719476736), (1546789053/1099511627776)), (47/137438953472), by norm_num⟩
  | 9 => ⟨((-324446809/4398046511104), (-357384157/1099511627776)), (175/2199023255552), by norm_num⟩
  | 10 => ⟨((269867269/17592186044416), (297263785/4398046511104)), (293/17592186044416), by norm_num⟩
  | 11 => ⟨((-204062985/70368744177664), (-899116601/70368744177664)), (7/2199023255552), by norm_num⟩
  | 12 => ⟨((282891365/562949953421312), (623220137/281474976710656)), (313/562949953421312), by norm_num⟩
  | 13 => ⟨((-362003727/4503599627370496), (-1595015191/4503599627370496)), (403/4503599627370496), by norm_num⟩
  | 14 => ⟨((107537941/9007199254740992), (473820121/9007199254740992)), (121/9007199254740992), by norm_num⟩
  | 15 => ⟨((-119263393/72057594037927936), (-1050966659/144115188075855872)), (135/72057594037927936), by norm_num⟩
  | 16 => ⟨((124000627/576460752303423488), (1092711865/1152921504606846976)), (283/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (877711233463/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779200213484873/633825300114114700748351602688), (2078414995139/633825300114114700748351602688)), (138607/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890227060375365/39614081257132168796771975168), (2337845660505/39614081257132168796771975168)), (9747/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((945016128674557/1237940039285380274899124224), (2483506252459/2475880078570760549798248448)), (82861/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885849139858371/77371252455336267181195264), (2482994763259/154742504910672534362390528)), (41437/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550029051937061/9671406556917033397649408), (581816063643/2417851639229258349412352)), (19427/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629602307861021/302231454903657293676544), (1017906511595/302231454903657293676544)), (136017/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888467482717379/75557863725914323419136), (1653588976677/37778931862957161709568)), (221077/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162255704504827/590295810358705651712), (1239746410815/2361183241434822606848)), (165853/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811071736499259/295147905179352825856), (3407855877439/590295810358705651712)), (28515/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912171425989123/36893488147419103232), (4257650668671/73786976294838206464)), (285259/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455908079453585/2305843009213693952), (2393437963047/4611686018427387904)), (321067/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24919986672629/18014398509481984), (4783151895643/1152921504606846976)), (321255/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195360504437367/144115188075855872), (522633944469/18014398509481984)), (140655/72057594037927936), by norm_num⟩
  | 4 => ⟨((373200813217979/9007199254740992), (3131621288341/18014398509481984)), (105597/9007199254740992), by norm_num⟩
  | 3 => ⟨((745354214339743/4503599627370496), (7814432769237/9007199254740992)), (528727/9007199254740992), by norm_num⟩
  | 2 => ⟨((278853742564135/562949953421312), (15585075615575/4503599627370496)), (529841/2251799813685248), by norm_num⟩
  | 1 => ⟨((277547206082817/281474976710656), (23268388356875/2251799813685248)), (1595109/2251799813685248), by norm_num⟩
  | 0 => ⟨((273635826488417/281474976710656), (46101372723479/2251799813685248)), (3212627/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((273635826488417/281474976710656), (46101372723479/2251799813685248)), (12255199440962981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((8309281835277/8796093022208), (44817437680819/1125899906842624)), (6377855/2251799813685248), by norm_num⟩
  | 2 => ⟨((2005881665891159/2251799813685248), (5292132539479/70368744177664)), (12557511/2251799813685248), by norm_num⟩
  | 3 => ⟨((1774084182110917/2251799813685248), (18856723532691/140737488355328)), (24261015/2251799813685248), by norm_num⟩
  | 4 => ⟨((1357290823504773/2251799813685248), (475401619521929/2251799813685248)), (22364695/1125899906842624), by norm_num⟩
  | 5 => ⟨((179437762396061/562949953421312), (143276114451845/562949953421312)), (36404309/1125899906842624), by norm_num⟩
  | 6 => ⟨((1295615348483/35184372088832), (1461395719504765/9007199254740992)), (166951623/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-926119941/16777216)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile038Terms0
