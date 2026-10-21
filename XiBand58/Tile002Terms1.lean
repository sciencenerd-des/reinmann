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
namespace Reinmann.XiBand58.Tile002Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2403/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2403/160))
  have he : value ((15/16), (2403/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-69118709/33554432), (-553640857/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-14745767532645/9007199254740992), (-1148025652323699/9007199254740992)), (185332903/9007199254740992), by norm_num⟩
  | 1 => ⟨((15449411/4294967296), (150350939/536870912)), (49/1073741824), by norm_num⟩
  | 2 => ⟨((-16972913/4294967296), (-660709557/2147483648)), (217/4294967296), by norm_num⟩
  | 3 => ⟨((24862201/8589934592), (967818185/4294967296)), (5/134217728), by norm_num⟩
  | 4 => ⟨((-106695/67108864), (-132907119/1073741824)), (89/4294967296), by norm_num⟩
  | 5 => ⟨((24005927/34359738368), (934485723/17179869184)), (315/34359738368), by norm_num⟩
  | 6 => ⟨((-8791069/34359738368), (-1368849999/68719476736)), (233/68719476736), by norm_num⟩
  | 7 => ⟨((22075375/274877906944), (214833633/34359738368)), (295/274877906944), by norm_num⟩
  | 8 => ⟨((-12126139/549755813888), (-944075477/549755813888)), (327/1099511627776), by norm_num⟩
  | 9 => ⟨((23683423/4398046511104), (921931485/2199023255552)), (161/2199023255552), by norm_num⟩
  | 10 => ⟨((-1300945/1099511627776), (-810276207/8796093022208)), (143/8796093022208), by norm_num⟩
  | 11 => ⟨((1039443/4398046511104), (647403199/35184372088832)), (231/70368744177664), by norm_num⟩
  | 12 => ⟨((-12180745/281474976710656), (-474163407/140737488355328)), (341/562949953421312), by norm_num⟩
  | 13 => ⟨((16470051/2251799813685248), (1282268913/2251799813685248)), (233/2251799813685248), by norm_num⟩
  | 14 => ⟨((-10339543/9007199254740992), (-1609961583/18014398509481984)), (295/18014398509481984), by norm_num⟩
  | 15 => ⟨((24232851/144115188075855872), (1886638485/144115188075855872)), (87/36028797018963968), by norm_num⟩
  | 16 => ⟨((-6655627/288230376151711744), (-32385691/18014398509481984)), (385/1152921504606846976), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (-2062868016879/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778788589344575/633825300114114700748351602688), (-2441356360273/633825300114114700748351602688)), (92441/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889764013245191/39614081257132168796771975168), (-2746027301241/39614081257132168796771975168)), (104011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((3690508401899/4835703278458516698824704), (-2917040521911/2475880078570760549798248448)), (55265/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442801590046557/38685626227668133590597632), (-1458175266691/77371252455336267181195264)), (55275/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193695989463449/1208925819614629174706176), (-2733345698163/9671406556917033397649408)), (51831/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157350144985845/75557863725914323419136), (-597736192031/151115727451828646838272)), (45363/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887811938994907/75557863725914323419136), (-3883911846653/75557863725914323419136)), (147469/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324388510332463/1180591620717411303424), (-727933150699/1180591620717411303424)), (110637/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810733816461709/295147905179352825856), (-2000840538927/295147905179352825856)), (76091/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113968637881387/4611686018427387904), (-2499587963689/36893488147419103232)), (95157/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822682303648523/9223372036854775808), (-2810026415955/4611686018427387904)), (53555/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49810293719689/36028797018963968), (-5615031271461/1152921504606846976)), (6699/36028797018963968), by norm_num⟩
  | 5 => ⟨((1194529775149133/144115188075855872), (-4907507982443/144115188075855872)), (93869/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491557761418295/36028797018963968), (-3674992697355/18014398509481984)), (281939/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489152623236933/9007199254740992), (-572985944861/562949953421312)), (353005/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113860762159651/2251799813685248), (-9138269904017/2251799813685248)), (707759/4503599627370496), by norm_num⟩
  | 1 => ⟨((276965384247963/281474976710656), (-13633833130761/1125899906842624)), (533011/1125899906842624), by norm_num⟩
  | 0 => ⟨((544952508868307/562949953421312), (-53949050793815/2251799813685248)), (1074819/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((544952508868307/562949953421312), (-53949050793815/2251799813685248)), (4100109104636764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1054414620209219/1125899906842624), (-26112152956473/562949953421312)), (33319/17592186044416), by norm_num⟩
  | 2 => ⟨((492522828380465/562949953421312), (-97816993056357/1125899906842624)), (4191873/1125899906842624), by norm_num⟩
  | 3 => ⟨((1706629116734221/2251799813685248), (-85579724789023/562949953421312)), (503955/70368744177664), by norm_num⟩
  | 4 => ⟨((620703647006413/1125899906842624), (-518883958474163/2251799813685248)), (29347621/2251799813685248), by norm_num⟩
  | 5 => ⟨((35300970681785/140737488355328), (-572116870142091/2251799813685248)), (45883619/2251799813685248), by norm_num⟩
  | 6 => ⟨((-14745767532645/9007199254740992), (-1148025652323699/9007199254740992)), (185332903/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-553640857/16777216)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-9054133/4194304), (-1160377685/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-2079649504268681/18014398509481984), (25408671082895/9007199254740992)), (84473511/4503599627370496), by norm_num⟩
  | 1 => ⟨((1141684043/4294967296), (-27897657/4294967296)), (187/4294967296), by norm_num⟩
  | 2 => ⟨((-1314412329/4294967296), (32118365/4294967296)), (109/2147483648), by norm_num⟩
  | 3 => ⟨((1008848745/4294967296), (-6162939/1073741824)), (337/8589934592), by norm_num⟩
  | 4 => ⟨((-1161480041/8589934592), (28381383/8589934592)), (49/2147483648), by norm_num⟩
  | 5 => ⟨((1069762651/17179869184), (-6535055/4294967296)), (183/17179869184), by norm_num⟩
  | 6 => ⟨((-410536589/17179869184), (40126721/68719476736)), (283/68719476736), by norm_num⟩
  | 7 => ⟨((540168817/68719476736), (-13199313/68719476736)), (47/34359738368), by norm_num⟩
  | 8 => ⟨((-621892333/274877906944), (30392541/549755813888)), (109/274877906944), by norm_num⟩
  | 9 => ⟨((1272853347/2199023255552), (-15551425/1099511627776)), (225/2199023255552), by norm_num⟩
  | 10 => ⟨((-1172341257/8796093022208), (223803/68719476736)), (209/8796093022208), by norm_num⟩
  | 11 => ⟨((1963211275/70368744177664), (-47972115/70368744177664)), (353/70368744177664), by norm_num⟩
  | 12 => ⟨((-1506820339/281474976710656), (36819959/281474976710656)), (273/281474976710656), by norm_num⟩
  | 13 => ⟨((266890927/281474976710656), (-26086489/1125899906842624)), (195/1125899906842624), by norm_num⟩
  | 14 => ⟨((-351165183/2251799813685248), (34323635/9007199254740992)), (259/9007199254740992), by norm_num⟩
  | 15 => ⟨((1724987127/72057594037927936), (-42150981/72057594037927936)), (321/72057594037927936), by norm_num⟩
  | 16 => ⟨((-992982411/288230376151711744), (24264055/288230376151711744)), (93/144115188075855872), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (507556439511/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27791049348001/9903520314283042199192993792), (600583333153/79228162514264337593543950336)), (92673/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944790960281037/19807040628566084398385987584), (5404196536487/39614081257132168796771975168)), (3259/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((944673097029311/1237940039285380274899124224), (5740690459931/2475880078570760549798248448)), (110841/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27672055305221/2417851639229258349412352), (5739263528077/154742504910672534362390528)), (110881/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774692257188749/4835703278458516698824704), (1344760900061/2417851639229258349412352)), (103993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258639927348059/604462909807314587353088), (4705147369725/604462909807314587353088)), (22759/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943774259589091/37778931862957161709568), (7643022763739/75557863725914323419136)), (37003/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648677618952313/2361183241434822606848), (2864890475867/2361183241434822606848)), (55539/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405298066978137/147573952589676412928), (3937204785043/295147905179352825856)), (152845/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911575494260013/36893488147419103232), (9836954346805/73786976294838206464)), (191225/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822287550017569/9223372036854775808), (2764561610435/2305843009213693952)), (215359/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593529488145627/1152921504606846976), (5523920243735/576460752303423488)), (215649/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149271758129431/18014398509481984), (1206894740923/18014398509481984)), (189021/144115188075855872), by norm_num⟩
  | 4 => ⟨((745506327290599/18014398509481984), (14459342433905/36028797018963968)), (284185/36028797018963968), by norm_num⟩
  | 3 => ⟨((744225559662255/4503599627370496), (18033261576803/9007199254740992)), (178189/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113129232538915/2251799813685248), (17971934838699/2251799813685248)), (358101/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106689719060829/1125899906842624), (26804754579331/1125899906842624)), (541471/1125899906842624), by norm_num⟩
  | 0 => ⟨((67954157694547/70368744177664), (52997943834783/1125899906842624)), (550143/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((67954157694547/70368744177664), (52997943834783/1125899906842624)), (2098628999950218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1047464080122553/1125899906842624), (102358814980209/1125899906842624)), (2228649/1125899906842624), by norm_num⟩
  | 2 => ⟨((965186750206145/1125899906842624), (190455974503719/1125899906842624)), (4552007/1125899906842624), by norm_num⟩
  | 3 => ⟨((397598391787807/562949953421312), (163269915888077/562949953421312)), (18689029/2251799813685248), by norm_num⟩
  | 4 => ⟨((233461988795637/562949953421312), (461254899053855/1125899906842624)), (37239845/2251799813685248), by norm_num⟩
  | 5 => ⟨((18694091424985/4503599627370496), (1530302797545513/4503599627370496)), (61400197/2251799813685248), by norm_num⟩
  | 6 => ⟨((-2079649504268681/18014398509481984), (25408671082895/9007199254740992)), (84473511/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-1160377685/33554432)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-75431263/33554432), (-1208408833/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-54540058170035/4503599627370496), (1889903873542263/18014398509481984)), (316761115/18014398509481984), by norm_num⟩
  | 1 => ⟨((31180703/1073741824), (-540231653/2147483648)), (183/4294967296), by norm_num⟩
  | 2 => ⟨((-149536121/4294967296), (1295418927/4294967296)), (221/4294967296), by norm_num⟩
  | 3 => ⟨((59761993/2147483648), (-1035426307/4294967296)), (89/2147483648), by norm_num⟩
  | 4 => ⟨((-143303001/8589934592), (1241421923/8589934592)), (27/1073741824), by norm_num⟩
  | 5 => ⟨((137450235/17179869184), (-37209997/536870912)), (209/17179869184), by norm_num⟩
  | 6 => ⟨((-219727513/68719476736), (951740543/34359738368)), (337/68719476736), by norm_num⟩
  | 7 => ⟨((150538161/137438953472), (-652049757/68719476736)), (233/137438953472), by norm_num⟩
  | 8 => ⟨((-45121843/137438953472), (781773515/274877906944)), (141/274877906944), by norm_num⟩
  | 9 => ⟨((192351029/2199023255552), (-1666320903/2199023255552)), (303/2199023255552), by norm_num⟩
  | 10 => ⟨((-184495049/8796093022208), (1598265207/8796093022208)), (293/8796093022208), by norm_num⟩
  | 11 => ⟨((160872657/35184372088832), (-696813197/17592186044416)), (129/17592186044416), by norm_num⟩
  | 12 => ⟨((-128585261/140737488355328), (1113923381/140737488355328)), (13/8796093022208), by norm_num⟩
  | 13 => ⟨((94871997/562949953421312), (-1643736375/1125899906842624)), (309/1125899906842624), by norm_num⟩
  | 14 => ⟨((-129996065/4503599627370496), (281536263/1125899906842624)), (107/2251799813685248), by norm_num⟩
  | 15 => ⟨((10390565/2251799813685248), (-1440201545/36028797018963968)), (69/9007199254740992), by norm_num⟩
  | 16 => ⟨((-99661947/144115188075855872), (863363119/144115188075855872)), (167/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (274480176383/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778498188509183/633825300114114700748351602688), (2597920444427/633825300114114700748351602688)), (11557/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889437351505033/39614081257132168796771975168), (182630232557/2475880078570760549798248448)), (52015/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889193268826493/2475880078570760549798248448), (388000197175/309485009821345068724781056)), (110551/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221357422257837/19342813113834066795298816), (3103200393985/154742504910672534362390528)), (27643/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549242673977065/9671406556917033397649408), (2908399350379/9671406556917033397649408)), (25921/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258516627395961/604462909807314587353088), (2543998680719/604462909807314587353088)), (45373/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887349675019099/75557863725914323419136), (4132403267915/75557863725914323419136)), (147505/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648603716016149/2361183241434822606848), (774476938917/1180591620717411303424)), (55333/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25327987332863/9223372036854775808), (4257357851621/590295810358705651712)), (152227/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455725716978389/18446744073709551616), (5318301213141/73786976294838206464)), (95187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911006422897993/4611686018427387904), (2989211129195/4611686018427387904)), (214297/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593260313409053/1152921504606846976), (5972593547691/1152921504606846976)), (107227/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193944744291611/144115188075855872), (2609734151803/72057594037927936)), (11739/9007199254740992), by norm_num⟩
  | 4 => ⟨((1490681054000523/36028797018963968), (3908057982801/18014398509481984)), (282089/36028797018963968), by norm_num⟩
  | 3 => ⟨((11625454755107/70368744177664), (9747278695753/9007199254740992)), (22077/562949953421312), by norm_num⟩
  | 2 => ⟨((2225537110839991/4503599627370496), (19426098842259/4503599627370496)), (708327/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212457515901769/2251799813685248), (7242123009923/562949953421312)), (533581/1125899906842624), by norm_num⟩
  | 0 => ⟨((2173323303366559/2251799813685248), (57257294708933/2251799813685248)), (538271/562949953421312), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2173323303366559/2251799813685248), (57257294708933/2251799813685248)), (2053340914012718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1048062921595593/1125899906842624), (27630922634059/562949953421312)), (4265591/2251799813685248), by norm_num⟩
  | 2 => ⟨((1945789336021613/2251799813685248), (6430177613089/70368744177664)), (4180063/1125899906842624), by norm_num⟩
  | 3 => ⟨((415640480213619/562949953421312), (44450740078167/281474976710656)), (15975907/2251799813685248), by norm_num⟩
  | 4 => ⟨((1171354821978957/2251799813685248), (525106058601639/2251799813685248)), (894897/70368744177664), by norm_num⟩
  | 5 => ⟨((973741750514639/4503599627370496), (546305679621457/2251799813685248)), (86297279/4503599627370496), by norm_num⟩
  | 6 => ⟨((-54540058170035/4503599627370496), (1889903873542263/18014398509481984)), (316761115/18014398509481984), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-1208408833/33554432)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-19542101/8388608), (-313064459/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((407261442989109/4503599627370496), (324311317047057/9007199254740992)), (18952785/2251799813685248), by norm_num⟩
  | 1 => ⟨((-965124767/4294967296), (-192137563/2147483648)), (23/1073741824), by norm_num⟩
  | 2 => ⟨((1199122475/4294967296), (119360977/1073741824)), (117/4294967296), by norm_num⟩
  | 3 => ⟨((-248308951/1073741824), (-395467847/4294967296)), (99/4294967296), by norm_num⟩
  | 4 => ⟨((1234049127/8589934592), (491350341/8589934592)), (125/8589934592), by norm_num⟩
  | 5 => ⟨((-38331211/536870912), (-122095973/4294967296)), (127/17179869184), by norm_num⟩
  | 6 => ⟨((1015994465/34359738368), (101132365/8589934592)), (107/34359738368), by norm_num⟩
  | 7 => ⟨((-180332243/17179869184), (-287205127/68719476736)), (77/68719476736), by norm_num⟩
  | 8 => ⟨((896217579/274877906944), (356838965/274877906944)), (49/137438953472), by norm_num⟩
  | 9 => ⟨((-989785343/1099511627776), (-394094007/1099511627776)), (55/549755813888), by norm_num⟩
  | 10 => ⟨((122976209/549755813888), (391714727/4398046511104)), (111/4398046511104), by norm_num⟩
  | 11 => ⟨((-444486399/8796093022208), (-176977187/8796093022208)), (103/17592186044416), by norm_num⟩
  | 12 => ⟨((736338139/70368744177664), (586362385/140737488355328)), (173/140737488355328), by norm_num⟩
  | 13 => ⟨((-1125988639/562949953421312), (-224162429/281474976710656)), (135/562949953421312), by norm_num⟩
  | 14 => ⟨((399710951/1125899906842624), (79574673/562949953421312)), (49/1125899906842624), by norm_num⟩
  | 15 => ⟨((-1059460693/18014398509481984), (-421836019/18014398509481984)), (33/4503599627370496), by norm_num⟩
  | 16 => ⟨((329082615/36028797018963968), (131027891/36028797018963968)), (83/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (493585739619/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778375914146817/633825300114114700748351602688), (36492953169/39614081257132168796771975168)), (46129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944650006446531/19807040628566084398385987584), (656740389857/39614081257132168796771975168)), (51897/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889047633612441/2475880078570760549798248448), (348810454767/1237940039285380274899124224)), (55143/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770714065515521/154742504910672534362390528), (697434516135/154742504910672534362390528)), (110291/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549106786075983/9671406556917033397649408), (326823442891/4835703278458516698824704)), (103403/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314599516961229/151115727451828646838272), (142935782655/151115727451828646838272)), (45241/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943578828574155/37778931862957161709568), (928711702249/75557863725914323419136)), (147043/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648531989662213/2361183241434822606848), (43513088705/295147905179352825856)), (110291/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620794851967635/590295810358705651712), (239190295905/147573952589676412928)), (9479/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822658809716183/73786976294838206464), (1195161874883/73786976294838206464)), (5925/2305843009213693952), by norm_num⟩
  | 7 => ⟨((455435038070623/2305843009213693952), (671736145677/4611686018427387904)), (13333/576460752303423488), by norm_num⟩
  | 6 => ⟨((49780936113293/36028797018963968), (5242646877/4503599627370496)), (53341/288230376151711744), by norm_num⟩
  | 5 => ⟨((298427700783721/36028797018963968), (1172830702109/144115188075855872)), (93367/72057594037927936), by norm_num⟩
  | 4 => ⟨((745167685808935/18014398509481984), (439051555675/9007199254740992)), (280183/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487635224584703/9007199254740992), (2189948332747/9007199254740992)), (175185/4503599627370496), by norm_num⟩
  | 2 => ⟨((139044898121081/281474976710656), (1091002319501/1125899906842624)), (701169/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211297020925449/2251799813685248), (3253219202897/1125899906842624)), (1052835/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171270080741889/2251799813685248), (3213857399055/562949953421312)), (65939/70368744177664), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2171270080741889/2251799813685248), (3213857399055/562949953421312)), (251537323266482331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1046773446023949/1125899906842624), (24791377535177/2251799813685248)), (4093269/2251799813685248), by norm_num⟩
  | 2 => ⟨((1946142792165571/2251799813685248), (23049078818163/1125899906842624)), (1925333/562949953421312), by norm_num⟩
  | 3 => ⟨((1681031637162063/2251799813685248), (79681681000963/2251799813685248)), (6813621/1125899906842624), by norm_num⟩
  | 4 => ⟨((626058803654989/1125899906842624), (59484606869053/1125899906842624)), (10655329/1125899906842624), by norm_num⟩
  | 5 => ⟨((344978452186551/1125899906842624), (33076529792743/562949953421312)), (25951475/2251799813685248), by norm_num⟩
  | 6 => ⟨((407261442989109/4503599627370496), (324311317047057/9007199254740992)), (18952785/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-313064459/8388608)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-40343165/16777216), (-1292595009/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((552953876898349/9007199254740992), (-596448665995441/9007199254740992)), (95074777/9007199254740992), by norm_num⟩
  | 1 => ⟨((-338148759/2147483648), (91186799/536870912)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((433667221/2147483648), (-467779043/2147483648)), (77/2147483648), by norm_num⟩
  | 3 => ⟨((-741556307/4294967296), (799886371/4294967296)), (67/2147483648), by norm_num⟩
  | 4 => ⟨((951027187/8589934592), (-1025834017/8589934592)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((-975734629/17179869184), (1052484921/17179869184)), (181/17179869184), by norm_num⟩
  | 6 => ⟨((834236637/34359738368), (-899856841/34359738368)), (157/34359738368), by norm_num⟩
  | 7 => ⟨((-38210263/4294967296), (659453493/68719476736)), (117/68719476736), by norm_num⟩
  | 8 => ⟨((196014779/68719476736), (-845732407/274877906944)), (19/34359738368), by norm_num⟩
  | 9 => ⟨((-893809745/1099511627776), (964115909/1099511627776)), (11/68719476736), by norm_num⟩
  | 10 => ⟨((917030693/4398046511104), (-989163393/4398046511104)), (183/4398046511104), by norm_num⟩
  | 11 => ⟨((-427661325/8796093022208), (461300729/8796093022208)), (173/17592186044416), by norm_num⟩
  | 12 => ⟨((731286427/70368744177664), (-24650271/2199023255552)), (75/35184372088832), by norm_num⟩
  | 13 => ⟨((-288571177/140737488355328), (77817473/35184372088832)), (15/35184372088832), by norm_num⟩
  | 14 => ⟨((211477273/562949953421312), (-57027965/140737488355328)), (179/2251799813685248), by norm_num⟩
  | 15 => ⟨((-578590395/9007199254740992), (624101727/9007199254740992)), (31/2251799813685248), by norm_num⟩
  | 16 => ⟨((742027531/72057594037927936), (-400197331/36028797018963968)), (161/72057594037927936), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (-1072337697895/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889129805419217/316912650057057350374175801344), (-158545589399/79228162514264337593543950336)), (92325/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59036536272211/1237940039285380274899124224), (-1426612582701/39614081257132168796771975168)), (51937/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59028393333517/77371252455336267181195264), (-757702081491/1237940039285380274899124224)), (13797/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((221321875007417/19342813113834066795298816), (-1514986172851/154742504910672534362390528)), (55193/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548976392567027/9671406556917033397649408), (-177481947429/1208925819614629174706176)), (103499/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258283953914333/604462909807314587353088), (-310482462737/151115727451828646838272)), (90573/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886972185313107/75557863725914323419136), (-1008652146667/37778931862957161709568)), (575/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1296924843408405/4722366482869645213696), (-756125422341/2361183241434822606848)), (110419/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620603488151965/590295810358705651712), (-519540907237/147573952589676412928)), (151855/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822419527282765/73786976294838206464), (-2595933840851/73786976294838206464)), (189863/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455367713283757/2305843009213693952), (-2917992859509/9223372036854775808)), (106829/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398180131007871/288230376151711744), (-2914954959509/1152921504606846976)), (213735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193474902264599/144115188075855872), (-636793014519/36028797018963968)), (187105/144115188075855872), by norm_num⟩
  | 4 => ⟨((744990612899067/18014398509481984), (-3813941276271/36028797018963968)), (280831/36028797018963968), by norm_num⟩
  | 3 => ⟨((92949501953477/562949953421312), (-4755520208339/9007199254740992)), (351343/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111915233718071/2251799813685248), (-4737706603545/2251799813685248)), (703603/4503599627370496), by norm_num⟩
  | 1 => ⟨((552490359476751/562949953421312), (-3531093205965/562949953421312)), (264427/562949953421312), by norm_num⟩
  | 0 => ⟨((1084292178726115/1125899906842624), (-27895677596133/2251799813685248)), (132793/140737488355328), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1084292178726115/1125899906842624), (-27895677596133/2251799813685248)), (506565094531011537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2088098559197761/2251799813685248), (-13432395212899/562949953421312)), (4144983/2251799813685248), by norm_num⟩
  | 2 => ⟨((1935016025218629/2251799813685248), (-99647099782733/2251799813685248)), (1971277/562949953421312), by norm_num⟩
  | 3 => ⟨((829193929820569/1125899906842624), (-171257439293047/2251799813685248)), (14249525/2251799813685248), by norm_num⟩
  | 4 => ⟨((1208331737997127/2251799813685248), (-126126335241147/1125899906842624)), (23156213/2251799813685248), by norm_num⟩
  | 5 => ⟨((620141351286611/2251799813685248), (-135360570635917/1125899906842624)), (30039619/2251799813685248), by norm_num⟩
  | 6 => ⟨((552953876898349/9007199254740992), (-596448665995441/9007199254740992)), (95074777/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-1292595009/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-83017565/33554432), (-1329941397/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-135570226640123/4503599627370496), (-1417284602473047/18014398509481984)), (267395683/18014398509481984), by norm_num⟩
  | 1 => ⟨((85300827/1073741824), (891755895/4294967296)), (85/2147483648), by norm_num⟩
  | 2 => ⟨((-450227545/4294967296), (-1176697465/4294967296)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((396058767/4294967296), (1035124023/4294967296)), (201/4294967296), by norm_num⟩
  | 4 => ⟨((-32663181/536870912), (-341468955/2147483648)), (67/2147483648), by norm_num⟩
  | 5 => ⟨((275840023/8589934592), (1441849837/17179869184)), (285/17179869184), by norm_num⟩
  | 6 => ⟨((-242652545/17179869184), (-1268374793/34359738368)), (253/34359738368), by norm_num⟩
  | 7 => ⟨((365927987/68719476736), (478187685/34359738368)), (193/68719476736), by norm_num⟩
  | 8 => ⟨((-120713117/68719476736), (-1261964715/274877906944)), (257/274877906944), by norm_num⟩
  | 9 => ⟨((283172299/549755813888), (1480176547/1099511627776)), (19/68719476736), by norm_num⟩
  | 10 => ⟨((-74730793/549755813888), (-781254153/2199023255552)), (81/1099511627776), by norm_num⟩
  | 11 => ⟨((573727555/17592186044416), (749736181/8796093022208)), (313/17592186044416), by norm_num⟩
  | 12 => ⟨((-252349985/35184372088832), (-1319064509/70368744177664)), (139/35184372088832), by norm_num⟩
  | 13 => ⟨((204912639/140737488355328), (1071103649/281474976710656)), (57/70368744177664), by norm_num⟩
  | 14 => ⟨((-77253743/281474976710656), (-6309607/8796093022208)), (87/562949953421312), by norm_num⟩
  | 15 => ⟨((434937721/9007199254740992), (568368285/4503599627370496)), (247/9007199254740992), by norm_num⟩
  | 16 => ⟨((-286956395/36028797018963968), (-187494561/9007199254740992)), (41/9007199254740992), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (-1261078156247/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222268583212877/79228162514264337593543950336), (-2982872910379/633825300114114700748351602688)), (46247/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889044157152257/39614081257132168796771975168), (-3355005445381/39614081257132168796771975168)), (104075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944387757838713/1237940039285380274899124224), (-3563793068057/2475880078570760549798248448)), (55301/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885220821415727/77371252455336267181195264), (-3562780649459/154742504910672534362390528)), (55313/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548851066290605/9671406556917033397649408), (-834757872249/2417851639229258349412352)), (51869/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258173989825255/604462909807314587353088), (-1460288774177/302231454903657293676544)), (90797/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886792925014085/75557863725914323419136), (-2371961829397/37778931862957161709568)), (73797/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296789901201699/4722366482869645213696), (-1778090259973/2361183241434822606848)), (110739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620417136126649/590295810358705651712), (-4886886055169/590295810358705651712)), (152335/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227773172430869/9223372036854775808), (-6104316873755/73786976294838206464)), (47631/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821205779225671/9223372036854775808), (-3430730455019/4611686018427387904)), (214483/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796226691414115/576460752303423488), (-6854097640295/1152921504606846976)), (26833/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193238834456577/144115188075855872), (-5989060271971/144115188075855872)), (94017/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489622501671225/36028797018963968), (-1120882669319/4503599627370496)), (282457/36028797018963968), by norm_num⟩
  | 3 => ⟨((23230243328149/140737488355328), (-11179948673751/9007199254740992)), (353785/9007199254740992), by norm_num⟩
  | 2 => ⟨((277861691967927/562949953421312), (-22273454382067/4503599627370496)), (44357/281474976710656), by norm_num⟩
  | 1 => ⟨((2208496504875021/2251799813685248), (-16597371034765/1125899906842624)), (534971/1125899906842624), by norm_num⟩
  | 0 => ⟨((2165419349163203/2251799813685248), (-8191465782203/281474976710656)), (1080735/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2165419349163203/2251799813685248), (-8191465782203/281474976710656)), (4122676853660201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2080445393996693/2251799813685248), (-15754471951715/281474976710656)), (1070729/562949953421312), by norm_num⟩
  | 2 => ⟨((957538053440455/1125899906842624), (-58222437727543/562949953421312)), (8393441/2251799813685248), by norm_num⟩
  | 3 => ⟨((802309076745531/1125899906842624), (-396128994056181/2251799813685248)), (8006407/1125899906842624), by norm_num⟩
  | 4 => ⟨((1073754968752773/2251799813685248), (-564557978132553/2251799813685248)), (28455099/2251799813685248), by norm_num⟩
  | 5 => ⟨((370469886878123/2251799813685248), (-1076822070034297/4503599627370496)), (82810839/4503599627370496), by norm_num⟩
  | 6 => ⟨((-135570226640123/4503599627370496), (-1417284602473047/18014398509481984)), (267395683/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-1329941397/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-85187893/33554432), (-1364710053/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1402133967252901/18014398509481984), (-119747975300687/9007199254740992)), (121325305/9007199254740992), by norm_num⟩
  | 1 => ⟨((226321767/1073741824), (38657609/1073741824)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-1225781413/4294967296), (-52343373/1073741824)), (27/536870912), by norm_num⟩
  | 3 => ⟨((553246267/2147483648), (23624747/536870912)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((-187277333/1073741824), (-255908003/8589934592)), (269/8589934592), by norm_num⟩
  | 5 => ⟨((811450271/8589934592), (17325293/1073741824)), (147/8589934592), by norm_num⟩
  | 6 => ⟨((-366241345/8589934592), (-125114035/17179869184)), (67/8589934592), by norm_num⟩
  | 7 => ⟨((1133485655/68719476736), (193608621/68719476736)), (105/34359738368), by norm_num⟩
  | 8 => ⟨((-383692007/68719476736), (-65537733/68719476736)), (287/274877906944), by norm_num⟩
  | 9 => ⟨((923606415/549755813888), (78879765/274877906944)), (87/274877906944), by norm_num⟩
  | 10 => ⟨((-1000469015/2199023255552), (-170888291/2199023255552)), (95/1099511627776), by norm_num⟩
  | 11 => ⟨((246301847/2199023255552), (21035185/1099511627776)), (189/8796093022208), by norm_num⟩
  | 12 => ⟨((-889330355/35184372088832), (-303809797/70368744177664)), (343/70368744177664), by norm_num⟩
  | 13 => ⟨((1482062305/281474976710656), (63287091/70368744177664)), (9/8796093022208), by norm_num⟩
  | 14 => ⟨((-1146714035/1125899906842624), (-195868137/1125899906842624)), (225/1125899906842624), by norm_num⟩
  | 15 => ⟨((1656191559/9007199254740992), (282891065/9007199254740992)), (41/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1121262471/36028797018963968), (-191520801/36028797018963968)), (7/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (-1935952586853/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889021278199809/316912650057057350374175801344), (-1144672052821/158456325028528675187087900672)), (92651/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59028889159165/1237940039285380274899124224), (-2574931532441/19807040628566084398385987584)), (52131/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888647886294239/2475880078570760549798248448), (-1367577375409/618970019642690137449562112)), (110811/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770313514676013/154742504910672534362390528), (-5468712216131/154742504910672534362390528)), (55425/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548730416636251/9671406556917033397649408), (-5125220949379/9671406556917033397649408)), (51981/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258067892360377/604462909807314587353088), (-4482871984555/604462909807314587353088)), (91007/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886619525769653/75557863725914323419136), (-910185898905/9444732965739290427392)), (147961/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648329492902597/2361183241434822606848), (-2729166974213/2361183241434822606848)), (111037/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101264732638763/36893488147419103232), (-7500690954837/590295810358705651712)), (152783/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910978253813079/36893488147419103232), (-9369089200359/73786976294838206464)), (191139/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820945410372267/9223372036854775808), (-10530915045047/9223372036854775808)), (53813/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796094706108703/576460752303423488), (-2629821025511/288230376151711744)), (107765/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193003819608511/144115188075855872), (-9191298326443/144115188075855872)), (188901/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489261926761909/36028797018963968), (-13760820855937/36028797018963968)), (283975/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486270826231839/9007199254740992), (-8577679138827/4503599627370496)), (11127/281474976710656), by norm_num⟩
  | 2 => ⟨((1110961106565743/2251799813685248), (-17086964371309/2251799813685248)), (178855/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103467919606135/1125899906842624), (-1591239980691/70368744177664)), (540691/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080944307416387/1125899906842624), (-50239524563581/1125899906842624)), (1097957/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1080944307416387/1125899906842624), (-50239524563581/1125899906842624)), (4188373569968795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1035541950773505/1125899906842624), (-24116765510977/281474976710656)), (2206221/1125899906842624), by norm_num⟩
  | 2 => ⟨((1888340573246007/2251799813685248), (-354900782946065/2251799813685248)), (138637/35184372088832), by norm_num⟩
  | 3 => ⟨((763805808563795/1125899906842624), (-595233682710931/2251799813685248)), (17678091/2251799813685248), by norm_num⟩
  | 4 => ⟨((439491579962049/1125899906842624), (-807608103605567/2251799813685248)), (16665715/1125899906842624), by norm_num⟩
  | 5 => ⟨((106919403482639/4503599627370496), (-1260989398033149/4503599627370496)), (24965141/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1402133967252901/18014398509481984), (-119747975300687/9007199254740992)), (121325305/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-1364710053/33554432)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile002Terms1
