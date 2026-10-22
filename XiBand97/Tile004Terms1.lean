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
namespace Reinmann.XiBand97.Tile004Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (10277/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (10277/640))
  have he : value ((69/80), (10277/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1183888283/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-253307578947549/2251799813685248), (897857462902455/9007199254740992)), (245601453/9007199254740992), by norm_num⟩
  | 1 => ⟨((16587187/67108864), (-235175429/1073741824)), (65/1073741824), by norm_num⟩
  | 2 => ⟨((-583132399/2147483648), (516733233/2147483648)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((854181893/4294967296), (-756919307/4294967296)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((-938414725/8589934592), (207890213/2147483648)), (239/8589934592), by norm_num⟩
  | 5 => ⟨((824763159/17179869184), (-730850377/17179869184)), (53/4294967296), by norm_num⟩
  | 6 => ⟨((-604063295/34359738368), (133820201/8589934592)), (157/34359738368), by norm_num⟩
  | 7 => ⟨((758435839/137438953472), (-168018877/34359738368)), (199/137438953472), by norm_num⟩
  | 8 => ⟨((-833226933/549755813888), (184587603/137438953472)), (221/549755813888), by norm_num⟩
  | 9 => ⟨((25427593/68719476736), (-360515927/1099511627776)), (109/1099511627776), by norm_num⟩
  | 10 => ⟨((-715137693/8796093022208), (158426891/2199023255552)), (97/4398046511104), by norm_num⟩
  | 11 => ⟨((285694203/17592186044416), (-506326485/35184372088832)), (157/35184372088832), by norm_num⟩
  | 12 => ⟨((-836979099/281474976710656), (185418833/70368744177664)), (233/281474976710656), by norm_num⟩
  | 13 => ⟨((565855707/1125899906842624), (-501423775/1125899906842624)), (159/1125899906842624), by norm_num⟩
  | 14 => ⟨((-355232019/4503599627370496), (629566081/9007199254740992)), (101/4503599627370496), by norm_num⟩
  | 15 => ⟨((832559491/72057594037927936), (-737758969/72057594037927936)), (239/72057594037927936), by norm_num⟩
  | 16 => ⟨((-114332511/72057594037927936), (405255535/288230376151711744)), (265/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (3147750062315/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889519215399433/316912650057057350374175801344), (3726302182109/633825300114114700748351602688)), (92567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890044792583359/39614081257132168796771975168), (4191376580387/39614081257132168796771975168)), (104161/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236229782093865/309485009821345068724781056), (2226237397233/1237940039285380274899124224)), (110699/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885751947849163/77371252455336267181195264), (4451504188079/154742504910672534362390528)), (55365/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774923204896117/4835703278458516698824704), (260765877869/604462909807314587353088)), (103841/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314761099251531/151115727451828646838272), (3649691315735/604462909807314587353088)), (45447/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472051591273265/18889465931478580854784), (2964407821331/37778931862957161709568)), (147763/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297849131498061/4722366482869645213696), (1111230227901/1180591620717411303424)), (27719/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810936098814455/295147905179352825856), (1527254823231/147573952589676412928)), (76271/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824002137333545/73786976294838206464), (7632154765729/73786976294838206464)), (190807/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227905848625377/1152921504606846976), (1072563972247/1152921504606846976)), (107419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797245421038229/576460752303423488), (8573436523841/1152921504606846976)), (215063/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195017621116613/144115188075855872), (7493800962963/144115188075855872)), (188433/144115188075855872), by norm_num⟩
  | 4 => ⟨((186535338963329/4503599627370496), (11224798630255/36028797018963968)), (70789/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490046911552207/9007199254740992), (7001594522781/4503599627370496)), (22177/562949953421312), by norm_num⟩
  | 2 => ⟨((1114737267298931/2251799813685248), (1745189579377/281474976710656)), (178083/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109132067860103/1125899906842624), (5209559850969/281474976710656)), (537589/1125899906842624), by norm_num⟩
  | 0 => ⟨((546135277764125/562949953421312), (2578825787713/70368744177664)), (136073/140737488355328), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((546135277764125/562949953421312), (2578825787713/70368744177664)), (519077301562261537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((529066780966975/562949953421312), (80057574102621/1125899906842624)), (1095963/562949953421312), by norm_num⟩
  | 2 => ⟨((988753452197805/1125899906842624), (150478040774611/1125899906842624)), (2215855/562949953421312), by norm_num⟩
  | 3 => ⟨((424100642816377/562949953421312), (528592928702163/2251799813685248)), (17936741/2251799813685248), by norm_num⟩
  | 4 => ⟨((144238576611627/281474976710656), (796435276309561/2251799813685248)), (35446463/2251799813685248), by norm_num⟩
  | 5 => ⟨((619234386041965/4503599627370496), (816247980269075/2251799813685248)), (122804511/4503599627370496), by norm_num⟩
  | 6 => ⟨((-253307578947549/2251799813685248), (897857462902455/9007199254740992)), (245601453/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1183888283/33554432)), (1/16777216), by norm_num⟩, -6, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1240657665/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((231399669520951/2251799813685248), (819429539991699/9007199254740992)), (135324517/9007199254740992), by norm_num⟩
  | 1 => ⟨((-254067149/1073741824), (-899699327/4294967296)), (151/4294967296), by norm_num⟩
  | 2 => ⟨((292505615/1073741824), (517908565/2147483648)), (89/2147483648), by norm_num⟩
  | 3 => ⟨((-898025425/4294967296), (-198754757/1073741824)), (139/4294967296), by norm_num⟩
  | 4 => ⟨((1033889979/8589934592), (915299481/8589934592)), (163/8589934592), by norm_num⟩
  | 5 => ⟨((-476123931/8589934592), (-105377747/2147483648)), (153/17179869184), by norm_num⟩
  | 6 => ⟨((182719311/8589934592), (323521639/17179869184)), (15/4294967296), by norm_num⟩
  | 7 => ⟨((-480830585/68719476736), (-851355547/137438953472)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((1107153337/549755813888), (15314989/8589934592)), (187/549755813888), by norm_num⟩
  | 9 => ⟨((-1133028787/2199023255552), (-250766687/549755813888)), (97/1099511627776), by norm_num⟩
  | 10 => ⟨((521779039/4398046511104), (923858617/8796093022208)), (181/8796093022208), by norm_num⟩
  | 11 => ⟨((-873775009/35184372088832), (-773550211/35184372088832)), (77/17592186044416), by norm_num⟩
  | 12 => ⟨((10478861/2199023255552), (4638451/1099511627776)), (15/17592186044416), by norm_num⟩
  | 13 => ⟨((-950290477/1125899906842624), (-210322277/281474976710656)), (43/281474976710656), by norm_num⟩
  | 14 => ⟨((312589241/2251799813685248), (553468503/4503599627370496)), (115/4503599627370496), by norm_num⟩
  | 15 => ⟨((-191936887/9007199254740992), (-84960555/4503599627370496)), (9/2251799813685248), by norm_num⟩
  | 16 => ⟨((441951015/144115188075855872), (391257815/144115188075855872)), (21/36028797018963968), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (117989283165/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889452536001567/316912650057057350374175801344), (139654609081/79228162514264337593543950336)), (46155/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472473793966135/9903520314283042199192993792), (1256672828031/39614081257132168796771975168)), (6491/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472419954823801/618970019642690137449562112), (667472194917/1237940039285380274899124224)), (110355/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221418256805469/19342813113834066795298816), (333660047649/38685626227668133590597632)), (110365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193712383340471/1208925819614629174706176), (156362757603/1208925819614629174706176)), (103477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258916104528493/604462909807314587353088), (547108145467/302231454903657293676544)), (11319/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471999768823127/18889465931478580854784), (1777496048989/75557863725914323419136)), (147165/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297694700588639/4722366482869645213696), (333148128775/1180591620717411303424)), (55195/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810830768875925/295147905179352825856), (915727327855/295147905179352825856)), (37953/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823741333635841/73786976294838206464), (2288028975615/73786976294838206464)), (47451/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822956846897543/9223372036854775808), (1286130471429/4611686018427387904)), (13349/576460752303423488), by norm_num⟩
  | 6 => ⟨((1594205220757105/1152921504606846976), (1285024081581/576460752303423488)), (213651/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597386277015115/72057594037927936), (2246305222963/144115188075855872)), (187021/144115188075855872), by norm_num⟩
  | 4 => ⟨((372981197737199/9007199254740992), (3364490131941/36028797018963968)), (70171/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489616398108417/9007199254740992), (4196932976763/9007199254740992)), (175561/4503599627370496), by norm_num⟩
  | 2 => ⟨((557165990374107/1125899906842624), (4183940983849/2251799813685248)), (703047/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108586840817247/1125899906842624), (12487055374933/2251799813685248)), (264147/562949953421312), by norm_num⟩
  | 0 => ⟨((1091428732420815/1125899906842624), (24716191677845/2251799813685248)), (530321/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091428732420815/1125899906842624), (24716191677845/2251799813685248)), (2023014070750999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2115754603375107/2251799813685248), (11979733539933/562949953421312)), (4159243/2251799813685248), by norm_num⟩
  | 2 => ⟨((993454500320279/1125899906842624), (90047707545865/2251799813685248)), (999117/281474976710656), by norm_num⟩
  | 3 => ⟨((218697215181429/281474976710656), (39727465896961/562949953421312)), (14744635/2251799813685248), by norm_num⟩
  | 4 => ⟨((337038159454037/562949953421312), (246935944627483/2251799813685248)), (6248325/562949953421312), by norm_num⟩
  | 5 => ⟨((390029824904119/1125899906842624), (295681119696279/2251799813685248)), (70817181/4503599627370496), by norm_num⟩
  | 6 => ⟨((231399669520951/2251799813685248), (819429539991699/9007199254740992)), (135324517/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1240657665/33554432)), (1/16777216), by norm_num⟩, -6, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-1292011817/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((788517641218283/9007199254740992), (-821433972360915/9007199254740992)), (65532283/4503599627370496), by norm_num⟩
  | 1 => ⟨((-901595461/4294967296), (939232177/4294967296)), (19/536870912), by norm_num⟩
  | 2 => ⟨((540482873/2147483648), (-563045099/2147483648)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-864014217/4294967296), (900082121/4294967296)), (151/4294967296), by norm_num⟩
  | 4 => ⟨((1035907803/8589934592), (-269787833/2147483648)), (23/1073741824), by norm_num⟩
  | 5 => ⟨((-496799685/8589934592), (1035076751/17179869184)), (179/17179869184), by norm_num⟩
  | 6 => ⟨((794182411/34359738368), (-51708451/2147483648)), (145/34359738368), by norm_num⟩
  | 7 => ⟨((-544104643/68719476736), (283409029/34359738368)), (101/68719476736), by norm_num⟩
  | 8 => ⟨((40772061/17179869184), (-679585171/274877906944)), (123/274877906944), by norm_num⟩
  | 9 => ⟨((-695232941/1099511627776), (362127571/549755813888)), (133/1099511627776), by norm_num⟩
  | 10 => ⟨((666838313/4398046511104), (-694675193/4398046511104)), (65/2199023255552), by norm_num⟩
  | 11 => ⟨((-290728807/8796093022208), (605730313/17592186044416)), (115/17592186044416), by norm_num⟩
  | 12 => ⟨((929516309/140737488355328), (-968318569/140737488355328)), (187/140737488355328), by norm_num⟩
  | 13 => ⟨((-685810081/562949953421312), (714438929/562949953421312)), (35/140737488355328), by norm_num⟩
  | 14 => ⟨((939714715/4503599627370496), (-978942703/4503599627370496)), (97/2251799813685248), by norm_num⟩
  | 15 => ⟨((-600889993/18014398509481984), (4890421/140737488355328)), (63/9007199254740992), by norm_num⟩
  | 16 => ⟨((720435637/144115188075855872), (-750509913/144115188075855872)), (153/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-131212210921/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444694544723189/158456325028528675187087900672), (-1242275830567/633825300114114700748351602688)), (92323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889752437590545/39614081257132168796771975168), (-1397307494381/39614081257132168796771975168)), (103871/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889528179590669/2475880078570760549798248448), (-742163003781/1237940039285380274899124224)), (27593/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442798609228801/38685626227668133590597632), (-370993443635/38685626227668133590597632)), (55191/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774778474425697/4835703278458516698824704), (-695425639227/4835703278458516698824704)), (51747/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629395887474649/302231454903657293676544), (-1216620859943/604462909807314587353088)), (90569/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471949270974119/18889465931478580854784), (-61759621867/2361183241434822606848)), (147193/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162192905710911/590295810358705651712), (-1481617820395/4722366482869645213696)), (55207/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621453350055665/590295810358705651712), (-2036228711645/590295810358705651712)), (151847/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911740596597381/36893488147419103232), (-2543793082707/73786976294838206464)), (47463/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227833039797547/1152921504606846976), (-357464504765/1152921504606846976)), (53411/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593912854062731/1152921504606846976), (-1428577102933/576460752303423488)), (26715/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194516915187379/144115188075855872), (-2497130812419/144115188075855872)), (187089/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491541696623759/36028797018963968), (-3739945334411/36028797018963968)), (280803/36028797018963968), by norm_num⟩
  | 3 => ⟨((372284541722913/2251799813685248), (-2332442069823/4503599627370496)), (351301/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227709408309131/4503599627370496), (-9299691664311/4503599627370496)), (703495/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107873311032451/1125899906842624), (-3468644094623/562949953421312)), (1057485/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180022408915689/2251799813685248), (-27450687001425/2251799813685248)), (1061993/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180022408915689/2251799813685248), (-27450687001425/2251799813685248)), (4051181797507857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527549577706589/562949953421312), (-53151361359515/2251799813685248)), (16267/8796093022208), by norm_num⟩
  | 2 => ⟨((1976246652457563/2251799813685248), (-99618014245601/2251799813685248)), (2000389/562949953421312), by norm_num⟩
  | 3 => ⟨((865002976488391/1125899906842624), (-43713869674575/562949953421312)), (1844097/281474976710656), by norm_num⟩
  | 4 => ⟨((1315545965010175/2251799813685248), (-134337438532601/1125899906842624)), (12479793/1125899906842624), by norm_num⟩
  | 5 => ⟨((368255425373343/1125899906842624), (-2452580849679/17592186044416)), (70239809/4503599627370496), by norm_num⟩
  | 6 => ⟨((788517641218283/9007199254740992), (-821433972360915/9007199254740992)), (65532283/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-1292011817/33554432)), (1/16777216), by norm_num⟩, -6, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-334723621/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-312125385588979/4503599627370496), (-852129794655027/9007199254740992)), (95576033/4503599627370496), by norm_num⟩
  | 1 => ⟨((739672133/4294967296), (252421259/1073741824)), (229/4294967296), by norm_num⟩
  | 2 => ⟨((-229752025/1073741824), (-627243265/2147483648)), (9/134217728), by norm_num⟩
  | 3 => ⟨((380608223/2147483648), (1039093973/4294967296)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((-29555497/268435456), (-645512881/4294967296)), (151/4294967296), by norm_num⟩
  | 5 => ⟨((470032967/8589934592), (160403925/2147483648)), (19/1073741824), by norm_num⟩
  | 6 => ⟨((-778658697/34359738368), (-1062903413/34359738368)), (127/17179869184), by norm_num⟩
  | 7 => ⟨((552826907/68719476736), (377316537/34359738368)), (91/34359738368), by norm_num⟩
  | 8 => ⟨((-686861629/274877906944), (-234399093/68719476736)), (229/274877906944), by norm_num⟩
  | 9 => ⟨((758572013/1099511627776), (258871051/274877906944)), (255/1099511627776), by norm_num⟩
  | 10 => ⟨((-11781129/68719476736), (-1029232633/4398046511104)), (1/17179869184), by norm_num⟩
  | 11 => ⟨((340654613/8796093022208), (116252137/2199023255552)), (117/8796093022208), by norm_num⟩
  | 12 => ⟨((-282164971/35184372088832), (-385167611/35184372088832)), (195/70368744177664), by norm_num⟩
  | 13 => ⟨((215739573/140737488355328), (1177976071/562949953421312)), (301/562949953421312), by norm_num⟩
  | 14 => ⟨((-612677371/2251799813685248), (-104541449/281474976710656)), (27/281474976710656), by norm_num⟩
  | 15 => ⟨((811971239/18014398509481984), (554188249/9007199254740992)), (9/562949953421312), by norm_num⟩
  | 16 => ⟨((-504418183/72057594037927936), (-86069129/9007199254740992)), (181/72057594037927936), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-22419709227/79228162514264337593543950336)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778657145990269/633825300114114700748351602688), (-1697891571505/316912650057057350374175801344)), (46267/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889615998979627/39614081257132168796771975168), (-3819529675601/39614081257132168796771975168)), (104123/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472345712611305/618970019642690137449562112), (-2028680887789/1237940039285380274899124224)), (110655/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442762174904045/38685626227668133590597632), (-4056362392773/154742504910672534362390528)), (27671/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((24209685730771/151115727451828646838272), (-3801778125989/9671406556917033397649408)), (103795/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157333926574955/75557863725914323419136), (-103921703067/18889465931478580854784)), (90851/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471900170966351/18889465931478580854784), (-5401939047743/75557863725914323419136)), (18461/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297395236566651/4722366482869645213696), (-2024857002623/2361183241434822606848)), (110815/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621248686569341/590295810358705651712), (-1391382454497/147573952589676412928)), (76225/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823223639757861/73786976294838206464), (-6952673642933/73786976294838206464)), (190681/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822372203952981/9223372036854775808), (-7815932624159/9223372036854775808)), (26835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398404446703089/288230376151711744), (-7808655431489/1152921504606846976)), (214885/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597127708616165/72057594037927936), (-3412196312645/72057594037927936)), (5883/4503599627370496), by norm_num⟩
  | 4 => ⟨((1491142840977301/36028797018963968), (-10220242095879/36028797018963968)), (282845/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488628075897319/9007199254740992), (-796670575165/562949953421312)), (177183/4503599627370496), by norm_num⟩
  | 2 => ⟨((278331854607977/562949953421312), (-1587992024709/281474976710656)), (355583/2251799813685248), by norm_num⟩
  | 1 => ⟨((276759925179999/281474976710656), (-9474578370985/562949953421312)), (67053/140737488355328), by norm_num⟩
  | 0 => ⟨((1088175080293467/1125899906842624), (-74945466557099/2251799813685248)), (33909/35184372088832), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088175080293467/1125899906842624), (-74945466557099/2251799813685248)), (129352569714295853/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2100934181527819/2251799813685248), (-144868631026189/2251799813685248)), (4339381/2251799813685248), by norm_num⟩
  | 2 => ⟨((1950856149893349/2251799813685248), (-33790687887121/281474976710656)), (4327825/1125899906842624), by norm_num⟩
  | 3 => ⟨((1657680144241201/2251799813685248), (-468395251642425/2251799813685248)), (4268979/562949953421312), by norm_num⟩
  | 4 => ⟨((280720929707363/562949953421312), (-344812848631419/1125899906842624)), (16122519/1125899906842624), by norm_num⟩
  | 5 => ⟨((174368129643333/1125899906842624), (-1375556499892471/4503599627370496)), (51909087/2251799813685248), by norm_num⟩
  | 6 => ⟨((-312125385588979/4503599627370496), (-852129794655027/9007199254740992)), (95576033/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-334723621/8388608)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-691011179/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-463586565796899/4503599627370496), (167528108615787/4503599627370496)), (5431015/281474976710656), by norm_num⟩
  | 1 => ⟨((1133991303/4294967296), (-409794917/4294967296)), (215/4294967296), by norm_num⟩
  | 2 => ⟨((-363578783/1073741824), (525551605/4294967296)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((155426861/536870912), (-449337751/4294967296)), (15/268435456), by norm_num⟩
  | 4 => ⟨((-797324055/4294967296), (18008259/268435456)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((818038329/8589934592), (-295617743/8589934592)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((-349704481/8589934592), (63187045/4294967296)), (279/34359738368), by norm_num⟩
  | 7 => ⟨((1025113467/68719476736), (-46306163/8589934592)), (103/34359738368), by norm_num⟩
  | 8 => ⟨((-82167629/17179869184), (118772963/68719476736)), (267/274877906944), by norm_num⟩
  | 9 => ⟨((1498707963/1099511627776), (-270797009/549755813888)), (307/1099511627776), by norm_num⟩
  | 10 => ⟨((-1537644011/4398046511104), (555664491/4398046511104)), (159/2199023255552), by norm_num⟩
  | 11 => ⟨((1434174189/17592186044416), (-518273193/17592186044416)), (299/17592186044416), by norm_num⟩
  | 12 => ⟨((-613097361/35184372088832), (443114831/70368744177664)), (129/35184372088832), by norm_num⟩
  | 13 => ⟨((967731497/281474976710656), (-174856477/140737488355328)), (205/281474976710656), by norm_num⟩
  | 14 => ⟨((-1418389875/2251799813685248), (8008893/35184372088832)), (303/2251799813685248), by norm_num⟩
  | 15 => ⟨((30317485/281474976710656), (-175295189/4503599627370496)), (209/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1244205019/72057594037927936), (224811641/36028797018963968)), (135/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (3640566773823/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778546976475603/633825300114114700748351602688), (4307442746269/633825300114114700748351602688)), (5789/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889491871451865/39614081257132168796771975168), (4844913802777/39614081257132168796771975168)), (52115/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889250717088113/2475880078570760549798248448), (5146556502041/2475880078570760549798248448)), (110775/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442729071917849/38685626227668133590597632), (321577915039/9671406556917033397649408)), (110811/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549295454796677/9671406556917033397649408), (602784652719/1208925819614629174706176)), (103923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258562239102049/604462909807314587353088), (2109050658299/302231454903657293676544)), (90971/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887422723366227/75557863725914323419136), (6851806575673/75557863725914323419136)), (73949/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297261282359345/4722366482869645213696), (160517919087/147573952589676412928)), (110985/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405265928578013/147573952589676412928), (1764770492951/147573952589676412928)), (152705/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455747812090679/18446744073709551616), (8818294520351/73786976294838206464)), (191033/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822109149389959/9223372036854775808), (4956471010317/4611686018427387904)), (13445/576460752303423488), by norm_num⟩
  | 6 => ⟨((199169089840967/144115188075855872), (9903397169983/1152921504606846976)), (53845/288230376151711744), by norm_num⟩
  | 5 => ⟨((298505305832325/36028797018963968), (2163685119207/36028797018963968)), (188751/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490787046153861/36028797018963968), (3240165354741/9007199254740992)), (283713/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488175483423499/9007199254740992), (4040830965223/2251799813685248)), (355669/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112863118419889/2251799813685248), (8053568177691/1125899906842624)), (178607/1125899906842624), by norm_num⟩
  | 1 => ⟨((34572319121103/35184372088832), (12010235237033/562949953421312)), (134923/281474976710656), by norm_num⟩
  | 0 => ⟨((543304661478547/562949953421312), (23740709178403/562949953421312)), (547465/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((543304661478547/562949953421312), (23740709178403/562949953421312)), (2088413240672874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1046687479487307/1125899906842624), (91648913975695/1125899906842624)), (68931/35184372088832), by norm_num⟩
  | 2 => ⟨((965587748675893/1125899906842624), (170401951690325/1125899906842624)), (4460315/1125899906842624), by norm_num⟩
  | 3 => ⟨((1604623767642557/2251799813685248), (146139133596747/562949953421312)), (9000573/1125899906842624), by norm_num⟩
  | 4 => ⟨((247925135287027/562949953421312), (104138176816107/281474976710656)), (17500559/1125899906842624), by norm_num⟩
  | 5 => ⟨((128521785034931/2251799813685248), (11465704641579/35184372088832)), (113456355/4503599627370496), by norm_num⟩
  | 6 => ⟨((-463586565796899/4503599627370496), (167528108615787/4503599627370496)), (5431015/281474976710656), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-691011179/16777216)), (1/16777216), by norm_num⟩, -7, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-355488133/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-31449671291763/9007199254740992), (1848557965622157/18014398509481984)), (301430703/18014398509481984), by norm_num⟩
  | 1 => ⟨((39576285/4294967296), (-145389153/536870912)), (191/4294967296), by norm_num⟩
  | 2 => ⟨((-26111021/2147483648), (1534761239/4294967296)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((11484747/1073741824), (-84381727/268435456)), (225/4294967296), by norm_num⟩
  | 4 => ⟨((-60617811/8589934592), (1781505721/8589934592)), (75/2147483648), by norm_num⟩
  | 5 => ⟨((63989551/17179869184), (-470149573/4294967296)), (319/17179869184), by norm_num⟩
  | 6 => ⟨((-28145349/17179869184), (103395973/2147483648)), (283/34359738368), by norm_num⟩
  | 7 => ⟨((10611027/17179869184), (-311849029/17179869184)), (215/68719476736), by norm_num⟩
  | 8 => ⟨((-56006217/274877906944), (1645974931/274877906944)), (143/137438953472), by norm_num⟩
  | 9 => ⟨((65690497/1099511627776), (-1930587647/1099511627776)), (169/549755813888), by norm_num⟩
  | 10 => ⟨((-69344395/4398046511104), (127373287/274877906944)), (359/4398046511104), by norm_num⟩
  | 11 => ⟨((66546849/17592186044416), (-1955755093/17592186044416)), (347/17592186044416), by norm_num⟩
  | 12 => ⟨((-58540317/70368744177664), (1720449937/70368744177664)), (77/17592186044416), by norm_num⟩
  | 13 => ⟨((23767885/140737488355328), (-1397035697/281474976710656)), (63/70368744177664), by norm_num⟩
  | 14 => ⟨((-35842749/1125899906842624), (1053387799/1125899906842624)), (3/17592186044416), by norm_num⟩
  | 15 => ⟨((25224285/4503599627370496), (-741320211/4503599627370496)), (17/562949953421312), by norm_num⟩
  | 16 => ⟨((-33284167/36028797018963968), (244548317/9007199254740992)), (361/72057594037927936), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (1045221692199/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778455129735545/633825300114114700748351602688), (618277020399/158456325028528675187087900672)), (23111/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889388939184423/39614081257132168796771975168), (1390845802165/19807040628566084398385987584)), (104015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236142733449525/309485009821345068724781056), (2954860767655/2475880078570760549798248448)), (55267/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770808018273999/154742504910672534362390528), (92315269711/4835703278458516698824704)), (55277/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549194568183865/9671406556917033397649408), (1384318967309/4835703278458516698824704)), (103667/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629237289404875/302231454903657293676544), (302717288077/75557863725914323419136)), (45365/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943640714239697/37778931862957161709568), (61465437893/1180591620717411303424)), (36869/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297156319183889/4722366482869645213696), (2948996959295/4722366482869645213696)), (110643/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620921026125379/590295810358705651712), (506585973895/73786976294838206464)), (1189/4611686018427387904), by norm_num⟩
  | 8 => ⟨((455703834811091/18446744073709551616), (5062587067001/73786976294838206464)), (95163/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821914616792761/9223372036854775808), (5690913563523/9223372036854775808)), (53559/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593162384904973/1152921504606846976), (710662126007/144115188075855872)), (107193/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193859394310639/144115188075855872), (4968322513571/144115188075855872)), (46939/36028797018963968), by norm_num⟩
  | 4 => ⟨((745276851223787/18014398509481984), (7439874662189/36028797018963968)), (281971/36028797018963968), by norm_num⟩
  | 3 => ⟨((743950097160681/4503599627370496), (9277812519481/9007199254740992)), (176527/4503599627370496), by norm_num⟩
  | 2 => ⟨((556306148508497/1125899906842624), (4622418242433/1125899906842624)), (176971/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105998736659957/1125899906842624), (27570119767273/2251799813685248)), (1066275/2251799813685248), by norm_num⟩
  | 0 => ⟨((1086218933769045/1125899906842624), (27242808816345/1125899906842624)), (537605/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086218933769045/1125899906842624), (27242808816345/1125899906842624)), (2050800325633811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2094554576796805/2251799813685248), (105130676592197/2251799813685248)), (265833/140737488355328), by norm_num⟩
  | 2 => ⟨((971690820254991/1125899906842624), (24447326365299/281474976710656)), (8309783/2251799813685248), by norm_num⟩
  | 3 => ⟨((830109582765845/1125899906842624), (168791150720003/1125899906842624)), (15786747/2251799813685248), by norm_num⟩
  | 4 => ⟨((586723085083831/1125899906842624), (497789016047351/2251799813685248)), (28012071/2251799813685248), by norm_num⟩
  | 5 => ⟨((1002915093003555/4503599627370496), (1037620859336195/4503599627370496)), (83159719/4503599627370496), by norm_num⟩
  | 6 => ⟨((-31449671291763/9007199254740992), (1848557965622157/18014398509481984)), (301430703/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-355488133/8388608)), (1/16777216), by norm_num⟩, -7, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-729563317/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((191497736024365/2251799813685248), (207709601942581/4503599627370496)), (5146459/562949953421312), by norm_num⟩
  | 1 => ⟨((-989123311/4294967296), (-536430387/4294967296)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((669648895/2147483648), (726340209/4294967296)), (149/4294967296), by norm_num⟩
  | 3 => ⟨((-1208961883/4294967296), (-327827625/2147483648)), (137/4294967296), by norm_num⟩
  | 4 => ⟨((818482367/4294967296), (443886833/4294967296)), (95/4294967296), by norm_num⟩
  | 5 => ⟨((-886596535/8589934592), (-480827131/8589934592)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((800315975/17179869184), (217017335/8589934592)), (97/17179869184), by norm_num⟩
  | 7 => ⟨((-309613691/17179869184), (-167912525/17179869184)), (19/8589934592), by norm_num⟩
  | 8 => ⟨((419224709/68719476736), (454715547/137438953472)), (13/17179869184), by norm_num⟩
  | 9 => ⟨((-504569581/274877906944), (-8551337/8589934592)), (127/549755813888), by norm_num⟩
  | 10 => ⟨((273279951/549755813888), (592830717/2199023255552)), (139/2199023255552), by norm_num⟩
  | 11 => ⟨((-538222419/4398046511104), (-583787397/8796093022208)), (139/8796093022208), by norm_num⟩
  | 12 => ⟨((971688887/35184372088832), (526975193/35184372088832)), (1/274877906944), by norm_num⟩
  | 13 => ⟨((-101207011/17592186044416), (-439100085/140737488355328)), (27/35184372088832), by norm_num⟩
  | 14 => ⟨((1252908189/1125899906842624), (679488613/1125899906842624)), (85/562949953421312), by norm_num⟩
  | 15 => ⟨((-904783539/4503599627370496), (-490690473/4503599627370496)), (125/4503599627370496), by norm_num⟩
  | 16 => ⟨((612549811/18014398509481984), (664407217/36028797018963968)), (171/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (20228533099/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222295799169519/79228162514264337593543950336), (382865639843/316912650057057350374175801344)), (23069/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889289296825165/39614081257132168796771975168), (861273079467/39614081257132168796771975168)), (103815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944518120404541/1237940039285380274899124224), (228721173781/618970019642690137449562112)), (55155/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770702664867873/154742504910672534362390528), (914639604663/154742504910672534362390528)), (27579/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387274022410347/2417851639229258349412352), (857214312323/9671406556917033397649408)), (25857/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629194350072627/302231454903657293676544), (749802309279/604462909807314587353088)), (45253/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471785604763639/18889465931478580854784), (1217941070193/75557863725914323419136)), (147085/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324263134284269/1180591620717411303424), (456514649657/2361183241434822606848)), (110325/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405194774216067/147573952589676412928), (1254722628571/590295810358705651712)), (75857/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911319541374569/36893488147419103232), (1567365015625/73786976294838206464)), (94835/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821717914039363/9223372036854775808), (55058099539/288230376151711744)), (26677/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398241915190349/288230376151711744), (1760077858067/1152921504606846976)), (213463/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193691231616647/144115188075855872), (192258316103/18014398509481984)), (11677/9007199254740992), by norm_num⟩
  | 4 => ⟨((745152943890271/18014398509481984), (2303102581809/36028797018963968)), (280355/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487598149350647/9007199254740992), (358987068357/1125899906842624)), (87657/2251799813685248), by norm_num⟩
  | 2 => ⟨((2224643562313973/4503599627370496), (2861450852691/2251799813685248)), (701815/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211183181092401/2251799813685248), (4266155699299/1125899906842624)), (65883/140737488355328), by norm_num⟩
  | 0 => ⟨((2171035973949389/2251799813685248), (16857578246605/2251799813685248)), (264241/281474976710656), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2171035973949389/2251799813685248), (16857578246605/2251799813685248)), (1007999421239757449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((130815164873733/140737488355328), (32505916897781/2251799813685248)), (2053935/1125899906842624), by norm_num⟩
  | 2 => ⟨((486252243999427/562949953421312), (30214173409285/1125899906842624)), (7755111/2251799813685248), by norm_num⟩
  | 3 => ⟨((839197229843253/1125899906842624), (6524429716871/140737488355328)), (13813297/2251799813685248), by norm_num⟩
  | 4 => ⟨((1246163397994317/2251799813685248), (38904228068085/562949953421312)), (10936205/1125899906842624), by norm_num⟩
  | 5 => ⟨((339441051070547/1125899906842624), (21529900105253/281474976710656)), (54463659/4503599627370496), by norm_num⟩
  | 6 => ⟨((191497736024365/2251799813685248), (207709601942581/4503599627370496)), (5146459/562949953421312), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-729563317/16777216)), (1/16777216), by norm_num⟩, -7, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile004Terms1
