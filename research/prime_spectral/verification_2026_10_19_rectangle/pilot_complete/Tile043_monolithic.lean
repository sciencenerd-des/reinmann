/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.RectangleModel
import XiRectangle.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile043
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

private theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((215/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88064000/1504020649), (-45841920/1504020649)), 0, by norm_num⟩
  | 1 => ⟨((-2826893233356800/2262078112618381201), (4037022842880000/2262078112618381201)), 0, by norm_num⟩
  | 2 => ⟨((165162453/17592186044416), (-78387283/1099511627776)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((228453835/281474976710656), (1255524539/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1040334361/18014398509481984), (-476700839/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1439573519/576460752303423488), (192919909/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((-768405623/9223372036854775808), (170286047/9223372036854775808)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((636827783/295147905179352825856), (-534261383/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-336059581/9444732965739290427392), (811080383/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-80708797/302231454903657293676544), (-461869187/151115727451828646838272)), (41/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((263046815/4835703278458516698824704), (826033871/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-447849639/154742504910672534362390528), (-517298267/309485009821345068724781056)), (11/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((34106183/309485009821345068724781056), (47816151/9903520314283042199192993792)), (1/154742504910672534362390528), by norm_num⟩
  | _ => zero

private theorem V_shiftInv : F_shift c=value ((215/16), (17907/2560)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (17907/2560)))⁻¹=value ((88064000/1504020649), (-45841920/1504020649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using contains_exact ((88064000/1504020649), (-45841920/1504020649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((182397957/67108864), (32209165/67108864)), (1/268435456), by norm_num⟩
  | 1 => ⟨((44032000/1504020649), (-22920960/1504020649)), 0, by norm_num⟩
  | 2 => ⟨((-706723308339200/2262078112618381201), (1009255710720000/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((55054151/35184372088832), (-1672262037/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((228453835/2251799813685248), (1255524539/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-832267489/144115188075855872), (-381360671/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((959715679/4611686018427387904), (257226545/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-878177855/147573952589676412928), (194612625/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((636827783/4722366482869645213696), (-534261383/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-597439255/302231454903657293676544), (1441920681/302231454903657293676544)), (13/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-129134075/9671406556917033397649408), (-738990699/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((382613549/154742504910672534362390528), (300375953/77371252455336267181195264)), (45/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-149283213/1237940039285380274899124224), (-689731023/9903520314283042199192993792)), (59/9903520314283042199192993792), by norm_num⟩
  | _ => zero

private def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (381/40960)), 0, by norm_num⟩
  | 45 => ⟨((362084153177/16322553446400), (-1505331/120586240)), 0, by norm_num⟩
  | 44 => ⟨((-38283647570441/1838572420202496), (55464659959079/4741643894784000)), 0, by norm_num⟩
  | 43 => ⟨((737936811/34359738368), (-377154209/34359738368)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-771388937/34359738368), (191508375/17179869184)), (1/34359738368), by norm_num⟩
  | 41 => ⟨((794136893/34359738368), (-398580361/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-811927041/34359738368), (411017981/34359738368)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((415682103/17179869184), (-420787487/34359738368)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-106673855/4294967296), (430849725/34359738368)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((219239361/8589934592), (-442090917/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-7043851/268435456), (227097087/17179869184)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((463769979/17179869184), (-466911535/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-955006255/34359738368), (480283147/34359738368)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((492091485/17179869184), (-247216241/17179869184)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-1015207591/34359738368), (509454139/34359738368)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((262061501/8589934592), (-32838961/2147483648)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1083501795/34359738368), (542424769/34359738368)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1121209469/34359738368), (-560560867/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-580817375/17179869184), (72493827/4294967296)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((150635205/4294967296), (-150182309/8589934592)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-19560959/536870912), (623051287/34359738368)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((325625543/8589934592), (-323547539/17179869184)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-1357360909/34359738368), (336533815/17179869184)), (1/17179869184), by norm_num⟩
  | 23 => ⟨((1417038033/34359738368), (-350605291/17179869184)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-741098355/17179869184), (365903827/17179869184)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((776813749/17179869184), (-382597103/17179869184)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-816140233/17179869184), (400884785/17179869184)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((859653741/17179869184), (-421006527/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-908059361/17179869184), (443252499/17179869184)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((962229635/17179869184), (-233988713/8589934592)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-511628659/8589934592), (123904895/4294967296)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((546264701/8589934592), (-263363443/8589934592)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-1171833087/17179869184), (280996733/8589934592)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((1263511017/17179869184), (-301155911/8589934592)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-1370694693/17179869184), (20276533/536870912)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((748833041/8589934592), (-175790281/4294967296)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-825218841/8589934592), (383684613/8589934592)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((918860889/8589934592), (-422220821/8589934592)), (3/8589934592), by norm_num⟩
  | 8 => ⟨((-1036315535/8589934592), (29333207/536870912)), (3/8589934592), by norm_num⟩
  | 7 => ⟨((2320161/16777216), (-528225481/8589934592)), (3/8589934592), by norm_num⟩
  | 6 => ⟨((-1390977969/8589934592), (301968825/4294967296)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((419182423/2147483648), (-352417889/4294967296)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-1053940219/4294967296), (422960465/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((1415539915/4294967296), (-528504105/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-535784601/1073741824), (87936585/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((67666399/67108864), (-262402901/1073741824)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-117354321/2147483648), (515346639/1073741824)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (17907/40960)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (17907/40960)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

private theorem logNorm : ‖value ((-41/256), (17907/40960))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
private theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((182397957/67108864), (32209165/67108864)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (17907/2560))) (z:=((-41/256), (17907/40960))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((182397957/67108864), (32209165/67108864))) (r:=(1/268435456)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
private theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((207/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((133404561/4194304), (423141383/16777216)), (3/33554432), by norm_num⟩
  | 1 => ⟨((247542129/134217728), (16615945/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-464897485/8796093022208), (176585041/2199023255552)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((81551573/562949953421312), (-1829202603/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((234779785/18014398509481984), (1099759799/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-674809453/1152921504606846976), (-135158553/288230376151711744)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1316362379/73786976294838206464), (122660017/36893488147419103232)), (119/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1037384801/2361183241434822606848), (164088987/1180591620717411303424)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((640749045/75557863725914323419136), (-327569545/37778931862957161709568)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-222833941/2417851639229258349412352), (1523031897/4835703278458516698824704)), (137/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-285222459/154742504910672534362390528), (-1375271517/154742504910672534362390528)), (361/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((404358911/2475880078570760549798248448), (243358823/1237940039285380274899124224)), (949/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((77043601/4194304), (76446517/4194304)), (1/8388608), by norm_num⟩
  | 1 => ⟨((180433265/134217728), (16615945/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-464897485/8796093022208), (176585041/2199023255552)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((81551573/562949953421312), (-1829202603/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((234779785/18014398509481984), (1099759799/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-674809453/1152921504606846976), (-135158553/288230376151711744)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1316362379/73786976294838206464), (122660017/36893488147419103232)), (119/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1037384801/2361183241434822606848), (164088987/1180591620717411303424)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((640749045/75557863725914323419136), (-327569545/37778931862957161709568)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-222833941/2417851639229258349412352), (1523031897/4835703278458516698824704)), (137/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-285222459/154742504910672534362390528), (-1375271517/154742504910672534362390528)), (361/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((404358911/2475880078570760549798248448), (243358823/1237940039285380274899124224)), (949/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log2 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((986702737/536870912), 0), (1/1073741824), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((986702737/1073741824), 0), (1/2147483648), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647183269/33554432), (76446517/4194304)), (5/33554432), by norm_num⟩
  | 1 => ⟨((180433265/134217728), (16615945/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-464897485/8796093022208), (176585041/2199023255552)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((81551573/562949953421312), (-1829202603/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((234779785/18014398509481984), (1099759799/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-674809453/1152921504606846976), (-135158553/288230376151711744)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1316362379/73786976294838206464), (122660017/36893488147419103232)), (119/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1037384801/2361183241434822606848), (164088987/1180591620717411303424)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((640749045/75557863725914323419136), (-327569545/37778931862957161709568)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-222833941/2417851639229258349412352), (1523031897/4835703278458516698824704)), (137/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-285222459/154742504910672534362390528), (-1375271517/154742504910672534362390528)), (361/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((404358911/2475880078570760549798248448), (243358823/1237940039285380274899124224)), (949/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5653786466713600/2262078112618381201), (-8074045685760000/2262078112618381201)), 0, by norm_num⟩
  | 1 => ⟨((-165162453/4398046511104), (78387283/274877906944)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-342680753/70368744177664), (-235410851/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1040334361/2251799813685248), (476700839/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-899733449/36028797018963968), (-120574943/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((576304217/576460752303423488), (-127714535/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1114448619/36893488147419103232), (934957421/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 7 => ⟨((84014895/147573952589676412928), (-811080383/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((90797397/18889465931478580854784), (519602835/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-657617037/604462909807314587353088), (-516271169/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((615793253/9671406556917033397649408), (711285117/19342813113834066795298816)), (17/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-1637096783/618970019642690137449562112), (-17931057/154742504910672534362390528)), (51/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((424848883/4951760157141521099596496896), (-396052801/9903520314283042199192993792)), (19/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((165162453/4398046511104), (-78387283/274877906944)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((342680753/35184372088832), (235410851/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-780250771/562949953421312), (-357525629/281474976710656)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((899733449/9007199254740992), (120574943/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-720380271/144115188075855872), (159643169/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((52239779/288230376151711744), (-701218065/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-588104265/147573952589676412928), (1419390669/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-90797397/2361183241434822606848), (-519602835/1180591620717411303424)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((739819167/75557863725914323419136), (580805065/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-384870783/604462909807314587353088), (-222276599/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((562752019/19342813113834066795298816), (24655203/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-159318331/154742504910672534362390528), (594079201/1237940039285380274899124224)), (37/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((263762165/9903520314283042199192993792), (-171808943/4951760157141521099596496896)), (29/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-228453835/35184372088832), (-1255524539/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((1040334361/562949953421312), (953401677/562949953421312)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-899733449/4503599627370496), (-120574943/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((240126757/18014398509481984), (-212857559/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((-696530387/1152921504606846976), (146087097/288230376151711744)), (5/1152921504606846976), by norm_num⟩
  | 5 => ⟨((588104265/36893488147419103232), (-1419390669/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 6 => ⟨((105930297/590295810358705651712), (606203307/295147905179352825856)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-246606389/4722366482869645213696), (-774406753/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1154612349/302231454903657293676544), (666829797/302231454903657293676544)), (19/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-1875840063/9671406556917033397649408), (-82184011/9671406556917033397649408)), (1/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((584167213/77371252455336267181195264), (-544572601/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-527524329/2475880078570760549798248448), (171808943/618970019642690137449562112)), (23/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((99411503/39614081257132168796771975168), (-563180161/39614081257132168796771975168)), (9/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1040334361/1125899906842624), (-476700839/562949953421312)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((899733449/4503599627370496), (120574943/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((-720380271/36028797018963968), (159643169/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((696530387/576460752303423488), (-146087097/144115188075855872)), (7/576460752303423488), by norm_num⟩
  | 4 => ⟨((-183782583/4611686018427387904), (13861237/144115188075855872)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-79447723/147573952589676412928), (-1818609921/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((431561181/2361183241434822606848), (677605909/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1154612349/75557863725914323419136), (-166707449/18889465931478580854784)), (9/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((1055160035/1208925819614629174706176), (23114253/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-1460418033/38685626227668133590597632), (680715751/38685626227668133590597632)), (15/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((725345953/618970019642690137449562112), (-472474593/309485009821345068724781056)), (27/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-74558627/4951760157141521099596496896), (844770241/9903520314283042199192993792)), (23/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-363030873/316912650057057350374175801344), (-576089025/158456325028528675187087900672)), (39/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1439573519/18014398509481984), (-192919909/9007199254740992)), (7/18014398509481984), by norm_num⟩
  | 1 => ⟨((576304217/36028797018963968), (-255429071/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((-52239779/36028797018963968), (701218065/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((588104265/9223372036854775808), (-1419390669/9223372036854775808)), (15/9223372036854775808), by norm_num⟩
  | 4 => ⟨((158895445/147573952589676412928), (1818609921/147573952589676412928)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-517873417/1180591620717411303424), (-406563545/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 6 => ⟨((202057161/4722366482869645213696), (466780857/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-211032007/75557863725914323419136), (-73965609/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((1314376229/9671406556917033397649408), (-38290261/604462909807314587353088)), (27/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-22667061/4835703278458516698824704), (472474593/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((164028979/2475880078570760549798248448), (-929247265/2475880078570760549798248448)), (3/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((54454631/9903520314283042199192993792), (345653415/19807040628566084398385987584)), (21/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-766689517/1267650600228229401496703205376), (-767009355/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-768405623/144115188075855872), (170286047/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 1 => ⟨((1114448619/1152921504606846976), (-934957421/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-588104265/9223372036854775808), (1419390669/9223372036854775808)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((-105930297/73786976294838206464), (-606203307/36893488147419103232)), (15/73786976294838206464), by norm_num⟩
  | 4 => ⟨((107890295/147573952589676412928), (677605909/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-202057161/2361183241434822606848), (-466780857/9444732965739290427392)), (15/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1969632065/302231454903657293676544), (43146605/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-876250819/2417851639229258349412352), (408429451/2417851639229258349412352)), (5/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((68001183/4835703278458516698824704), (-708711889/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1067897/4835703278458516698824704), (1548745441/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-399333961/19807040628566084398385987584), (-633697927/9903520314283042199192993792)), (39/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((766689517/316912650057057350374175801344), (383504677/158456325028528675187087900672)), (37/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-819235511/5070602400912917605986812821504), (-8078195/158456325028528675187087900672)), (17/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-636827783/2305843009213693952), (534261383/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 1 => ⟨((84014895/2305843009213693952), (-811080383/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 2 => ⟨((90797397/73786976294838206464), (1039205669/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-246606389/295147905179352825856), (-774406753/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 4 => ⟨((1154612349/9444732965739290427392), (666829797/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-211032007/18889465931478580854784), (-73965609/151115727451828646838272)), (35/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((876250819/1208925819614629174706176), (-408429451/1208925819614629174706176)), (23/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-310862551/9671406556917033397649408), (809956445/19342813113834066795298816)), (27/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((175745335/309485009821345068724781056), (-995622069/309485009821345068724781056)), (15/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((285238543/4951760157141521099596496896), (905282753/4951760157141521099596496896)), (31/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-301199453/39614081257132168796771975168), (-602650207/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((1404403733/2535301200456458802993406410752), (443146697/2535301200456458802993406410752)), (59/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-1212682823/40564819207303340847894502572032), (213538985/40564819207303340847894502572032)), (7/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-336059581/36893488147419103232), (811080383/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-45398699/73786976294838206464), (-519602835/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 2 => ⟨((369909583/590295810358705651712), (1161610129/1180591620717411303424)), (27/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-1154612349/9444732965739290427392), (-166707449/2361183241434822606848)), (29/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((1055160035/75557863725914323419136), (23114253/37778931862957161709568)), (27/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1314376229/1208925819614629174706176), (38290261/75557863725914323419136)), (5/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((68001183/1208925819614629174706176), (-708711889/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-175745335/154742504910672534362390528), (497811035/77371252455336267181195264)), (35/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-320893361/2475880078570760549798248448), (-1018443097/2475880078570760549798248448)), (5/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((752998633/39614081257132168796771975168), (753312759/39614081257132168796771975168)), (11/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-482763783/316912650057057350374175801344), (-304663355/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((1819024235/20282409603651670423947251286016), (-320308477/20282409603651670423947251286016)), (45/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-322484479/81129638414606681695789005144064), (61831603/20282409603651670423947251286016)), (11/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80708797/590295810358705651712), (461869187/295147905179352825856)), (41/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-328808519/1180591620717411303424), (-516271169/1180591620717411303424)), (29/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((384870783/4722366482869645213696), (444553197/9444732965739290427392)), (3/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-937920031/75557863725914323419136), (-41092005/75557863725914323419136)), (55/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((91276127/75557863725914323419136), (-680715751/1208925819614629174706176)), (27/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-22667061/302231454903657293676544), (472474593/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((1067897/604462909807314587353088), (-1548745441/154742504910672534362390528)), (61/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((285238543/1237940039285380274899124224), (905282753/1237940039285380274899124224)), (21/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-752998633/19807040628566084398385987584), (-753312759/19807040628566084398385987584)), (51/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((1072808407/316912650057057350374175801344), (338514839/316912650057057350374175801344)), (59/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-1111625921/5070602400912917605986812821504), (195744069/5070602400912917605986812821504)), (1/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((859958611/81129638414606681695789005144064), (-329768549/40564819207303340847894502572032)), (33/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-105875753/324518553658426726783156020576256), (453800553/649037107316853453566312041152512)), (33/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((263046815/4722366482869645213696), (826033871/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-1231586507/37778931862957161709568), (-177821279/9444732965739290427392)), (23/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((1125504037/151115727451828646838272), (49310405/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-584167213/604462909807314587353088), (544572601/1208925819614629174706176)), (51/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((22667061/302231454903657293676544), (-944949185/9671406556917033397649408)), (53/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-164028979/77371252455336267181195264), (929247265/77371252455336267181195264)), (23/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-399333961/1237940039285380274899124224), (-633697927/618970019642690137449562112)), (17/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((301199453/4951760157141521099596496896), (602650207/9903520314283042199192993792)), (3/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-965527567/158456325028528675187087900672), (-304663355/158456325028528675187087900672)), (31/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((555812961/1267650600228229401496703205376), (-195744069/2535301200456458802993406410752)), (75/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-118244309/5070602400912917605986812821504), (90686351/5070602400912917605986812821504)), (85/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((508203615/649037107316853453566312041152512), (-1089121327/649037107316853453566312041152512)), (23/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((50444933/10384593717069655257060992658440192), (1162487151/10384593717069655257060992658440192)), (3/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22016000/4512061947), (-3820160/1504020649)), 0, by norm_num⟩
  | 1 => ⟨((-706723308339200/6786234337855143603), (336418570240000/2262078112618381201)), 0, by norm_num⟩
  | 2 => ⟨((55054151/70368744177664), (-1672262037/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((304605113/4503599627370496), (837016359/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-693556241/144115188075855872), (-635601119/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((959715679/4611686018427387904), (257226545/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-1024540831/147573952589676412928), (227048063/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((849103711/4722366482869645213696), (-712348511/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-448079441/151115727451828646838272), (1081440511/151115727451828646838272)), (5/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-107611729/4835703278458516698824704), (-1231651165/4835703278458516698824704)), (7/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((701458173/154742504910672534362390528), (1101378495/154742504910672534362390528)), (41/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-149283213/618970019642690137449562112), (-689731023/4951760157141521099596496896)), (59/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1455197141/158456325028528675187087900672), (15938717/39614081257132168796771975168)), (43/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346993/33554432), (611486909/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((360838575/268435456), (33251851/134217728)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((513749687/68719476736), (-277555925/68719476736)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-464302553/8796093022208), (353987481/4398046511104)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((78842369/562949953421312), (-1834168237/1125899906842624)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((477057349/36028797018963968), (1101769381/36028797018963968)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-341406839/576460752303423488), (-538860399/1152921504606846976)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((166203703/9223372036854775808), (234189589/73786976294838206464)), (121/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-522193021/1180591620717411303424), (172537741/1180591620717411303424)), (37/590295810358705651712), by norm_num⟩
  | 9 => ⟨((159766903/18889465931478580854784), (-674383639/75557863725914323419136)), (51/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-211873657/2417851639229258349412352), (1557449975/4835703278458516698824704)), (275/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-161271631/77371252455336267181195264), (-1396825611/154742504910672534362390528)), (725/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((854192733/4951760157141521099596496896), (60964227/309485009821345068724781056)), (953/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-234897711/2251799813685248), (1783746173/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-243684091/9007199254740992), (-1339226175/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109689985/288230376151711744), (1016961789/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 3 => ⟨((-1279620905/4611686018427387904), (-342968727/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((512270415/36893488147419103232), (-227048063/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-594372597/1180591620717411303424), (498643957/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((418207477/37778931862957161709568), (-252336119/9444732965739290427392)), (5/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((32283519/302231454903657293676544), (1477981397/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-263046815/9671406556917033397649408), (-413016935/9671406556917033397649408)), (7/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1094743561/618970019642690137449562112), (632253437/618970019642690137449562112)), (11/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-800358427/9903520314283042199192993792), (-70130355/19807040628566084398385987584)), (35/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((906344283/316912650057057350374175801344), (-422456321/316912650057057350374175801344)), (27/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-750256825/10141204801825835211973625643008), (977401987/10141204801825835211973625643008)), (21/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (7/33554432), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1027499903/137438953472), (-555111365/137438953472)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-232152497/4398046511104), (176993577/2199023255552)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((157700371/1125899906842624), (-1834171701/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | 5 => ⟨((238519605/18014398509481984), (550892299/18014398509481984)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-682800915/1152921504606846976), (-269445601/576460752303423488)), (49/1152921504606846976), by norm_num⟩
  | 7 => ⟨((664818753/36893488147419103232), (117139899/36893488147419103232)), (61/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-522225131/1180591620717411303424), (43121831/295147905179352825856)), (149/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((19975039/2361183241434822606848), (-168576615/18889465931478580854784)), (205/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-212069057/2417851639229258349412352), (1557432853/4835703278458516698824704)), (551/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-322100711/154742504910672534362390528), (-1397031889/154742504910672534362390528)), (363/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((853826397/4951760157141521099596496896), (975904879/4951760157141521099596496896)), (477/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-211369521/288230376151711744), (-387414015/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((365605973/2305843009213693952), (391964259/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-585451903/36893488147419103232), (64870875/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((141517285/147573952589676412928), (-949798015/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-298719627/9444732965739290427392), (1441920679/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-129134077/302231454903657293676544), (-369495349/75557863725914323419136)), (7/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((350729087/2417851639229258349412352), (1101378493/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-938351623/77371252455336267181195264), (-541931517/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((1715053771/2475880078570760549798248448), (75139667/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-1186879417/39614081257132168796771975168), (276608305/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((589487505/633825300114114700748351602688), (-47997419/39614081257132168796771975168)), (23/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-242374711/20282409603651670423947251286016), (343271717/5070602400912917605986812821504)), (19/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-147517307/162259276829213363391578010288128), (-117046659/40564819207303340847894502572032)), (33/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (1/4194304), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-1834171615/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((477039195/36028797018963968), (550892211/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-170700187/288230376151711744), (-538890939/1152921504606846976)), (25/576460752303423488), by norm_num⟩
  | 7 => ⟨((1329636611/73786976294838206464), (234279281/73786976294838206464)), (123/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-522224313/1180591620717411303424), (2695115/18446744073709551616)), (75/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((79899873/9444732965739290427392), (-674305405/75557863725914323419136)), (103/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-424133617/4835703278458516698824704), (778713497/2417851639229258349412352)), (69/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-10065705/4835703278458516698824704), (-1397021413/154742504910672534362390528)), (727/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((853821895/4951760157141521099596496896), (975890591/4951760157141521099596496896)), (955/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((936723045/295147905179352825856), (-12974175/18446744073709551616)), (1/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-84910371/147573952589676412928), (569878809/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((5600993/147573952589676412928), (-108144051/1180591620717411303424)), (5/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((32283519/37778931862957161709568), (369495349/37778931862957161709568)), (19/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-526093629/1208925819614629174706176), (-413016935/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((246317301/4835703278458516698824704), (142257023/4835703278458516698824704)), (19/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-150067205/38685626227668133590597632), (-26298883/154742504910672534362390528)), (23/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((1068191475/4951760157141521099596496896), (-248947475/2475880078570760549798248448)), (25/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-331586721/39614081257132168796771975168), (863953541/79228162514264337593543950336)), (13/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((83316307/633825300114114700748351602688), (-943997221/1267650600228229401496703205376)), (13/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((243403557/20282409603651670423947251286016), (772507949/20282409603651670423947251286016)), (49/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-467315515/324518553658426726783156020576256), (-935020927/649037107316853453566312041152512)), (23/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((998687099/10384593717069655257060992658440192), (78781635/2596148429267413814265248164610048)), (21/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (9/33554432), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-57317863/35184372088832)), (23/1125899906842624), by norm_num⟩
  | 5 => ⟨((477039197/36028797018963968), (1101784423/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-42675047/72057594037927936), (-538890939/1152921504606846976)), (51/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1329636627/73786976294838206464), (117139637/36893488147419103232)), (31/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-522224323/1180591620717411303424), (172487373/1180591620717411303424)), (151/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((319599497/37778931862957161709568), (-674305461/75557863725914323419136)), (207/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-424133559/4835703278458516698824704), (778713589/2417851639229258349412352)), (553/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-322102783/154742504910672534362390528), (-349255409/38685626227668133590597632)), (91/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((853822371/4951760157141521099596496896), (975890741/4951760157141521099596496896)), (239/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-579335035/75557863725914323419136), (1398226115/75557863725914323419136)), (25/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((-78263077/151115727451828646838272), (-1791492603/302231454903657293676544)), (1/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((637689247/1208925819614629174706176), (1001253175/1208925819614629174706176)), (3/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-995221419/9671406556917033397649408), (-574775851/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((227374553/19342813113834066795298816), (39846793/77371252455336267181195264)), (47/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-70808147/77371252455336267181195264), (528070401/1237940039285380274899124224)), (35/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((234455257/4951760157141521099596496896), (-610876241/9903520314283042199192993792)), (3/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-302968389/316912650057057350374175801344), (1716358585/316912650057057350374175801344)), (61/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-276594951/2535301200456458802993406410752), (-438924971/1267650600228229401496703205376)), (35/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((649049327/40564819207303340847894502572032), (649320089/40564819207303340847894502572032)), (39/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-832239249/649037107316853453566312041152512), (-262605451/649037107316853453566312041152512)), (41/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((1567913145/20769187434139310514121985316880384), (-34511351/2596148429267413814265248164610048)), (79/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-555932839/166153499473114484112975882535043072), (852734835/332306998946228968225951765070086144)), (77/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (5/16777216), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-57317863/35184372088832)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((477039197/36028797018963968), (1101784423/36028797018963968)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-42675047/72057594037927936), (-538890939/1152921504606846976)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((1329636627/73786976294838206464), (117139637/36893488147419103232)), (125/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-522224323/1180591620717411303424), (344974745/2361183241434822606848)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((639198995/75557863725914323419136), (-168576365/18889465931478580854784)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-424133565/4835703278458516698824704), (194678397/604462909807314587353088)), (277/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-322102771/154742504910672534362390528), (-698510819/77371252455336267181195264)), (729/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((426911177/2475880078570760549798248448), (487945377/2475880078570760549798248448)), (957/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-516504933/4835703278458516698824704), (-810978397/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((1209139343/19342813113834066795298816), (349160539/9671406556917033397649408)), (23/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-1104990355/77371252455336267181195264), (-48411663/77371252455336267181195264)), (21/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((286760027/154742504910672534362390528), (-267323551/309485009821345068724781056)), (51/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-356062819/2475880078570760549798248448), (927726335/4951760157141521099596496896)), (53/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((161039351/39614081257132168796771975168), (-1824621203/79228162514264337593543950336)), (91/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((392055613/633825300114114700748351602688), (1244296021/633825300114114700748351602688)), (17/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((-147854863/1267650600228229401496703205376), (-591666173/5070602400912917605986812821504)), (3/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((947929651/81129638414606681695789005144064), (149555247/40564819207303340847894502572032)), (31/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((-1091365185/1298074214633706907132624082305024), (192176395/1298074214633706907132624082305024)), (75/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((928713299/20769187434139310514121985316880384), (-356133927/10384593717069655257060992658440192)), (85/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-498940985/332306998946228968225951765070086144), (267317691/83076749736557242056487941267521536)), (91/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-49525513/5316911983139663491615228241121378304), (-1141299407/5316911983139663491615228241121378304)), (3/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (11/33554432), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-57317863/35184372088832)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((477039197/36028797018963968), (1101784423/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 6 => ⟨((-42675047/72057594037927936), (-538890939/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1329636627/73786976294838206464), (117139637/36893488147419103232)), (63/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-522224323/1180591620717411303424), (344974745/2361183241434822606848)), (153/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((639198995/75557863725914323419136), (-168576365/18889465931478580854784)), (209/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-424133565/4835703278458516698824704), (194678397/604462909807314587353088)), (555/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-322102771/154742504910672534362390528), (-698510819/77371252455336267181195264)), (365/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((426911177/2475880078570760549798248448), (975890753/4951760157141521099596496896)), (479/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((406419065841029/2097152), (-293735240415873/2097152)), (17167313/131072), by norm_num⟩
  | 1 => ⟨((1180823607/4), -140265824), (847/4), by norm_num⟩
  | 2 => ⟨(216670308, (-119073083/2)), (689/4), by norm_num⟩
  | 3 => ⟨((824768841/8), (-164077649/16)), 94, by norm_num⟩
  | 4 => ⟨((1150962937/32), (9208441/4)), (1239/32), by norm_num⟩
  | 5 => ⟨((629969103/64), (283622415/128)), (823/64), by norm_num⟩
  | 6 => ⟨((1128529543/512), (27659481/32)), (1837/512), by norm_num⟩
  | 7 => ⟨((850677885/2048), (244188213/1024)), (443/512), by norm_num⟩
  | 8 => ⟨((1100106731/16384), (860946379/16384)), (377/2048), by norm_num⟩
  | 9 => ⟨((617791531/65536), (639482017/65536)), (575/16384), by norm_num⟩
  | 10 => ⟨((606414007/524288), (412760111/262144)), (1591/262144), by norm_num⟩
  | 11 => ⟨((129921407/1048576), (945069279/4194304)), (2017/2097152), by norm_num⟩
  | 12 => ⟨((383812983/33554432), (60847775/2097152)), (2363/16777216), by norm_num⟩
  | _ => zero

private def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((402276582247203/2535301200456458802993406410752), (-815207091239/10141204801825835211973625643008)), (427031/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((906144124378871/316912650057057350374175801344), (-249693968923/158456325028528675187087900672)), (523711/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((240936179543215/4951760157141521099596496896), (-1126410484629/39614081257132168796771975168)), (295349/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1929659780627453/2475880078570760549798248448), (-1199221207709/2475880078570760549798248448)), (314461/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1811366498883745/154742504910672534362390528), (-1201919403745/154742504910672534362390528)), (39399/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((396815332666123/2417851639229258349412352), (-1129674430767/9671406556917033397649408)), (296271/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((645913140189023/302231454903657293676544), (-1936230071/1180591620717411303424)), (520037/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1941559309646579/75557863725914323419136), (-404093210813/18889465931478580854784)), (848003/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((668968066993329/2361183241434822606848), (-1217051140651/4722366482869645213696)), (638589/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1677109695428271/590295810358705651712), (-420309536541/147573952589676412928)), (882283/590295810358705651712), by norm_num⟩
  | 8 => ⟨((946613250892881/36893488147419103232), (-1056652897403/36893488147419103232)), (277307/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1901369374661673/9223372036854775808), (-2393749089391/9223372036854775808)), (628355/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1672921593045995/1152921504606846976), (-2414269501203/1152921504606846976)), (9905/9007199254740992), by norm_num⟩
  | 5 => ⟨((1263993562108227/144115188075855872), (-1067903821669/72057594037927936)), (1122015/144115188075855872), by norm_num⟩
  | 4 => ⟨((1596450609950891/36028797018963968), (-1625476308709/18014398509481984)), (1708665/36028797018963968), by norm_num⟩
  | 3 => ⟨((1621502215341893/9007199254740992), (-4147725442097/9007199254740992)), (68171/281474976710656), by norm_num⟩
  | 2 => ⟨((624043985429033/1125899906842624), (-4276549126173/2251799813685248)), (70359/70368744177664), by norm_num⟩
  | 1 => ⟨((656996791281601/562949953421312), (-6746795984191/1125899906842624)), (889459/281474976710656), by norm_num⟩
  | 0 => ⟨((190241247829135/140737488355328), (-7441346653175/562949953421312)), (1968119/281474976710656), by norm_num⟩
  | _ => zero

private def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((190241247829135/140737488355328), (-7441346653175/562949953421312)), (7507778168798351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((514266269008851/281474976710656), (-20117611723395/562949953421312)), (5372823/281474976710656), by norm_num⟩
  | 2 => ⟨((1878451995657717/562949953421312), (-574307774801/4398046511104)), (20016741/281474976710656), by norm_num⟩
  | 3 => ⟨((1564605322976733/140737488355328), (-61323225150811/70368744177664)), (8675715/17592186044416), by norm_num⟩
  | 4 => ⟨((1080445806118897/8796093022208), (-170435478162751/8796093022208)), (52005035/4398046511104), by norm_num⟩
  | 5 => ⟨((252756679529253/17179869184), (-81777383795695/17179869184)), (231111585/68719476736), by norm_num⟩
  | 6 => ⟨((406419065841029/2097152), (-293735240415873/2097152)), (17167313/131072), by norm_num⟩
  | _ => zero

private def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((647346989/33554432), (76435867/4194304)), (11/33554432), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9420800/334203049), (-45841920/334203049)), 0, by norm_num⟩
  | 1 => ⟨((1006365078323200/111691677960896401), (431867559936000/111691677960896401)), 0, by norm_num⟩
  | 2 => ⟨((-862414355/2199023255552), (1239056889/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-145648323/4398046511104), (-612892517/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((25122949/8796093022208), (-501090755/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((184286259/2251799813685248), (995193093/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-293796303/18014398509481984), (180023655/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((67469279/1152921504606846976), (-1330178489/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((1444446937/18446744073709551616), (374006565/18446744073709551616)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-368075933/147573952589676412928), (750355571/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-740392295/2361183241434822606848), (-286559411/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((795874365/37778931862957161709568), (-683219777/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((285124067/302231454903657293676544), (1027420569/604462909807314587353088)), (15/302231454903657293676544), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse0 : F_base c=value ((23/16), (17907/2560)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (17907/2560)))⁻¹=value ((9420800/334203049), (-45841920/334203049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using contains_exact ((9420800/334203049), (-45841920/334203049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5324800/119866083), (-15280640/119866083)), 0, by norm_num⟩
  | 1 => ⟨((34190743961600/4789292617920963), (81366351872000/14367877853762889)), 0, by norm_num⟩
  | 2 => ⟨((-4462767/8589934592), (181011429/549755813888)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-332402049/35184372088832), (-1422457175/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((1568819459/562949953421312), (166518091/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-363677617/4503599627370496), (770389397/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-656434729/72057594037927936), (-644679193/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((445380177/576460752303423488), (-440355093/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((132533699/18446744073709551616), (1064934513/18446744073709551616)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-566585507/147573952589676412928), (-243295749/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((325417283/2361183241434822606848), (-267299585/1180591620717411303424)), (13/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((859123495/75557863725914323419136), (1043727175/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-1369760619/1208925819614629174706176), (126312935/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (17907/2560)))⁻¹=value ((5324800/119866083), (-15280640/119866083)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using contains_exact ((5324800/119866083), (-15280640/119866083))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-650330000588800/40059610410287067), (-388054908928000/40059610410287067)), 0, by norm_num⟩
  | 1 => ⟨((1028708471/549755813888), (-493809669/274877906944)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((280053997/2199023255552), (1030022345/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-1665569069/70368744177664), (393344281/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((39049277/562949953421312), (-73043725/35184372088832)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((1464500269/9007199254740992), (14050231/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-518750483/72057594037927936), (824702847/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((-823291073/1152921504606846976), (-222455849/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((1311913237/18446744073709551616), (-345463973/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 9 => ⟨((99254787/73786976294838206464), (1744006889/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-1065809577/2361183241434822606848), (-9629913/590295810358705651712)), (19/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((366312617/37778931862957161709568), (-1205083363/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1255128443/604462909807314587353088), (387397349/302231454903657293676544)), (41/604462909807314587353088), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22528000/398100649), (-45841920/398100649)), 0, by norm_num⟩
  | 1 => ⟨((796985422643200/158484126734221201), (1032726773760000/158484126734221201)), 0, by norm_num⟩
  | 2 => ⟨((-1137921165/2199023255552), (57814197/549755813888)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((302111195/35184372088832), (-576479783/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((462676153/281474976710656), (800264565/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1156129759/9007199254740992), (7658731/140737488355328)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((71850603/144115188075855872), (-643470491/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((144127359/288230376151711744), (648800269/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1119665779/36893488147419103232), (768457455/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-201029253/590295810358705651712), (-172417299/73786976294838206464)), (13/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1361671877/9444732965739290427392), (6863267/147573952589676412928)), (37/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-1021083803/151115727451828646838272), (263884271/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-255059827/1208925819614629174706176), (-1418487141/2417851639229258349412352)), (73/2417851639229258349412352), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (17907/2560)))⁻¹=value ((22528000/398100649), (-45841920/398100649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using contains_exact ((22528000/398100649), (-45841920/398100649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1118274987/549755813888), (726340775/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-262765717/2199023255552), (-1037129669/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((569202369/8796093022208), (5555561/1099511627776)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-396542581/140737488355328), (932339501/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-604417877/1125899906842624), (-534953127/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((1035725745/18014398509481984), (-601012617/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((86804773/72057594037927936), (1651823099/288230376151711744)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-568770995/1152921504606846976), (-62534085/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((309773325/18446744073709551616), (-1371633731/36893488147419103232)), (19/36893488147419103232), by norm_num⟩
  | 9 => ⟨((714837767/295147905179352825856), (648816721/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1050808891/4722366482869645213696), (605891789/4722366482869645213696)), (3/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-19907505/4722366482869645213696), (-1463062679/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((906239419/604462909807314587353088), (167547043/1208925819614629174706176)), (7/151115727451828646838272), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((71/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((29081600/449710249), (-45841920/449710249)), 0, by norm_num⟩
  | 1 => ⟨((627871085363200/202239308055642001), (1333156380672000/202239308055642001)), 0, by norm_num⟩
  | 2 => ⟨((-959576117/2199023255552), (-60371013/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((594890691/35184372088832), (-180015645/8796093022208)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((34930665/70368744177664), (107205703/70368744177664)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1687943353/18014398509481984), (-431616473/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((306304877/72057594037927936), (-288303265/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((306582423/4611686018427387904), (797879931/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1459937433/73786976294838206464), (-287766829/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 9 => ⟨((612313235/590295810358705651712), (-892821909/1180591620717411303424)), (19/590295810358705651712), by norm_num⟩
  | 10 => ⟨((94542179/18889465931478580854784), (1460565659/18889465931478580854784)), (13/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-1239990809/302231454903657293676544), (-169627405/75557863725914323419136)), (35/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1194815561/4835703278458516698824704), (-660183559/4835703278458516698824704)), (47/2417851639229258349412352), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (17907/2560)))⁻¹=value ((29081600/449710249), (-45841920/449710249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using contains_exact ((29081600/449710249), (-45841920/449710249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13797859/4398046511104), (643854789/2199023255552)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-623012251/8796093022208), (-485997175/17592186044416)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((590951063/70368744177664), (-632361975/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((382566551/562949953421312), (403693833/281474976710656)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((-401318697/2251799813685248), (110432763/9007199254740992)), (11/9007199254740992), by norm_num⟩
  | 5 => ⟨((393057521/72057594037927936), (-1260887475/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 6 => ⟨((12408125/9007199254740992), (314635351/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-634619385/4611686018427387904), (753529633/9223372036854775808)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-178445645/73786976294838206464), (-508075791/36893488147419103232)), (17/73786976294838206464), by norm_num⟩
  | 9 => ⟨((685220225/590295810358705651712), (64132713/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-235736003/4722366482869645213696), (392514931/4722366482869645213696)), (23/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-367874959/75557863725914323419136), (-457448007/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1395298249/2417851639229258349412352), (-59316621/302231454903657293676544)), (55/2417851639229258349412352), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11878400/171475683), (-15280640/171475683)), 0, by norm_num⟩
  | 1 => ⟨((15400262041600/9801303286772163), (181509554176000/29403909860316489)), 0, by norm_num⟩
  | 2 => ⟨((-724503797/2199023255552), (-79053269/549755813888)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((313464483/17592186044416), (-682524885/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-208281847/1125899906842624), (318028245/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-791465943/18014398509481984), (-426727485/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((1047037659/288230376151711744), (-45637413/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 7 => ⟨((-32198135/288230376151711744), (797015839/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-141349835/36893488147419103232), (-202237453/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 9 => ⟨((366682677/590295810358705651712), (246761405/1180591620717411303424)), (37/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-582327663/18889465931478580854784), (772136191/37778931862957161709568)), (3/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((94964213/604462909807314587353088), (-1258180557/604462909807314587353088)), (61/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((52770693/604462909807314587353088), (382474893/4835703278458516698824704)), (39/4835703278458516698824704), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (17907/2560)))⁻¹=value ((11878400/171475683), (-15280640/171475683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using contains_exact ((11878400/171475683), (-15280640/171475683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((925655353/35184372088832), (703777425/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1290655017/140737488355328), (343218277/70368744177664)), (3/70368744177664), by norm_num⟩
  | 2 => ⟨((-16712701/140737488355328), (-1096855679/562949953421312)), (7/562949953421312), by norm_num⟩
  | 3 => ⟨((1197093233/4503599627370496), (454795477/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((-449623297/18014398509481984), (451743339/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-413411785/288230376151711744), (-530180549/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 6 => ⟨((1873721107/4611686018427387904), (75498233/4611686018427387904)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-629187309/36893488147419103232), (163522797/4611686018427387904)), (25/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-703615117/295147905179352825856), (-804708609/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1434772863/4722366482869645213696), (-118268129/1180591620717411303424)), (37/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-39871887/18889465931478580854784), (514042389/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-1218711771/604462909807314587353088), (-154458329/151115727451828646838272)), (51/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((666650933/4835703278458516698824704), (-577637493/4835703278458516698824704)), (41/4835703278458516698824704), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((42188800/592251049), (-45841920/592251049)), 0, by norm_num⟩
  | 1 => ⟨((160793391923200/350761305041600401), (1934015594496000/350761305041600401)), 0, by norm_num⟩
  | 2 => ⟨((-505155265/2199023255552), (-785686277/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((531133927/35184372088832), (-177862591/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-495225711/1125899906842624), (189785083/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-23482393/2251799813685248), (-1478543727/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((564830655/288230376151711744), (609935101/576460752303423488)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1021454011/9223372036854775808), (175961957/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((364184089/147573952589676412928), (-416530529/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 9 => ⟨((616620367/4722366482869645213696), (350126821/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1218623979/75557863725914323419136), (-104072961/18889465931478580854784)), (53/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((476121745/604462909807314587353088), (-517364515/1208925819614629174706176)), (1/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-222297993/19342813113834066795298816), (884485159/19342813113834066795298816)), (77/19342813113834066795298816), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (17907/2560)))⁻¹=value ((42188800/592251049), (-45841920/592251049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using contains_exact ((42188800/592251049), (-45841920/592251049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((963304965/281474976710656), (-86060083/140737488355328)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-210526987/562949953421312), (682017275/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((-217116967/1125899906842624), (-421596089/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 3 => ⟨((368084473/9007199254740992), (-510719379/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-214402007/288230376151711744), (209135849/36028797018963968)), (21/288230376151711744), by norm_num⟩
  | 5 => ⟨((-674554547/1152921504606846976), (-445695009/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((1217668439/18446744073709551616), (-180580295/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | 7 => ⟨((51213261/73786976294838206464), (575188249/73786976294838206464)), (25/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-417494523/590295810358705651712), (-153759789/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((928617961/18889465931478580854784), (-920814529/18889465931478580854784)), (41/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((316080247/151115727451828646838272), (867516985/151115727451828646838272)), (9/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-313964887/604462909807314587353088), (-48685803/1208925819614629174706176)), (15/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((199550849/9671406556917033397649408), (-732077475/19342813113834066795298816)), (3/1208925819614629174706176), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((119/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((48742400/683182249), (-45841920/683182249)), 0, by norm_num⟩
  | 1 => ⟨((-137169964236800/466737985348698001), (2234445201408000/466737985348698001)), 0, by norm_num⟩
  | 2 => ⟨((-165073521/1099511627776), (-794463453/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1606693933/140737488355328), (198012331/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-255836225/562949953421312), (749461375/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((181779173/36028797018963968), (-977105495/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((420760801/576460752303423488), (655281349/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1183830441/18446744073709551616), (-296295817/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((834746583/295147905179352825856), (-116592289/73786976294838206464)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-452196627/9444732965739290427392), (178571203/1180591620717411303424)), (25/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-127190733/37778931862957161709568), (-1058124373/151115727451828646838272)), (57/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((858392083/2417851639229258349412352), (165419121/1208925819614629174706176)), (1/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-1335078025/77371252455336267181195264), (543913225/77371252455336267181195264)), (71/38685626227668133590597632), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (17907/2560)))⁻¹=value ((48742400/683182249), (-45841920/683182249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using contains_exact ((48742400/683182249), (-45841920/683182249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((457429649/2251799813685248), (-1230694719/4503599627370496)), (7/2251799813685248), by norm_num⟩
  | 1 => ⟨((254602065/4503599627370496), (576882555/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨((-587909985/18014398509481984), (-27841977/9007199254740992)), (15/36028797018963968), by norm_num⟩
  | 3 => ⟨((232915093/72057594037927936), (-682835289/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((438207181/1152921504606846976), (854919439/1152921504606846976)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-489392877/4611686018427387904), (-37299615/18446744073709551616)), (19/9223372036854775808), by norm_num⟩
  | 6 => ⟨((437966895/73786976294838206464), (-197587553/18446744073709551616)), (11/36893488147419103232), by norm_num⟩
  | 7 => ⟨((850274967/1180591620717411303424), (1287826113/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-19218351/147573952589676412928), (133393507/9444732965739290427392)), (21/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((83269223/18889465931478580854784), (-880225745/75557863725914323419136)), (39/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((928495145/1208925819614629174706176), (1006681121/1208925819614629174706176)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-919711173/9671406556917033397649408), (271206305/9671406556917033397649408)), (59/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((214170081/154742504910672534362390528), (-1280587997/154742504910672534362390528)), (95/154742504910672534362390528), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((135/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6144000/87468961), (-15280640/262406883)), 0, by norm_num⟩
  | 1 => ⟨((-53120332595200/68857372245775689), (31294750720000/7650819138419521)), 0, by norm_num⟩
  | 2 => ⟨((-202315561/2199023255552), (-730604525/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((567737107/70368744177664), (444102991/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-825151/2199023255552), (139707713/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((689284181/72057594037927936), (-1101290171/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((7857135/72057594037927936), (1879931411/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1017073379/36893488147419103232), (-469635701/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((504550251/295147905179352825856), (107992187/1180591620717411303424)), (23/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-592205055/9444732965739290427392), (879516289/18889465931478580854784)), (3/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((255830953/302231454903657293676544), (-1046002707/302231454903657293676544)), (25/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((687062141/9671406556917033397649408), (1413937459/9671406556917033397649408)), (13/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-522391765/77371252455336267181195264), (-14827113/4835703278458516698824704)), (27/38685626227668133590597632), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (17907/2560)))⁻¹=value ((6144000/87468961), (-15280640/262406883)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using contains_exact ((6144000/87468961), (-15280640/262406883))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-59239799/36028797018963968), (-139721185/4503599627370496)), (15/36028797018963968), by norm_num⟩
  | 1 => ⟨((892886257/72057594037927936), (243094563/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 2 => ⟨((-447339283/144115188075855872), (260437639/144115188075855872)), (19/288230376151711744), by norm_num⟩
  | 3 => ⟨((17369891/2305843009213693952), (-1556191617/2305843009213693952)), (31/2305843009213693952), by norm_num⟩
  | 4 => ⟨((102915027/1152921504606846976), (124227501/2305843009213693952)), (11/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-905775953/73786976294838206464), (497658495/73786976294838206464)), (27/73786976294838206464), by norm_num⟩
  | 6 => ⟨((16490719/590295810358705651712), (-1997934689/1180591620717411303424)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((766930779/4722366482869645213696), (448302571/4722366482869645213696)), (17/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-634418869/37778931862957161709568), (188330321/18889465931478580854784)), (67/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-20931563/302231454903657293676544), (-578504403/302231454903657293676544)), (1/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((388314589/2417851639229258349412352), (381902137/4835703278458516698824704)), (57/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-502402195/38685626227668133590597632), (728054703/77371252455336267181195264)), (25/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-250761975/1237940039285380274899124224), (-1696602213/1237940039285380274899124224)), (167/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((151/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((61849600/904366249), (-45841920/904366249)), 0, by norm_num⟩
  | 1 => ⟨((-861945695436800/817878312330330001), (2835304415232000/817878312330330001)), 0, by norm_num⟩
  | 2 => ⟨((-455850879/8796093022208), (-638828183/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((191878933/35184372088832), (64272031/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-39276879/140737488355328), (59848311/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((331691877/36028797018963968), (-271210809/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-285979207/2305843009213693952), (1131565361/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((-604806811/73786976294838206464), (-1470142451/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((927068759/1180591620717411303424), (279542573/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-1467872001/37778931862957161709568), (35027487/9444732965739290427392)), (47/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((93285643/75557863725914323419136), (-335951569/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-271679449/19342813113834066795298816), (1340484951/19342813113834066795298816)), (89/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-394947411/309485009821345068724781056), (-843576511/309485009821345068724781056)), (43/154742504910672534362390528), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (17907/2560)))⁻¹=value ((61849600/904366249), (-45841920/904366249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using contains_exact ((61849600/904366249), (-45841920/904366249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-121421287/72057594037927936), (-293765625/144115188075855872)), (15/288230376151711744), by norm_num⟩
  | 1 => ⟨((1497342477/1152921504606846976), (-80514179/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 2 => ⟨((-372513783/2305843009213693952), (734700439/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-2611795/72057594037927936), (-1134982081/18446744073709551616)), (37/18446744073709551616), by norm_num⟩
  | 4 => ⟨((1716954593/147573952589676412928), (50916571/147573952589676412928)), (55/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-133441571/147573952589676412928), (403342425/295147905179352825856)), (35/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-25851259/295147905179352825856), (-882144377/4722366482869645213696)), (43/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((1786818185/75557863725914323419136), (183453515/75557863725914323419136)), (23/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-7146257/4722366482869645213696), (619399069/302231454903657293676544)), (47/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-61629461/604462909807314587353088), (-1140399139/4835703278458516698824704)), (23/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((118234625/4835703278458516698824704), (106010907/38685626227668133590597632)), (21/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-815007697/618970019642690137449562112), (1131365885/618970019642690137449562112)), (75/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-419038703/4951760157141521099596496896), (-888024307/4951760157141521099596496896)), (129/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((167/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((68403200/1034619049), (-45841920/1034619049)), 0, by norm_num⟩
  | 1 => ⟨((-1288758070476800/1070436576553664401), (3135734022144000/1070436576553664401)), 0, by norm_num⟩
  | 2 => ⟨((-220768789/8796093022208), (-1086406243/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1003720003/281474976710656), (248181003/70368744177664)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-1765535401/9007199254740992), (-21160491/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((1053828435/144115188075855872), (-446745363/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-399030519/2305843009213693952), (1219669501/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-20445213/147573952589676412928), (-1855971195/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((334344515/1180591620717411303424), (974404027/2361183241434822606848)), (21/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-1398141989/75557863725914323419136), (-556701361/75557863725914323419136)), (19/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((936829033/1208925819614629174706176), (-100571737/604462909807314587353088)), (35/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-848409675/38685626227668133590597632), (876920237/38685626227668133590597632)), (63/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((4309371/19342813113834066795298816), (-1529094271/1237940039285380274899124224)), (113/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (17907/2560)))⁻¹=value ((68403200/1034619049), (-45841920/1034619049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using contains_exact ((68403200/1034619049), (-45841920/1034619049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-465144955/2305843009213693952), (-34649039/576460752303423488)), (27/4611686018427387904), by norm_num⟩
  | 1 => ⟨((808675597/9223372036854775808), (-319408727/4611686018427387904)), (29/9223372036854775808), by norm_num⟩
  | 2 => ⟨((76472923/36893488147419103232), (1197405491/36893488147419103232)), (43/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-436087321/73786976294838206464), (-257431097/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 4 => ⟨((624037247/590295810358705651712), (-300043221/590295810358705651712)), (61/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-216460475/9444732965739290427392), (805816885/4722366482869645213696)), (81/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-80706597/4722366482869645213696), (-552252151/37778931862957161709568)), (51/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((1547351815/604462909807314587353088), (-473097939/604462909807314587353088)), (113/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-370060847/4835703278458516698824704), (344702361/1208925819614629174706176)), (59/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-811508491/38685626227668133590597632), (-858634001/38685626227668133590597632)), (59/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((904652677/309485009821345068724781056), (-6123807/9671406556917033397649408)), (55/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-219532095/2475880078570760549798248448), (1311601569/4951760157141521099596496896)), (25/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-81594087/4951760157141521099596496896), (-372917203/19807040628566084398385987584)), (11/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((183/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((24985600/392659683), (-15280640/392659683)), 0, by norm_num⟩
  | 1 => ⟨((-65130374758400/51393875551220163), (381795958784000/154181626653660489)), 0, by norm_num⟩
  | 2 => ⟨((-69167733/8796093022208), (-454948437/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((318484521/140737488355328), (110413129/35184372088832)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1198494113/9007199254740992), (-502689209/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1533195649/288230376151711744), (-117226511/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-353743687/2305843009213693952), (596672619/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((174389323/73786976294838206464), (-1047994867/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((297441835/4722366482869645213696), (321034655/1180591620717411303424)), (23/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-551199399/75557863725914323419136), (-561093965/75557863725914323419136)), (5/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((910546147/2417851639229258349412352), (228048461/2417851639229258349412352)), (17/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-1069028245/77371252455336267181195264), (83693851/19342813113834066795298816)), (57/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((219984181/618970019642690137449562112), (-1006469517/2475880078570760549798248448)), (47/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (17907/2560)))⁻¹=value ((24985600/392659683), (-15280640/392659683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using contains_exact ((24985600/392659683), (-15280640/392659683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1119729015/73786976294838206464), (148517595/36893488147419103232)), (45/73786976294838206464), by norm_num⟩
  | 1 => ⟨((485248445/147573952589676412928), (-608191887/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 2 => ⟨((214085707/147573952589676412928), (682019857/295147905179352825856)), (5/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-1423693319/2361183241434822606848), (-22016415/590295810358705651712)), (39/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((318276303/4722366482869645213696), (-198408655/2361183241434822606848)), (31/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((353073145/75557863725914323419136), (148610815/9444732965739290427392)), (85/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-1276136563/604462909807314587353088), (-407878027/604462909807314587353088)), (109/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1028699689/4835703278458516698824704), (-408697065/2417851639229258349412352)), (31/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((106284641/38685626227668133590597632), (592638221/19342813113834066795298816)), (133/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-445986075/154742504910672534362390528), (-117396771/77371252455336267181195264)), (17/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((699636751/2475880078570760549798248448), (-200360685/1237940039285380274899124224)), (129/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-11642325/9903520314283042199192993792), (1226171115/39614081257132168796771975168)), (239/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-743499883/316912650057057350374175801344), (-495793321/316912650057057350374175801344)), (213/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((199/16), (17907/2560)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((81510400/1334446249), (-45841920/1334446249)), 0, by norm_num⟩
  | 1 => ⟨((-2271231839436800/1780746791470170001), (3736593235968000/1780746791470170001)), 0, by norm_num⟩
  | 2 => ⟨((51216501/17592186044416), (-94549525/1099511627776)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((195360827/140737488355328), (376654141/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-397953691/4503599627370496), (-260728545/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((532231693/144115188075855872), (72158811/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-269992845/2305843009213693952), (257277365/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((772643753/295147905179352825856), (-1096479065/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-152438311/9444732965739290427392), (187034765/1180591620717411303424)), (25/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-336720669/151115727451828646838272), (-386528249/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((47124139/302231454903657293676544), (570438531/4835703278458516698824704)), (1/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-525207913/77371252455336267181195264), (-143070541/154742504910672534362390528)), (25/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((552609399/2475880078570760549798248448), (-218765447/2475880078570760549798248448)), (77/4951760157141521099596496896), by norm_num⟩
  | _ => zero

private theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
private theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (17907/2560)))⁻¹=value ((81510400/1334446249), (-45841920/1334446249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using contains_exact ((81510400/1334446249), (-45841920/1334446249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-58191101/73786976294838206464), (905747805/1180591620717411303424)), (35/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-168584913/2361183241434822606848), (-771403011/1180591620717411303424)), (85/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((856621225/4722366482869645213696), (507469/4611686018427387904)), (17/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-860247247/18889465931478580854784), (171800623/9444732965739290427392)), (35/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((174429577/75557863725914323419136), (-1327662427/151115727451828646838272)), (115/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((68482871/75557863725914323419136), (167520771/151115727451828646838272)), (41/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-1923237011/9671406556917033397649408), (125923983/9671406556917033397649408)), (53/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((504338707/38685626227668133590597632), (-829653135/38685626227668133590597632)), (125/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((368456491/309485009821345068724781056), (410994963/154742504910672534362390528)), (17/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1535787257/4951760157141521099596496896), (-269073437/4951760157141521099596496896)), (141/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((875715495/39614081257132168796771975168), (-230368033/9903520314283042199192993792)), (137/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((113440977/158456325028528675187087900672), (957446103/316912650057057350374175801344)), (129/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-686566695/2535301200456458802993406410752), (-481391049/5070602400912917605986812821504)), (465/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-199572833/4398046511104), (569853151/2199023255552)), (123/549755813888), by norm_num⟩
  | 1 => ⟨((-1013984733/4398046511104), (60603347/274877906944)), (1017/2199023255552), by norm_num⟩
  | 2 => ⟨((-824012573/4398046511104), (28835809/1099511627776)), (273/549755813888), by norm_num⟩
  | 3 => ⟨((-286325595/4398046511104), (-583979537/17592186044416)), (1607/4398046511104), by norm_num⟩
  | 4 => ⟨((-352339115/35184372088832), (-636067433/35184372088832)), (14477/70368744177664), by norm_num⟩
  | 5 => ⟨((84113803/281474976710656), (-1281804263/281474976710656)), (26511/281474976710656), by norm_num⟩
  | 6 => ⟨((264344245/562949953421312), (-757974419/1125899906842624)), (40991/1125899906842624), by norm_num⟩
  | 7 => ⟨((1005550169/9007199254740992), (-488837551/9007199254740992)), (27473/2251799813685248), by norm_num⟩
  | 8 => ⟨((1169115989/72057594037927936), (19757243/72057594037927936)), (260387/72057594037927936), by norm_num⟩
  | 9 => ⟨((30607915/18014398509481984), (116526415/144115188075855872)), (276827/288230376151711744), by norm_num⟩
  | 10 => ⟨((76810837/576460752303423488), (675597649/4611686018427387904)), (534727/2305843009213693952), by norm_num⟩
  | 11 => ⟨((8220875/1152921504606846976), (329327911/18446744073709551616)), (3791715/73786976294838206464), by norm_num⟩
  | 12 => ⟨((11407833/147573952589676412928), (2046788321/1180591620717411303424)), (6221577/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-199572833/4398046511104), (569853151/2199023255552)), (985/4398046511104), by norm_num⟩
  | 1 => ⟨((-1013984733/4398046511104), (60603347/274877906944)), (2035/4398046511104), by norm_num⟩
  | 2 => ⟨((-824012573/4398046511104), (28835809/1099511627776)), (4369/8796093022208), by norm_num⟩
  | 3 => ⟨((-286325595/4398046511104), (-583979537/17592186044416)), (6429/17592186044416), by norm_num⟩
  | 4 => ⟨((-352339115/35184372088832), (-636067433/35184372088832)), (905/4398046511104), by norm_num⟩
  | 5 => ⟨((84113803/281474976710656), (-1281804263/281474976710656)), (26523/281474976710656), by norm_num⟩
  | 6 => ⟨((264344245/562949953421312), (-757974419/1125899906842624)), (41037/1125899906842624), by norm_num⟩
  | 7 => ⟨((1005550169/9007199254740992), (-488837551/9007199254740992)), (110253/9007199254740992), by norm_num⟩
  | 8 => ⟨((1169115989/72057594037927936), (19757243/72057594037927936)), (131635/36028797018963968), by norm_num⟩
  | 9 => ⟨((30607915/18014398509481984), (116526415/144115188075855872)), (576713/576460752303423488), by norm_num⟩
  | 10 => ⟨((76810837/576460752303423488), (675597649/4611686018427387904)), (626961/2305843009213693952), by norm_num⟩
  | 11 => ⟨((8220875/1152921504606846976), (329327911/18446744073709551616)), (6743195/73786976294838206464), by norm_num⟩
  | 12 => ⟨((11407833/147573952589676412928), (2046788321/1180591620717411303424)), (59666819/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

private def J_negLog2 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/16777216), (-650756047/67108864)), (1/67108864), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-73911430673991/140737488355328), (330146656093111/2251799813685248)), (26011263/1125899906842624), by norm_num⟩
  | 1 => ⟨((1563461297/4294967296), (-54559761/536870912)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((-541854395/4294967296), (75635889/2147483648)), (51/8589934592), by norm_num⟩
  | 3 => ⟨((500779795/17179869184), (-279609617/34359738368)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((-347114103/68719476736), (387621235/274877906944)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((384961859/549755813888), (-214942853/1099511627776)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((-355780303/4398046511104), (397298753/17592186044416)), (19/4398046511104), by norm_num⟩
  | 7 => ⟨((563675689/70368744177664), (-314727441/140737488355328)), (31/70368744177664), by norm_num⟩
  | 8 => ⟨((-781420429/1125899906842624), (436304877/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 9 => ⟨((962914431/18014398509481984), (-268820885/18014398509481984)), (7/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1067906277/288230376151711744), (149065951/144115188075855872)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((538339073/2305843009213693952), (-150290391/2305843009213693952)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-995061895/73786976294838206464), (277795629/73786976294838206464)), (1/1152921504606846976), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583185728209367/10141204801825835211973625643008), (1868824278705/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445256140368179/158456325028528675187087900672), (554253765847/79228162514264337593543950336)), (2895/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((946139364265705/19807040628566084398385987584), (4987981758121/39614081257132168796771975168)), (26061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946105640850463/1237940039285380274899124224), (5299398901607/2475880078570760549798248448)), (13849/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886938160947367/77371252455336267181195264), (662378182497/19342813113834066795298816)), (6927/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((388017480761363/2417851639229258349412352), (1241859838169/2417851639229258349412352)), (12993/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630494667325121/302231454903657293676544), (4346112154153/604462909807314587353088)), (22747/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891365695105567/75557863725914323419136), (3530843396043/37778931862957161709568)), (36981/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300217584245415/4722366482869645213696), (5295612258751/4722366482869645213696)), (27753/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625127121837817/590295810358705651712), (3640202475225/295147905179352825856)), (38185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828068244103479/73786976294838206464), (9098911497267/73786976294838206464)), (47769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228477206662783/1152921504606846976), (5117039879187/4611686018427387904)), (26897/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599057321650695/1152921504606846976), (10231330702657/1152921504606846976)), (13465/288230376151711744), by norm_num⟩
  | 5 => ⟨((299752088642025/36028797018963968), (8949315549693/144115188075855872)), (47203/144115188075855872), by norm_num⟩
  | 4 => ⟨((46820591599131/1125899906842624), (419305012297/1125899906842624)), (35477/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497499875942275/9007199254740992), (1047580842811/562949953421312)), (22239/2251799813685248), by norm_num⟩
  | 2 => ⟨((561082114832643/1125899906842624), (16744864342429/2251799813685248)), (44675/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120207377729677/1125899906842624), (12537991999407/562949953421312)), (67507/562949953421312), by norm_num⟩
  | 0 => ⟨((1114159878946169/1125899906842624), (12496321107103/281474976710656)), (273991/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114159878946169/1125899906842624), (12496321107103/281474976710656)), (1045192722800826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1100323127895167/1125899906842624), (49464075899985/562949953421312)), (283299/562949953421312), by norm_num⟩
  | 2 => ⟨((266658740991065/281474976710656), (48340413194761/281474976710656)), (75439/70368744177664), by norm_num⟩
  | 3 => ⟨((977281737833375/1125899906842624), (183183512398029/562949953421312)), (1350783/562949953421312), by norm_num⟩
  | 4 => ⟨((91133189688531/140737488355328), (636013557691113/1125899906842624)), (3224049/562949953421312), by norm_num⟩
  | 5 => ⟨((225638677968943/2251799813685248), (1647377536003821/2251799813685248)), (31271569/2251799813685248), by norm_num⟩
  | 6 => ⟨((-73911430673991/140737488355328), (330146656093111/2251799813685248)), (26011263/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/16777216), (-650756047/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-64510795/67108864), (-257855983/16777216)), (1/33554432), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1624425368806711/4503599627370496), (-285984268167973/2251799813685248)), (74311585/2251799813685248), by norm_num⟩
  | 1 => ⟨((1662051/4194304), (149815479/1073741824)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-934886223/4294967296), (-329178253/4294967296)), (45/2147483648), by norm_num⟩
  | 3 => ⟨((684718329/8589934592), (482185699/17179869184)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((-1504479941/68719476736), (-264867567/34359738368)), (75/34359738368), by norm_num⟩
  | 5 => ⟨((1322272121/274877906944), (232789411/137438953472)), (135/274877906944), by norm_num⟩
  | 6 => ⟨((-484221467/549755813888), (-21312109/68719476736)), (101/1099511627776), by norm_num⟩
  | 7 => ⟨((607967605/4398046511104), (428137049/8796093022208)), (129/8796093022208), by norm_num⟩
  | 8 => ⟨((-333960341/17592186044416), (-470356623/70368744177664)), (9/4398046511104), by norm_num⟩
  | 9 => ⟨((326127053/140737488355328), (459324059/562949953421312)), (143/562949953421312), by norm_num⟩
  | 10 => ⟨((-573259501/2251799813685248), (-403695245/4503599627370496)), (1/35184372088832), by norm_num⟩
  | 11 => ⟨((229014521/9007199254740992), (322548769/36028797018963968)), (13/4503599627370496), by norm_num⟩
  | 12 => ⟨((-1341856891/576460752303423488), (-236237361/288230376151711744)), (155/576460752303423488), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395680896270333/2535301200456458802993406410752), (-456409665353/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780476952518715/633825300114114700748351602688), (-2164518253319/316912650057057350374175801344)), (46313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472915687823985/9903520314283042199192993792), (-1217429976687/9903520314283042199192993792)), (13029/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236444611870525/309485009821345068724781056), (-1293391621365/618970019642690137449562112)), (55389/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27706594304241/2417851639229258349412352), (-5172991482231/154742504910672534362390528)), (55407/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387864159046649/2417851639229258349412352), (-4849068411537/9671406556917033397649408)), (51963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260452815401627/604462909807314587353088), (-4242323574763/604462909807314587353088)), (45487/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945247025839555/37778931862957161709568), (-1723157315493/18889465931478580854784)), (36975/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299564027174783/4722366482869645213696), (-2584234165585/2361183241434822606848)), (27747/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812114383204619/295147905179352825856), (-888126544529/73786976294838206464)), (76355/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913472864378877/36893488147419103232), (-2219704195167/18446744073709551616)), (95519/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28539928349137/144115188075855872), (-2496324977521/2305843009213693952)), (107563/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199724477840017/144115188075855872), (-9981085623347/1152921504606846976)), (26923/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197905377619295/144115188075855872), (-8728704625653/144115188075855872)), (94377/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496606140182699/36028797018963968), (-13083555817525/36028797018963968)), (141859/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495436829143341/9007199254740992), (-16337794180805/9007199254740992)), (88919/4503599627370496), by norm_num⟩
  | 2 => ⟨((140013202382799/281474976710656), (-16312771200835/2251799813685248)), (89305/1125899906842624), by norm_num⟩
  | 1 => ⟨((34910332297435/35184372088832), (-6101608817373/281474976710656)), (269847/1125899906842624), by norm_num⟩
  | 0 => ⟨((277012890507317/281474976710656), (-48561005877561/1125899906842624)), (547443/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277012890507317/281474976710656), (-48561005877561/1125899906842624)), (2088329319480514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1088391681512899/1125899906842624), (-47791191818497/562949953421312)), (562377/562949953421312), by norm_num⟩
  | 2 => ⟨((1044018614071215/1125899906842624), (-92398152462251/562949953421312)), (2365539/1125899906842624), by norm_num⟩
  | 3 => ⟨((468880575349853/562949953421312), (-342713914407895/1125899906842624)), (1290883/281474976710656), by norm_num⟩
  | 4 => ⟨((676741461654067/1125899906842624), (-71361537731451/140737488355328)), (11744871/1125899906842624), by norm_num⟩
  | 5 => ⟨((234587435003163/2251799813685248), (-1372578462629235/2251799813685248)), (13014743/562949953421312), by norm_num⟩
  | 6 => ⟨((-1624425368806711/4503599627370496), (-285984268167973/2251799813685248)), (74311585/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/67108864), (-257855983/16777216)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/8388608), (-650756047/33554432)), (1/33554432), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((286327734643257/1125899906842624), (-693535516918359/4503599627370496)), (64289973/4503599627370496), by norm_num⟩
  | 1 => ⟨((-378546261/1073741824), (114613101/536870912)), (11/536870912), by norm_num⟩
  | 2 => ⟨((524776547/2147483648), (-635549983/4294967296)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((-15156141/134217728), (587372905/8589934592)), (15/2147483648), by norm_num⟩
  | 4 => ⟨((336173965/8589934592), (-407135873/17179869184)), (43/17179869184), by norm_num⟩
  | 5 => ⟨((-745657715/68719476736), (112882033/17179869184)), (49/68719476736), by norm_num⟩
  | 6 => ⟨((689134057/274877906944), (-208650301/137438953472)), (47/274877906944), by norm_num⟩
  | 7 => ⟨((-272955045/549755813888), (661144539/2199023255552)), (19/549755813888), by norm_num⟩
  | 8 => ⟨((756792079/8796093022208), (-458270473/8796093022208)), (55/8796093022208), by norm_num⟩
  | 9 => ⟨((-932565859/70368744177664), (564709131/70368744177664)), (35/35184372088832), by norm_num⟩
  | 10 => ⟨((1034248633/562949953421312), (-626282467/562949953421312)), (5/35184372088832), by norm_num⟩
  | 11 => ⟨((-1042744035/4503599627370496), (315713401/2251799813685248)), (83/4503599627370496), by norm_num⟩
  | 12 => ⟨((963700117/36028797018963968), (-583562277/36028797018963968)), (79/36028797018963968), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689313353/10141204801825835211973625643008), (-354626634533/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780097890213313/633825300114114700748351602688), (-840557925797/633825300114114700748351602688)), (23071/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891236922900747/39614081257132168796771975168), (-945525431017/39614081257132168796771975168)), (6489/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891105214266773/2475880078570760549798248448), (-1004496402757/2475880078570760549798248448)), (6895/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886385605898603/77371252455336267181195264), (-502178257195/77371252455336267181195264)), (13791/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775517449659683/4835703278458516698824704), (-470717813299/4835703278458516698824704)), (51719/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315021176419523/151115727451828646838272), (-823607596595/604462909807314587353088)), (22629/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889897579073829/75557863725914323419136), (-334520956183/18889465931478580854784)), (73551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162389770572945/590295810358705651712), (-1003319225303/4722366482869645213696)), (55169/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202952266057385/73786976294838206464), (-1379168129839/590295810358705651712)), (75867/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826186063951537/73786976294838206464), (-861683328311/36893488147419103232)), (741/576460752303423488), by norm_num⟩
  | 7 => ⟨((228213222874267/1152921504606846976), (-484492936531/2305843009213693952)), (106725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596952425845849/1152921504606846976), (-968476279647/576460752303423488)), (53375/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197174412305697/144115188075855872), (-211710947441/18014398509481984)), (93435/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495523689023015/36028797018963968), (-1269120618455/18014398509481984)), (140209/36028797018963968), by norm_num⟩
  | 3 => ⟨((747054110569611/4503599627370496), (-3168797608217/9007199254740992)), (175361/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118813617990123/2251799813685248), (-6325598563991/4503599627370496)), (351021/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115283879609063/1125899906842624), (-9458459217983/2251799813685248)), (263641/1125899906842624), by norm_num⟩
  | 0 => ⟨((552360712911485/562949953421312), (-9398740725523/1125899906842624)), (528787/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552360712911485/562949953421312), (-9398740725523/1125899906842624)), (2017162327293014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2167725718651621/2251799813685248), (-9221947876661/562949953421312)), (2093019/2251799813685248), by norm_num⟩
  | 2 => ⟨((1043093185635657/1125899906842624), (-35510534225663/1125899906842624)), (4098321/2251799813685248), by norm_num⟩
  | 3 => ⟨((1930513341858655/2251799813685248), (-131595343578791/2251799813685248)), (7852323/2251799813685248), by norm_num⟩
  | 4 => ⟨((823688768001907/1125899906842624), (-225638677968947/2251799813685248)), (14381691/2251799813685248), by norm_num⟩
  | 5 => ⟨((1182582890783845/2251799813685248), (-330146656093115/2251799813685248)), (5981247/562949953421312), by norm_num⟩
  | 6 => ⟨((286327734643257/1125899906842624), (-693535516918359/4503599627370496)), (64289973/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/8388608), (-650756047/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47253303/33554432), (-377752187/16777216)), (1/33554432), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-953303488240529/4503599627370496), (551709640136229/4503599627370496)), (98130337/4503599627370496), by norm_num⟩
  | 1 => ⟨((731603039/2147483648), (-13231373/67108864)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-294367417/1073741824), (681442347/4294967296)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((157922027/1073741824), (-91394929/1073741824)), (69/4294967296), by norm_num⟩
  | 4 => ⟨((-508331395/8589934592), (588377855/17179869184)), (113/17179869184), by norm_num⟩
  | 5 => ⟨((1309004511/68719476736), (-757566101/68719476736)), (37/17179869184), by norm_num⟩
  | 6 => ⟨((-702253829/137438953472), (406418535/137438953472)), (81/137438953472), by norm_num⟩
  | 7 => ⟨((161461991/137438953472), (-747549027/1099511627776)), (151/1099511627776), by norm_num⟩
  | 8 => ⟨((-1039452199/4398046511104), (601566873/4398046511104)), (123/4398046511104), by norm_num⟩
  | 9 => ⟨((743526123/17592186044416), (-430304237/17592186044416)), (45/8796093022208), by norm_num⟩
  | 10 => ⟨((-957327305/140737488355328), (277019181/70368744177664)), (59/70368744177664), by norm_num⟩
  | 11 => ⟨((560275949/562949953421312), (-648502069/1125899906842624)), (35/281474976710656), by norm_num⟩
  | 12 => ⟨((-1202305805/9007199254740992), (347907939/4503599627370496)), (19/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353606259/10141204801825835211973625643008), (3408877777757/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779788182943413/633825300114114700748351602688), (504833278539/79228162514264337593543950336)), (46299/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890888055346305/39614081257132168796771975168), (4542910576307/39614081257132168796771975168)), (52099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945366988176857/1237940039285380274899124224), (4826146324199/2475880078570760549798248448)), (27685/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886199668637727/77371252455336267181195264), (4825363036067/154742504910672534362390528)), (55387/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48458924714599/302231454903657293676544), (4522945577775/9671406556917033397649408)), (51943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259778385041409/604462909807314587353088), (3956745083927/604462909807314587353088)), (45467/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472349635440543/18889465931478580854784), (6428150145821/75557863725914323419136)), (73917/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649371389672299/2361183241434822606848), (4819747011701/4722366482869645213696)), (13867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((50721880495241/18446744073709551616), (1656233233721/147573952589676412928)), (76315/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912767964371699/36893488147419103232), (4138918584115/36893488147419103232)), (11933/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824970679952275/9223372036854775808), (145437330171/144115188075855872)), (53747/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596212702527603/1152921504606846976), (9302266569795/1152921504606846976)), (107615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196521964686023/144115188075855872), (8133044746521/144115188075855872)), (23575/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494534658387877/36028797018963968), (1523336073329/4503599627370496)), (35431/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492853849718111/9007199254740992), (7605409961335/4503599627370496)), (177635/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117532212774323/2251799813685248), (15177002108161/2251799813685248)), (44589/562949953421312), by norm_num⟩
  | 1 => ⟨((556647252561235/562949953421312), (5670234058647/281474976710656)), (269339/1125899906842624), by norm_num⟩
  | 0 => ⟨((137559439328931/140737488355328), (45023476026723/1125899906842624)), (545921/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((137559439328931/140737488355328), (45023476026723/1125899906842624)), (2082523350242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((268456200582761/281474976710656), (88013566125875/1125899906842624)), (1110849/1125899906842624), by norm_num⟩
  | 2 => ⟨((254319525056859/281474976710656), (41971382035463/281474976710656)), (2292615/1125899906842624), by norm_num⟩
  | 3 => ⟨((894101843800563/1125899906842624), (75844340196617/281474976710656)), (4826583/1125899906842624), by norm_num⟩
  | 4 => ⟨((1256559805628761/2251799813685248), (481837250359493/1125899906842624)), (20533737/2251799813685248), by norm_num⟩
  | 5 => ⟨((288779667639095/2251799813685248), (1075508254289341/2251799813685248)), (40491795/2251799813685248), by norm_num⟩
  | 6 => ⟨((-953303488240529/4503599627370496), (551709640136229/4503599627370496)), (98130337/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/33554432), (-377752187/16777216)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-105212575/67108864), (-841089989/33554432)), (1/33554432), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1873924256728087/9007199254740992), (31108811747159/2251799813685248)), (30604307/4503599627370496), by norm_num⟩
  | 1 => ⟨((-800519355/2147483648), (-53157337/2147483648)), (27/2147483648), by norm_num⟩
  | 2 => ⟨((1434338135/4294967296), (47622581/2147483648)), (25/2147483648), by norm_num⟩
  | 3 => ⟨((-1713325957/8589934592), (-113770947/8589934592)), (31/4294967296), by norm_num⟩
  | 4 => ⟨((383733501/4294967296), (50962543/8589934592)), (57/17179869184), by norm_num⟩
  | 5 => ⟨((-1100093015/34359738368), (-73050095/34359738368)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((1314068051/137438953472), (5453675/8589934592)), (13/34359738368), by norm_num⟩
  | 7 => ⟨((-1345425071/549755813888), (-44670509/274877906944)), (55/549755813888), by norm_num⟩
  | 8 => ⟨((75333691/137438953472), (10004851/274877906944)), (51/2199023255552), by norm_num⟩
  | 9 => ⟨((-959856741/8796093022208), (-127475815/17592186044416)), (83/17592186044416), by norm_num⟩
  | 10 => ⟨((343966481/17592186044416), (91362399/70368744177664)), (61/70368744177664), by norm_num⟩
  | 11 => ⟨((-1792887853/562949953421312), (-119054141/562949953421312)), (81/562949953421312), by norm_num⟩
  | 12 => ⟨((1070807929/2251799813685248), (35552731/1125899906842624)), (25/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773092659/5070602400912917605986812821504), (86371253997/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222443840223663/79228162514264337593543950336), (102301387659/633825300114114700748351602688)), (23053/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890621456198039/39614081257132168796771975168), (28768284591/9903520314283042199192993792)), (25935/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890451401137083/2475880078570760549798248448), (122245655039/2475880078570760549798248448)), (6889/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772117533902123/154742504910672534362390528), (30555915541/38685626227668133590597632)), (6889/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550422219943649/9671406556917033397649408), (114561321449/9671406556917033397649408)), (12917/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629774377417467/302231454903657293676544), (100217800739/604462909807314587353088)), (22605/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944513464068945/37778931862957161709568), (81405073985/37778931862957161709568)), (36733/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324616352958033/1180591620717411303424), (122069318407/4722366482869645213696)), (55101/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622720975872455/590295810358705651712), (167783112461/590295810358705651712)), (18941/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456266299151841/18446744073709551616), (104817816961/36893488147419103232)), (23677/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824445595185941/9223372036854775808), (235711931509/9223372036854775808)), (26637/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595693222296537/1152921504606846976), (3680497539/18014398509481984)), (13319/144115188075855872), by norm_num⟩
  | 5 => ⟨((598036857775997/72057594037927936), (205927908791/144115188075855872)), (93237/144115188075855872), by norm_num⟩
  | 4 => ⟨((186734356781267/4503599627370496), (308532322941/36028797018963968)), (69931/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492051040525641/9007199254740992), (192518516033/4503599627370496)), (21855/1125899906842624), by norm_num⟩
  | 2 => ⟨((558381110561201/1125899906842624), (384096120051/2251799813685248)), (174859/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224442413738941/2251799813685248), (1147595297787/2251799813685248)), (524677/2251799813685248), by norm_num⟩
  | 0 => ⟨((137331693784411/140737488355328), (2276487171815/2251799813685248)), (1049769/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137331693784411/140737488355328), (2276487171815/2251799813685248)), (4004550942427825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((268016348655483/281474976710656), (4442794067697/2251799813685248)), (1025427/1125899906842624), by norm_num⟩
  | 2 => ⟨((255200144514655/281474976710656), (4230363415489/1125899906842624)), (244605/140737488355328), by norm_num⟩
  | 3 => ⟨((1850992113699209/2251799813685248), (3835471868933/562949953421312)), (3563055/1125899906842624), by norm_num⟩
  | 4 => ⟨((1521421402845989/2251799813685248), (25222235612823/2251799813685248)), (11812509/2251799813685248), by norm_num⟩
  | 5 => ⟨((2055322067090291/4503599627370496), (68165294011943/4503599627370496)), (16226791/2251799813685248), by norm_num⟩
  | 6 => ⟨((1873924256728087/9007199254740992), (31108811747159/2251799813685248)), (30604307/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-105212575/67108864), (-841089989/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-57132171/33554432), (-1826903191/67108864)), (1/33554432), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-814622925104941/9007199254740992), (-1424613472275159/9007199254740992)), (145944953/9007199254740992), by norm_num⟩
  | 1 => ⟨((755874165/4294967296), (165234197/536870912)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((-735431605/4294967296), (-321530901/1073741824)), (17/536870912), by norm_num⟩
  | 3 => ⟨((477027941/4294967296), (834226991/4294967296)), (45/2147483648), by norm_num⟩
  | 4 => ⟨((-116031689/2147483648), (-101458173/1073741824)), (89/8589934592), by norm_num⟩
  | 5 => ⟨((180629793/8589934592), (1263542327/34359738368)), (35/8589934592), by norm_num⟩
  | 6 => ⟨((-468652463/68719476736), (-409789973/34359738368)), (23/17179869184), by norm_num⟩
  | 7 => ⟨((521117477/274877906944), (227832705/68719476736)), (13/34359738368), by norm_num⟩
  | 8 => ⟨((-253511947/549755813888), (-443341973/549755813888)), (103/1099511627776), by norm_num⟩
  | 9 => ⟨((438499085/4398046511104), (191711921/1099511627776)), (45/2199023255552), by norm_num⟩
  | 10 => ⟨((-42663991/2199023255552), (-1193773353/35184372088832)), (71/17592186044416), by norm_num⟩
  | 11 => ⟨((60378395/17592186044416), (422359215/70368744177664)), (51/70368744177664), by norm_num⟩
  | 12 => ⟨((-313309151/562949953421312), (-1095830777/1125899906842624)), (67/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (-2722767988223/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779337088533031/633825300114114700748351602688), (-1612116169643/316912650057057350374175801344)), (46259/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945190416597171/19807040628566084398385987584), (-3626706704965/39614081257132168796771975168)), (13013/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890195371990309/2475880078570760549798248448), (-3852705279687/2475880078570760549798248448)), (55317/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885930545958621/77371252455336267181195264), (-3851950924895/154742504910672534362390528)), (27665/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775090683592615/4835703278458516698824704), (-902600648779/2417851639229258349412352)), (25943/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314834392636735/151115727451828646838272), (-1579150495875/302231454903657293676544)), (22707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944341466383523/37778931862957161709568), (-5130736964343/75557863725914323419136)), (2307/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649103348797049/2361183241434822606848), (-3846738595341/4722366482869645213696)), (1731/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1622364078603701/590295810358705651712), (-2643565290713/295147905179352825856)), (76201/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912308664567811/36893488147419103232), (-6605711570161/73786976294838206464)), (95307/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823939346774955/9223372036854775808), (-7427024578555/9223372036854775808)), (53649/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595183981631911/1152921504606846976), (-3710762708763/576460752303423488)), (26849/288230376151711744), by norm_num⟩
  | 5 => ⟨((298906192510675/36028797018963968), (-6487650951919/144115188075855872)), (735/1125899906842624), by norm_num⟩
  | 4 => ⟨((746597366003599/18014398509481984), (-4859557888461/18014398509481984)), (141339/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491189191432725/9007199254740992), (-12127279183095/9007199254740992)), (177057/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115882898823393/2251799813685248), (-12094887122795/2251799813685248)), (177633/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110858789162243/1125899906842624), (-18061460096763/1125899906842624)), (267893/1125899906842624), by norm_num⟩
  | 0 => ⟨((547878233021547/562949953421312), (-8950024202737/281474976710656)), (135393/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547878233021547/562949953421312), (-8950024202737/281474976710656)), (516483307958507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((532640858505385/562949953421312), (-69683259279367/1125899906842624)), (1088587/1125899906842624), by norm_num⟩
  | 2 => ⟨((1003614418214499/1125899906842624), (-32965764381401/281474976710656)), (137169/70368744177664), by norm_num⟩
  | 3 => ⟨((1758333984206265/2251799813685248), (-470164940802477/2251799813685248)), (8853495/2251799813685248), by norm_num⟩
  | 4 => ⟨((318709872765819/562949953421312), (-734263311126535/2251799813685248)), (17523765/2251799813685248), by norm_num⟩
  | 5 => ⟨((60289169096393/281474976710656), (-831395277834257/2251799813685248)), (31270139/2251799813685248), by norm_num⟩
  | 6 => ⟨((-814622925104941/9007199254740992), (-1424613472275159/9007199254740992)), (145944953/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-1826903191/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30526335/16777216), (-1952268141/67108864)), (3/67108864), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-499803171645973/4503599627370496), (1064289823396191/9007199254740992)), (99152103/4503599627370496), by norm_num⟩
  | 1 => ⟨((991164663/4294967296), (-1055301891/4294967296)), (199/4294967296), by norm_num⟩
  | 2 => ⟨((-128816811/536870912), (34288103/134217728)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((714312075/4294967296), (-380267231/2147483648)), (37/1073741824), by norm_num⟩
  | 4 => ⟨((-742685101/8589934592), (790743477/8589934592)), (39/2147483648), by norm_num⟩
  | 5 => ⟨((617748101/17179869184), (-328860967/8589934592)), (33/4294967296), by norm_num⟩
  | 6 => ⟨((-856380709/68719476736), (56987263/4294967296)), (185/68719476736), by norm_num⟩
  | 7 => ⟨((1017596355/274877906944), (-541721975/137438953472)), (223/274877906944), by norm_num⟩
  | 8 => ⟨((-529008033/549755813888), (563239589/549755813888)), (59/274877906944), by norm_num⟩
  | 9 => ⟨((977814471/4398046511104), (-520543911/2199023255552)), (221/4398046511104), by norm_num⟩
  | 10 => ⟨((-203330803/4398046511104), (432976253/8796093022208)), (187/17592186044416), by norm_num⟩
  | 11 => ⟨((76875367/8796093022208), (-163699783/17592186044416)), (143/70368744177664), by norm_num⟩
  | 12 => ⟨((-426287551/281474976710656), (113468043/70368744177664)), (201/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790802825208669/5070602400912917605986812821504), (3028395288345/10141204801825835211973625643008)), (58233/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444788890053455/158456325028528675187087900672), (3585457296293/633825300114114700748351602688)), (69415/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945088285885317/19807040628566084398385987584), (4032979900609/39614081257132168796771975168)), (78109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889978286203865/2475880078570760549798248448), (4284244071399/2475880078570760549798248448)), (41505/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885821970467257/77371252455336267181195264), (2141673712925/77371252455336267181195264)), (10379/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549977718937623/9671406556917033397649408), (125458926511/302231454903657293676544)), (77867/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259159309207421/604462909807314587353088), (877974379141/151115727451828646838272)), (68157/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944196564325783/37778931862957161709568), (713130994847/9444732965739290427392)), (110799/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297989231415087/4722366482869645213696), (2138611972219/2361183241434822606848)), (41569/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622064879144435/590295810358705651712), (2939322591447/295147905179352825856)), (114377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824243055162521/73786976294838206464), (3672250414795/36893488147419103232)), (143065/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823517911798825/9223372036854775808), (8257332230491/9223372036854775808)), (161077/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594762077038065/1152921504606846976), (8250795576199/1152921504606846976)), (20155/144115188075855872), by norm_num⟩
  | 5 => ⟨((298813769256709/36028797018963968), (901511953369/18014398509481984)), (141267/144115188075855872), by norm_num⟩
  | 4 => ⟨((746319572022039/18014398509481984), (5401725265847/18014398509481984)), (106133/18014398509481984), by norm_num⟩
  | 3 => ⟨((745246440969035/4503599627370496), (13478618820033/9007199254740992)), (265973/9007199254740992), by norm_num⟩
  | 2 => ⟨((557591936466147/1125899906842624), (13440113870167/2251799813685248)), (266935/2251799813685248), by norm_num⟩
  | 1 => ⟨((277450882649857/281474976710656), (10032018376923/562949953421312)), (100703/281474976710656), by norm_num⟩
  | 0 => ⟨((273404874027737/281474976710656), (39744309936409/1125899906842624)), (815289/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((273404874027737/281474976710656), (39744309936409/1125899906842624)), (3110080723289107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66303850859797/70368744177664), (38604810198291/562949953421312)), (410347/281474976710656), by norm_num⟩
  | 2 => ⟨((497142788296399/562949953421312), (72749559702125/562949953421312)), (3318265/1125899906842624), by norm_num⟩
  | 3 => ⟨((1718507672295751/2251799813685248), (256981415401823/1125899906842624)), (13436747/2251799813685248), by norm_num⟩
  | 4 => ⟨((298551275733823/562949953421312), (784482761427537/2251799813685248)), (13321407/1125899906842624), by norm_num⟩
  | 5 => ⟨((180014364503593/1125899906842624), (104009391861563/281474976710656)), (46822825/2251799813685248), by norm_num⟩
  | 6 => ⟨((-499803171645973/4503599627370496), (1064289823396191/9007199254740992)), (99152103/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30526335/16777216), (-1952268141/67108864)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log9 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-64510795/33554432), (-257855983/8388608)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1026560957246689/9007199254740992), (412612255732835/4503599627370496)), (139789941/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1075546725/4294967296), (-432301421/2147483648)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((1181608849/4294967296), (949863307/4294967296)), (167/4294967296), by norm_num⟩
  | 3 => ⟨((-865420001/4294967296), (-173921917/1073741824)), (125/4294967296), by norm_num⟩
  | 4 => ⟨((118845131/1073741824), (764291021/8589934592)), (35/2147483648), by norm_num⟩
  | 5 => ⟨((-835614217/17179869184), (-335863803/8589934592)), (125/17179869184), by norm_num⟩
  | 6 => ⟨((306005349/17179869184), (245989401/17179869184)), (47/17179869184), by norm_num⟩
  | 7 => ⟨((-48025891/8589934592), (-154426845/34359738368)), (15/17179869184), by norm_num⟩
  | 8 => ⟨((844189345/549755813888), (678620919/549755813888)), (67/274877906944), by norm_num⟩
  | 9 => ⟨((-824388257/2199023255552), (-662703361/2199023255552)), (133/2199023255552), by norm_num⟩
  | 10 => ⟨((90568307/1099511627776), (582443245/8796093022208)), (119/8796093022208), by norm_num⟩
  | 11 => ⟨((-1157811841/70368744177664), (-930733537/70368744177664)), (193/70368744177664), by norm_num⟩
  | 12 => ⟨((423995439/140737488355328), (170419217/70368744177664)), (9/17592186044416), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403057283/10141204801825835211973625643008), (881995738239/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889501462228679/316912650057057350374175801344), (1044058025333/633825300114114700748351602688)), (92303/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945002622885003/19807040628566084398385987584), (587183612745/19807040628566084398385987584)), (12981/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889796751499883/2475880078570760549798248448), (1247520468227/2475880078570760549798248448)), (55173/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221432870930853/19342813113834066795298816), (1247245259835/154742504910672534362390528)), (55177/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549808652265247/9671406556917033397649408), (1169000104621/9671406556917033397649408)), (103467/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629505985740769/302231454903657293676544), (1022582857825/604462909807314587353088)), (45271/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944077410427939/37778931862957161709568), (415287350695/18889465931478580854784)), (36787/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297811476311955/4722366482869645213696), (1245382975505/4722366482869645213696)), (13797/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810911025014505/295147905179352825856), (855811730501/295147905179352825856)), (9487/36893488147419103232), by norm_num⟩
  | 8 => ⟨((911970946245347/36893488147419103232), (2138362776409/73786976294838206464)), (11861/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911591181797033/4611686018427387904), (1202027582973/4611686018427387904)), (53387/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398607649372077/288230376151711744), (1201026520363/576460752303423488)), (213611/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74685600080179/9007199254740992), (2099546179019/144115188075855872)), (186981/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492220047238039/36028797018963968), (3144824198051/36028797018963968)), (140307/18014398509481984), by norm_num⟩
  | 3 => ⟨((372496229588413/2251799813685248), (3923175993135/9007199254740992)), (351017/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229399353301861/4503599627370496), (3911418812375/2251799813685248)), (702785/4503599627370496), by norm_num⟩
  | 1 => ⟨((554568163364827/562949953421312), (1459454950947/281474976710656)), (528031/1125899906842624), by norm_num⟩
  | 0 => ⟨((2185038979977379/2251799813685248), (5779455922959/562949953421312)), (2119699/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185038979977379/2251799813685248), (5779455922959/562949953421312)), (8086009987837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120020119566285/2251799813685248), (2804053983391/140737488355328)), (2078617/1125899906842624), by norm_num⟩
  | 2 => ⟨((124691158825073/140737488355328), (84478569720245/2251799813685248)), (1998387/562949953421312), by norm_num⟩
  | 3 => ⟨((1764420589224327/2251799813685248), (74846658679221/1125899906842624)), (3691021/562949953421312), by norm_num⟩
  | 4 => ⟨((1372578462629257/2251799813685248), (29323429375397/281474976710656)), (25100047/2251799813685248), by norm_num⟩
  | 5 => ⟨((1624425368806759/4503599627370496), (571968536335987/4503599627370496)), (71658129/4503599627370496), by norm_num⟩
  | 6 => ⟨((1026560957246689/9007199254740992), (412612255732835/4503599627370496)), (139789941/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/33554432), (-257855983/8388608)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-67604193/33554432), (-540441199/16777216)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((209879955122133/2251799813685248), (-859021613019923/9007199254740992)), (137415117/9007199254740992), by norm_num⟩
  | 1 => ⟨((-460878807/2147483648), (471584883/2147483648)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((1061212671/4294967296), (-542932161/2147483648)), (179/4294967296), by norm_num⟩
  | 3 => ⟨((-407255413/2147483648), (833431667/4294967296)), (35/1073741824), by norm_num⟩
  | 4 => ⟨((937740243/8589934592), (-479761833/4294967296)), (41/2147483648), by norm_num⟩
  | 5 => ⟨((-431845341/8589934592), (220938489/4294967296)), (153/17179869184), by norm_num⟩
  | 6 => ⟨((662907097/34359738368), (-169576557/8589934592)), (15/4294967296), by norm_num⟩
  | 7 => ⟨((-872228571/137438953472), (892490177/137438953472)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((1004190253/549755813888), (-1027517289/549755813888)), (187/549755813888), by norm_num⟩
  | 9 => ⟨((-1027659337/2199023255552), (32860361/68719476736)), (97/1099511627776), by norm_num⟩
  | 10 => ⟨((236627307/2199023255552), (-968496351/8796093022208)), (181/8796093022208), by norm_num⟩
  | 11 => ⟨((-792515651/35184372088832), (810925549/35184372088832)), (77/17592186044416), by norm_num⟩
  | 12 => ⟨((608278241/140737488355328), (-77801045/17592186044416)), (15/17592186044416), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (-1038024068129/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778860556699229/633825300114114700748351602688), (-1228568871137/633825300114114700748351602688)), (92321/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472461274253903/9903520314283042199192993792), (-1381896112293/39614081257132168796771975168)), (103869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944813305532877/1237940039285380274899124224), (-366990714727/618970019642690137449562112)), (55185/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221411605854511/19342813113834066795298816), (-733811746395/77371252455336267181195264)), (27595/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549649185256365/9671406556917033397649408), (-687768276665/4835703278458516698824704)), (25873/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258872458913953/604462909807314587353088), (-601617065761/302231454903657293676544)), (90567/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943964076216981/37778931862957161709568), (-488645013571/18889465931478580854784)), (147191/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648820754780775/2361183241434822606848), (-183168038639/590295810358705651712)), (110411/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621588401922935/590295810358705651712), (-2013888957817/590295810358705651712)), (151843/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823649916632025/73786976294838206464), (-2515922821383/73786976294838206464)), (189847/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822854006646413/9223372036854775808), (-176777296681/576460752303423488)), (213637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594102385432243/1152921504606846976), (-353246027629/144115188075855872)), (13357/72057594037927936), by norm_num⟩
  | 5 => ⟨((597341289385421/72057594037927936), (-2469947860583/144115188075855872)), (93541/72057594037927936), by norm_num⟩
  | 4 => ⟨((23309216244193/562949953421312), (-3699380015149/36028797018963968)), (280789/36028797018963968), by norm_num⟩
  | 3 => ⟨((93090483112893/562949953421312), (-2307271197219/4503599627370496)), (351281/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228326689842037/4503599627370496), (-9200098751111/4503599627370496)), (175861/1125899906842624), by norm_num⟩
  | 1 => ⟨((554166986226217/562949953421312), (-13727899024339/2251799813685248)), (528691/1125899906842624), by norm_num⟩
  | 0 => ⟨((136365420271543/140737488355328), (-13584047067207/1125899906842624)), (265459/281474976710656), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((136365420271543/140737488355328), (-13584047067207/1125899906842624)), (1012645722509288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((66054342873139/70368744177664), (-52648212184411/2251799813685248)), (1041661/562949953421312), by norm_num⟩
  | 2 => ⟨((247863985295063/281474976710656), (-6177535033357/140737488355328)), (501075/140737488355328), by norm_num⟩
  | 3 => ⟨((1741793410303609/2251799813685248), (-174075973139649/2251799813685248)), (1852943/281474976710656), by norm_num⟩
  | 4 => ⟨((666920261183659/1125899906842624), (-269299589656339/2251799813685248)), (25224245/2251799813685248), by norm_num⟩
  | 5 => ⟨((378943159100597/1125899906842624), (-319036091181349/2251799813685248)), (71832317/4503599627370496), by norm_num⟩
  | 6 => ⟨((209879955122133/2251799813685248), (-859021613019923/9007199254740992)), (137415117/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-540441199/16777216)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4400157/2097152), (-562811511/16777216)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-293232306262879/4503599627370496), (-234138617212187/2251799813685248)), (99302523/4503599627370496), by norm_num⟩
  | 1 => ⟨((670566903/4294967296), (535430797/2147483648)), (229/4294967296), by norm_num⟩
  | 2 => ⟨((-803974603/4294967296), (-1283906977/4294967296)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((642615633/4294967296), (128278103/536870912)), (7/134217728), by norm_num⟩
  | 4 => ⟨((-385231247/4294967296), (-1230389827/8589934592)), (271/8589934592), by norm_num⟩
  | 5 => ⟨((738995349/17179869184), (295034595/4294967296)), (131/8589934592), by norm_num⟩
  | 6 => ⟨((-295338909/17179869184), (-235820687/8589934592)), (53/8589934592), by norm_num⟩
  | 7 => ⟨((809362027/137438953472), (161563803/17179869184)), (293/137438953472), by norm_num⟩
  | 8 => ⟨((-485191345/274877906944), (-774826159/274877906944)), (89/137438953472), by norm_num⟩
  | 9 => ⟨((258541785/549755813888), (825756437/1099511627776)), (3/17179869184), by norm_num⟩
  | 10 => ⟨((-495964899/4398046511104), (-792030983/4398046511104)), (93/2199023255552), by norm_num⟩
  | 11 => ⟨((54057813/2199023255552), (690620855/17592186044416)), (41/4398046511104), by norm_num⟩
  | 12 => ⟨((-172833299/35184372088832), (-552012161/70368744177664)), (33/17592186044416), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681581499/10141204801825835211973625643008), (-2774893226773/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778727026297037/633825300114114700748351602688), (-820953572489/158456325028528675187087900672)), (23131/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889694621679745/39614081257132168796771975168), (-3693603303345/39614081257132168796771975168)), (52055/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118091649905861/154742504910672534362390528), (-3923612407991/2475880078570760549798248448)), (110641/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885566130246443/77371252455336267181195264), (-980666586177/38685626227668133590597632)), (27667/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387374559674501/2417851639229258349412352), (-1838247359497/4835703278458516698824704)), (25945/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258739984117907/604462909807314587353088), (-3215928139453/604462909807314587353088)), (22709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887712137991043/75557863725914323419136), (-1305999962173/18889465931478580854784)), (73831/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648739424668993/2361183241434822606848), (-3916352439803/4722366482869645213696)), (55397/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810681845032069/295147905179352825856), (-5382308458141/590295810358705651712)), (152419/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823367447846591/73786976294838206464), (-6723873022897/73786976294838206464)), (95319/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822534061624205/9223372036854775808), (-1889710652199/2305843009213693952)), (107313/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593779736007559/1152921504606846976), (-7551953502427/1152921504606846976)), (26853/144115188075855872), by norm_num⟩
  | 5 => ⟨((597198612569109/72057594037927936), (-6600214667871/144115188075855872)), (188195/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491355756048269/36028797018963968), (-2471211675893/9007199254740992)), (282739/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488894571972277/9007199254740992), (-6164504049101/4503599627370496)), (177103/4503599627370496), by norm_num⟩
  | 2 => ⟨((69599652256967/140737488355328), (-1536061957573/281474976710656)), (177691/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107441507717479/1125899906842624), (-18331682854071/1125899906842624)), (134005/281474976710656), by norm_num⟩
  | 0 => ⟨((2177967351451925/2251799813685248), (-72520891981451/2251799813685248)), (1083873/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2177967351451925/2251799813685248), (-72520891981451/2251799813685248)), (4134647373679732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2104220133343983/2251799813685248), (-70143062484439/1125899906842624)), (541621/281474976710656), by norm_num⟩
  | 2 => ⟨((978786423624675/1125899906842624), (-65545988323273/562949953421312)), (2159467/562949953421312), by norm_num⟩
  | 3 => ⟨((1671263583934893/2251799813685248), (-113963102943659/562949953421312)), (1064369/140737488355328), by norm_num⟩
  | 4 => ⟨((574056479167007/1125899906842624), (-169164579110835/562949953421312)), (32173893/2251799813685248), by norm_num⟩
  | 5 => ⟨((95512141294057/562949953421312), (-1380016423754207/4503599627370496)), (6518119/281474976710656), by norm_num⟩
  | 6 => ⟨((-293232306262879/4503599627370496), (-234138617212187/2251799813685248)), (99302523/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4400157/2097152), (-562811511/16777216)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-72957177/33554432), (-291617003/8388608)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1002377152830107/9007199254740992), (209394637817059/9007199254740992)), (175275873/9007199254740992), by norm_num⟩
  | 1 => ⟨((1187712503/4294967296), (-15506927/268435456)), (105/2147483648), by norm_num⟩
  | 2 => ⟨((-368919337/1073741824), (19266633/268435456)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((611153409/2147483648), (-255337517/4294967296)), (55/1073741824), by norm_num⟩
  | 4 => ⟨((-759329585/4294967296), (317244947/8589934592)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((377372627/4294967296), (-315329631/17179869184)), (277/17179869184), by norm_num⟩
  | 6 => ⟨((-1250314333/34359738368), (32648529/4294967296)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((1775379657/137438953472), (-370873357/137438953472)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((-1102913179/274877906944), (115198209/137438953472)), (13/17179869184), by norm_num⟩
  | 9 => ⟨((609030287/549755813888), (-254450485/1099511627776)), (29/137438953472), by norm_num⟩
  | 10 => ⟨((-151338341/549755813888), (252914281/4398046511104)), (233/4398046511104), by norm_num⟩
  | 11 => ⟨((1093997527/17592186044416), (-57133489/4398046511104)), (53/4398046511104), by norm_num⟩
  | 12 => ⟨((-14158759/1099511627776), (94647591/35184372088832)), (89/35184372088832), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790571753654357/5070602400912917605986812821504), (3824019830817/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222325560052375/79228162514264337593543950336), (2262392105863/316912650057057350374175801344)), (92645/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236194561511805/4951760157141521099596496896), (2544693786447/19807040628566084398385987584)), (104255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889319285358157/2475880078570760549798248448), (2703135845023/1237940039285380274899124224)), (27701/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770984753434981/154742504910672534362390528), (675614850365/19342813113834066795298816)), (110841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387339883148411/2417851639229258349412352), (2532837063443/4835703278458516698824704)), (103953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258618198381703/604462909807314587353088), (4431027825291/604462909807314587353088)), (90999/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887513453344717/75557863725914323419136), (1799431557909/18889465931478580854784)), (147947/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648664575804483/2361183241434822606848), (2697968947661/2361183241434822606848)), (55513/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25330574143021/9223372036854775808), (926948212611/73786976294838206464)), (76383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455776775823211/18446744073709551616), (72372970897/576460752303423488)), (47779/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822238890678035/9223372036854775808), (10413815215319/9223372036854775808)), (26903/1152921504606846976), by norm_num⟩
  | 6 => ⟨((24898151823625/18014398509481984), (2600988289229/288230376151711744)), (107749/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194133261835511/144115188075855872), (2273092318081/36028797018963968)), (188869/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490953438168803/36028797018963968), (3404096787207/9007199254740992)), (141959/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488380566746295/9007199254740992), (4245430203055/2251799813685248)), (355979/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113063858403601/2251799813685248), (4230908437293/562949953421312)), (357601/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106604521929539/1125899906842624), (3155054449101/140737488355328)), (135117/281474976710656), by norm_num⟩
  | 0 => ⟨((1087147093611139/1125899906842624), (24951017178033/562949953421312)), (548633/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087147093611139/1125899906842624), (24951017178033/562949953421312)), (2092868807079124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((523758187982125/562949953421312), (96368871310447/1125899906842624)), (2216265/1125899906842624), by norm_num⟩
  | 2 => ⟨((483170658396593/562949953421312), (179319618409019/1125899906842624)), (4503337/1125899906842624), by norm_num⟩
  | 3 => ⟨((800834967225257/1125899906842624), (615628281438145/2251799813685248)), (18329507/2251799813685248), by norm_num⟩
  | 4 => ⟨((485466866265989/1125899906842624), (437886753158219/1125899906842624)), (18048667/1125899906842624), by norm_num⟩
  | 5 => ⟨((19510291005297/562949953421312), (377617066211949/1125899906842624)), (118414095/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1002377152830107/9007199254740992), (209394637817059/9007199254740992)), (175275873/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72957177/33554432), (-291617003/8388608)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75307241/33554432), (-1204041761/33554432)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-115824873898111/4503599627370496), (231555149400177/2251799813685248)), (163857709/9007199254740992), by norm_num⟩
  | 1 => ⟨((283322273/4294967296), (-566413147/2147483648)), (203/4294967296), by norm_num⟩
  | 2 => ⟨((-363353641/4294967296), (726410519/2147483648)), (263/4294967296), by norm_num⟩
  | 3 => ⟨((310661229/4294967296), (-1242137463/4294967296)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-49801895/1073741824), (398252461/2147483648)), (293/8589934592), by norm_num⟩
  | 5 => ⟨((102191471/4294967296), (-1634395831/17179869184)), (303/17179869184), by norm_num⟩
  | 6 => ⟨((-349487931/34359738368), (698690423/17179869184)), (131/17179869184), by norm_num⟩
  | 7 => ⟨((128059835/34359738368), (-1024060315/68719476736)), (97/34359738368), by norm_num⟩
  | 8 => ⟨((-20529187/17179869184), (41041607/8589934592)), (251/274877906944), by norm_num⟩
  | 9 => ⟨((187222489/549755813888), (-1497168263/1099511627776)), (289/1099511627776), by norm_num⟩
  | 10 => ⟨((-192086481/2199023255552), (768032155/2199023255552)), (299/4398046511104), by norm_num⟩
  | 11 => ⟨((89580381/4398046511104), (-1432700787/17592186044416)), (141/8796093022208), by norm_num⟩
  | 12 => ⟨((-153179427/35184372088832), (306233747/17592186044416)), (243/70368744177664), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275821141/10141204801825835211973625643008), (1182687434203/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444625826261971/158456325028528675187087900672), (1399257067009/316912650057057350374175801344)), (23119/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236180384237543/4951760157141521099596496896), (1573853508691/19807040628566084398385987584)), (104053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889199304744565/2475880078570760549798248448), (3343672463963/2475880078570760549798248448)), (110577/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770865364380345/154742504910672534362390528), (3342810682097/154742504910672534362390528)), (13825/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774624116742365/4835703278458516698824704), (3132969617711/9671406556917033397649408)), (3241/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258521439339771/604462909807314587353088), (171277080995/37778931862957161709568)), (90773/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943678697919781/37778931862957161709568), (2225744422773/37778931862957161709568)), (147551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648606568233643/2361183241434822606848), (3337116370123/4722366482869645213696)), (6919/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620998893016285/590295810358705651712), (4586098183475/590295810358705651712)), (152283/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911456144001811/36893488147419103232), (2864484710963/36893488147419103232)), (47613/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455505788928243/2305843009213693952), (6440070438353/9223372036854775808)), (214393/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796635132196425/576460752303423488), (6433799939395/1152921504606846976)), (107281/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193953048525761/144115188075855872), (2811263549379/72057594037927936)), (187933/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490692706902841/36028797018963968), (8419711100259/36028797018963968)), (282279/36028797018963968), by norm_num⟩
  | 3 => ⟨((744035686960723/4503599627370496), (5250017987673/4503599627370496)), (353517/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112779629724571/2251799813685248), (10463204179371/2251799813685248)), (709041/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212480356074727/2251799813685248), (31205960862869/2251799813685248)), (1068593/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173327883488875/2251799813685248), (61680354259517/2251799813685248)), (2157389/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2173327883488875/2251799813685248), (61680354259517/2251799813685248)), (8229785927779387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2095901062947837/2251799813685248), (119061768245103/2251799813685248)), (1070651/562949953421312), by norm_num⟩
  | 2 => ⟨((1944500365617429/2251799813685248), (27704692609083/281474976710656)), (2106273/562949953421312), by norm_num⟩
  | 3 => ⟨((1657322489184591/2251799813685248), (382782054285829/2251799813685248)), (8104589/1125899906842624), by norm_num⟩
  | 4 => ⟨((4510620578563/8796093022208), (281727222450537/1125899906842624)), (917833/70368744177664), by norm_num⟩
  | 5 => ⟨((902295796208265/4503599627370496), (1155753677382371/4503599627370496)), (700327/35184372088832), by norm_num⟩
  | 6 => ⟨((-115824873898111/4503599627370496), (231555149400177/2251799813685248)), (163857709/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75307241/33554432), (-1204041761/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-77483061/33554432), (-1238829619/33554432)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((636686484763457/9007199254740992), (314365974050689/4503599627370496)), (101769751/9007199254740992), by norm_num⟩
  | 1 => ⟨((-801206653/4294967296), (-791196659/4294967296)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((1057215145/4294967296), (1044006671/4294967296)), (87/2147483648), by norm_num⟩
  | 3 => ⟨((-465008563/2147483648), (-918397819/4294967296)), (155/4294967296), by norm_num⟩
  | 4 => ⟨((9587377/67108864), (151481531/1073741824)), (13/536870912), by norm_num⟩
  | 5 => ⟨((-647721921/8589934592), (-639629511/8589934592)), (7/536870912), by norm_num⟩
  | 6 => ⟨((569791761/17179869184), (562672983/17179869184)), (25/4294967296), by norm_num⟩
  | 7 => ⟨((-429632321/34359738368), (-848529291/68719476736)), (153/68719476736), by norm_num⟩
  | 8 => ⟨((566912163/137438953472), (559829361/137438953472)), (103/137438953472), by norm_num⟩
  | 9 => ⟨((-332469711/274877906944), (-656631901/549755813888)), (123/549755813888), by norm_num⟩
  | 10 => ⟨((350962651/1099511627776), (173288923/549755813888)), (33/549755813888), by norm_num⟩
  | 11 => ⟨((-673607677/8796093022208), (-332595929/4398046511104)), (129/8796093022208), by norm_num⟩
  | 12 => ⟨((148140773/8796093022208), (73144977/4398046511104)), (115/35184372088832), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (1014880569187/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111150424890235/39614081257132168796771975168), (1200593455199/633825300114114700748351602688)), (92319/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889334717510661/39614081257132168796771975168), (1350396456113/39614081257132168796771975168)), (51933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889084455099089/2475880078570760549798248448), (1434458339681/2475880078570760549798248448)), (110367/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770750828363297/154742504910672534362390528), (358519590755/38685626227668133590597632)), (110377/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48410662155693/302231454903657293676544), (1344044877269/9671406556917033397649408)), (1617/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1258428108169507/604462909807314587353088), (1175635833867/604462909807314587353088)), (90563/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887206356112533/75557863725914323419136), (1909652119551/75557863725914323419136)), (147185/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324275100412705/1180591620717411303424), (1431577820617/4722366482869645213696)), (55203/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810422383632061/295147905179352825856), (1967345555105/590295810358705651712)), (37959/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455680239011987/18446744073709551616), (76799127977/2305843009213693952)), (189837/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821809726706739/9223372036854775808), (2762556808891/9223372036854775808)), (213625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593059105565889/1152921504606846976), (2759794674163/1152921504606846976)), (106849/576460752303423488), by norm_num⟩
  | 5 => ⟨((596885416419439/72057594037927936), (2411716527753/144115188075855872)), (46767/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490424465806687/36028797018963968), (3611376130091/36028797018963968)), (280765/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487744935061411/9007199254740992), (4503392641335/9007199254740992)), (351245/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224932842578843/4503599627370496), (8974383115917/4503599627370496)), (351679/2251799813685248), by norm_num⟩
  | 1 => ⟨((2211606440939019/2251799813685248), (6690424989701/1125899906842624)), (1057215/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171840253564589/2251799813685248), (26440480188031/2251799813685248)), (2123197/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2171840253564589/2251799813685248), (26440480188031/2251799813685248)), (8099353798873137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1047204764683879/1125899906842624), (12750800236981/562949953421312)), (2072735/1125899906842624), by norm_num⟩
  | 2 => ⟨((1946864869406335/2251799813685248), (23719157769795/562949953421312)), (246851/70368744177664), by norm_num⟩
  | 3 => ⟨((1679226200136879/2251799813685248), (164057194474481/2251799813685248)), (14324711/2251799813685248), by norm_num⟩
  | 4 => ⟨((77518154899739/140737488355328), (122341754186239/1125899906842624)), (11725955/1125899906842624), by norm_num⟩
  | 5 => ⟨((1313127785644743/4503599627370496), (539086332293815/4503599627370496)), (61862475/4503599627370496), by norm_num⟩
  | 6 => ⟨((636686484763457/9007199254740992), (314365974050689/4503599627370496)), (101769751/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-1238829619/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-79508701/33554432), (-317804085/8388608)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((413920208784593/4503599627370496), (-311707574924833/18014398509481984)), (124178967/18014398509481984), by norm_num⟩
  | 1 => ⟨((-33405921/134217728), (100626917/2147483648)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((1447438577/4294967296), (-272502743/4294967296)), (113/4294967296), by norm_num⟩
  | 3 => ⟨((-163322347/536870912), (245983703/4294967296)), (13/536870912), by norm_num⟩
  | 4 => ⟨((884570229/4294967296), (-83267027/2147483648)), (143/8589934592), by norm_num⟩
  | 5 => ⟨((-479092117/4294967296), (180393031/8589934592)), (5/536870912), by norm_num⟩
  | 6 => ⟨((1729874005/34359738368), (-325675589/34359738368)), (147/34359738368), by norm_num⟩
  | 7 => ⟨((-669226521/34359738368), (251984527/68719476736)), (29/17179869184), by norm_num⟩
  | 8 => ⟨((906149507/137438953472), (-170596687/137438953472)), (5/8589934592), by norm_num⟩
  | 9 => ⟨((-1090621491/549755813888), (205326397/549755813888)), (49/274877906944), by norm_num⟩
  | 10 => ⟨((1181383099/2199023255552), (-55603419/549755813888)), (27/549755813888), by norm_num⟩
  | 11 => ⟨((-1163361723/8796093022208), (219020873/8796093022208)), (27/2199023255552), by norm_num⟩
  | 12 => ⟨((262536829/8796093022208), (-98853253/17592186044416)), (99/35184372088832), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580889171562799/10141204801825835211973625643008), (-242399545067/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778314504142475/633825300114114700748351602688), (-286727630913/633825300114114700748351602688)), (92229/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118076934278821/2475880078570760549798248448), (-161251178175/19807040628566084398385987584)), (6485/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944487140223885/1237940039285380274899124224), (-342575966681/2475880078570760549798248448)), (55123/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770640743599263/154742504910672534362390528), (-342482872959/154742504910672534362390528)), (110249/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549038079964755/9671406556917033397649408), (-160489408531/4835703278458516698824704)), (103361/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629168991582323/302231454903657293676544), (-280757628819/604462909807314587353088)), (22611/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887060081692427/75557863725914323419136), (-114011478641/18889465931478580854784)), (146975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648495426037365/2361183241434822606848), (-170936221541/2361183241434822606848)), (27559/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810347195116499/295147905179352825856), (-469811530887/590295810358705651712)), (151581/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227816670596479/9223372036854775808), (-586870075909/73786976294838206464)), (94743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455399802080627/2305843009213693952), (-82460884427/1152921504606846976)), (106593/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99553077397531/72057594037927936), (-659010556325/1152921504606846976)), (53301/288230376151711744), by norm_num⟩
  | 5 => ⟨((149198491267165/18014398509481984), (-575874087983/144115188075855872)), (93287/72057594037927936), by norm_num⟩
  | 4 => ⟨((745075785142367/18014398509481984), (-26946661537/1125899906842624)), (139951/18014398509481984), by norm_num⟩
  | 3 => ⟨((371851589958633/2251799813685248), (-537607635665/4503599627370496)), (349949/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224263291732395/4503599627370496), (-2142497908253/4503599627370496)), (175029/1125899906842624), by norm_num⟩
  | 1 => ⟨((138163812429909/140737488355328), (-3193988359927/2251799813685248)), (525365/1125899906842624), by norm_num⟩
  | 0 => ⟨((542486055171435/562949953421312), (-1577344918637/562949953421312)), (1051867/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542486055171435/562949953421312), (-1577344918637/562949953421312)), (4012554172996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((522761624279285/562949953421312), (-12160052485741/2251799813685248)), (508289/281474976710656), by norm_num⟩
  | 2 => ⟨((242712937871781/281474976710656), (-22583921537373/2251799813685248)), (1898991/562949953421312), by norm_num⟩
  | 3 => ⟨((1674084186809237/2251799813685248), (-608558752835/35184372088832)), (6626103/1125899906842624), by norm_num⟩
  | 4 => ⟨((38872251757771/70368744177664), (-57910857825927/2251799813685248)), (20162941/2251799813685248), by norm_num⟩
  | 5 => ⟨((42853596677513/140737488355328), (-31990416643423/1125899906842624)), (46626843/4503599627370496), by norm_num⟩
  | 6 => ⟨((413920208784593/4503599627370496), (-311707574924833/18014398509481984)), (124178967/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-79508701/33554432), (-317804085/8388608)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/4194304), (-650756047/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((737850343302293/18014398509481984), (-705492387900647/9007199254740992)), (214056593/18014398509481984), by norm_num⟩
  | 1 => ⟨((-487746129/4294967296), (932712669/4294967296)), (9/268435456), by norm_num⟩
  | 2 => ⟨((169039927/1073741824), (-646507157/2147483648)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-156226065/1073741824), (149374871/536870912)), (189/4294967296), by norm_num⟩
  | 4 => ⟨((216575313/2147483648), (-828310165/4294967296)), (133/4294967296), by norm_num⟩
  | 5 => ⟨((-60047427/1073741824), (918625369/8589934592)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((221982425/8589934592), (-848990113/17179869184)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((-351694839/34359738368), (672542975/34359738368)), (7/2147483648), by norm_num⟩
  | 8 => ⟨((121888143/34359738368), (-466171267/68719476736)), (157/137438953472), by norm_num⟩
  | 9 => ⟨((-600792339/549755813888), (1148889953/549755813888)), (49/137438953472), by norm_num⟩
  | 10 => ⟨((666300025/2199023255552), (-1274159731/2199023255552)), (55/549755813888), by norm_num⟩
  | 11 => ⟨((-671773067/8796093022208), (642312891/4398046511104)), (7/274877906944), by norm_num⟩
  | 12 => ⟨((620850143/35184372088832), (-1187246319/35184372088832)), (209/35184372088832), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395203902880331/2535301200456458802993406410752), (-1418506538131/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778226031628655/633825300114114700748351602688), (-419438797289/158456325028528675187087900672)), (92365/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472282839022783/9903520314283042199192993792), (-943538393285/19807040628566084398385987584)), (51961/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888868381539095/2475880078570760549798248448), (-2004522962347/2475880078570760549798248448)), (110429/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221316844067043/19342813113834066795298816), (-2003965054235/154742504910672534362390528)), (110443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774469307756813/4835703278458516698824704), (-1878124666167/9671406556917033397649408)), (25889/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629125427017567/302231454903657293676544), (-1642766741601/604462909807314587353088)), (45313/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943459156902855/37778931862957161709568), (-2668385805591/75557863725914323419136)), (73647/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162110545773889/590295810358705651712), (-2000318463555/4722366482869645213696)), (110495/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620547712571105/590295810358705651712), (-2748861108697/590295810358705651712)), (75985/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911174814497831/36893488147419103232), (-1716856412193/36893488147419103232)), (190021/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910695986091555/4611686018427387904), (-3859679639177/9223372036854775808)), (213855/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796320668542103/576460752303423488), (-3855624438777/1152921504606846976)), (53489/288230376151711744), by norm_num⟩
  | 5 => ⟨((596702635220325/72057594037927936), (-3369114654339/144115188075855872)), (93663/72057594037927936), by norm_num⟩
  | 4 => ⟨((744938047033081/18014398509481984), (-5044571933631/36028797018963968)), (281219/36028797018963968), by norm_num⟩
  | 3 => ⟨((743529712597619/4503599627370496), (-6289819965177/9007199254740992)), (175963/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223561703449383/4503599627370496), (-12532075385179/4503599627370496)), (176265/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104774745033719/1125899906842624), (-18679621825061/2251799813685248)), (1060625/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083862859325811/1125899906842624), (-9221947876661/562949953421312)), (533363/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083862859325811/1125899906842624), (-9221947876661/562949953421312)), (2034618379833030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((521546592817829/562949953421312), (-35510534225663/1125899906842624)), (1044373/562949953421312), by norm_num⟩
  | 2 => ⟨((1930513341858659/2251799813685248), (-131595343578791/2251799813685248)), (4002007/1125899906842624), by norm_num⟩
  | 3 => ⟨((1647377536003821/2251799813685248), (-225638677968947/2251799813685248)), (3664879/562949953421312), by norm_num⟩
  | 4 => ⟨((1182582890783855/2251799813685248), (-82536664023279/562949953421312)), (12193585/1125899906842624), by norm_num⟩
  | 5 => ⟨((143163867321631/562949953421312), (-693535516918367/4503599627370496)), (16382981/1125899906842624), by norm_num⟩
  | 6 => ⟨((737850343302293/18014398509481984), (-705492387900647/9007199254740992)), (214056593/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/4194304), (-650756047/16777216)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41591753/16777216), (-332492645/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-540832073554603/18014398509481984), (-1409822987744623/18014398509481984)), (16633511/1125899906842624), by norm_num⟩
  | 1 => ⟨((91331759/1073741824), (952322317/4294967296)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-517524717/4294967296), (-337266537/1073741824)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((488752645/4294967296), (1274064071/4294967296)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-346185129/4294967296), (-112802979/536870912)), (177/4294967296), by norm_num⟩
  | 5 => ⟨((392326531/8589934592), (1022703697/8589934592)), (101/4294967296), by norm_num⟩
  | 6 => ⟨((-370514921/17179869184), (-965845921/17179869184)), (193/17179869184), by norm_num⟩
  | 7 => ⟨((74981987/8589934592), (390921079/17179869184)), (79/17179869184), by norm_num⟩
  | 8 => ⟨((-106219983/34359738368), (-553781409/68719476736)), (113/68719476736), by norm_num⟩
  | 9 => ⟨((267505665/274877906944), (1394649669/549755813888)), (287/549755813888), by norm_num⟩
  | 10 => ⟨((-37895031/137438953472), (-790268011/1099511627776)), (41/274877906944), by norm_num⟩
  | 11 => ⟨((312333695/4398046511104), (814181045/4398046511104)), (171/4398046511104), by norm_num⟩
  | 12 => ⟨((-294969331/17592186044416), (-1537832401/35184372088832)), (325/35184372088832), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512500455/10141204801825835211973625643008), (-630822305357/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444535260684369/158456325028528675187087900672), (-746047098171/158456325028528675187087900672)), (92495/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889035582982895/39614081257132168796771975168), (-419560460257/4951760157141521099596496896)), (104075/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888766407615087/2475880078570760549798248448), (-445670187719/309485009821345068724781056)), (55301/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442608134252775/38685626227668133590597632), (-1782173309157/77371252455336267181195264)), (55313/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774421265983001/4835703278458516698824704), (-1670248483801/4835703278458516698824704)), (51869/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314541631168265/151115727451828646838272), (-91308038339/18889465931478580854784)), (90797/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886780798607393/75557863725914323419136), (-4745998236737/75557863725914323419136)), (73797/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296780810303789/4722366482869645213696), (-444716521287/590295810358705651712)), (110739/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202550580311311/73786976294838206464), (-1222253155485/147573952589676412928)), (9521/36893488147419103232), by norm_num⟩
  | 8 => ⟨((911084885961705/36893488147419103232), (-1526741166701/18446744073709551616)), (47631/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455297058463067/2305843009213693952), (-6864425377567/9223372036854775808)), (53621/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592435853815485/1152921504606846976), (-3428522132775/576460752303423488)), (26833/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193223514972593/144115188075855872), (-5991618540851/144115188075855872)), (188035/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489599559240547/36028797018963968), (-4485429406061/18014398509481984)), (282459/36028797018963968), by norm_num⟩
  | 3 => ⟨((185838369916791/1125899906842624), (-1398078229905/1125899906842624)), (353787/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111418250719201/2251799813685248), (-22282600735705/4503599627370496)), (709717/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208411435690277/2251799813685248), (-33207945118703/2251799813685248)), (8359/17592186044416), by norm_num⟩
  | 0 => ⟨((1082625569013753/1125899906842624), (-32778043560769/1125899906842624)), (2161501/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082625569013753/1125899906842624), (-32778043560769/1125899906842624)), (8245471962935637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520030117875461/562949953421312), (-63036417083735/1125899906842624)), (2141351/1125899906842624), by norm_num⟩
  | 2 => ⟨((957235805386877/1125899906842624), (-232921844702371/2251799813685248)), (8391927/2251799813685248), by norm_num⟩
  | 3 => ⟨((1603583471662827/2251799813685248), (-396058527495795/2251799813685248)), (16005659/2251799813685248), by norm_num⟩
  | 4 => ⟨((1072305619137767/2251799813685248), (-564093579405677/2251799813685248)), (14213337/1125899906842624), by norm_num⟩
  | 5 => ⟨((738642724325197/4503599627370496), (-537241997481391/2251799813685248)), (10328935/562949953421312), by norm_num⟩
  | 6 => ⟨((-540832073554603/18014398509481984), (-1409822987744623/18014398509481984)), (16633511/1125899906842624), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41591753/16777216), (-332492645/8388608)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-84861685/33554432), (-1356801955/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-330055655668759/4503599627370496), (-282876274916819/9007199254740992)), (256827389/18014398509481984), by norm_num⟩
  | 1 => ⟨((454894803/2147483648), (389870451/4294967296)), (89/2147483648), by norm_num⟩
  | 2 => ⟨((-328703773/1073741824), (-563435271/4294967296)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((1266768137/4294967296), (271422899/2147483648)), (253/4294967296), by norm_num⟩
  | 4 => ⟨((-57209857/268435456), (-392256541/4294967296)), (23/536870912), by norm_num⟩
  | 5 => ⟨((33071551/268435456), (453506891/8589934592)), (215/8589934592), by norm_num⟩
  | 6 => ⟨((-509808411/8589934592), (-436934503/17179869184)), (209/17179869184), by norm_num⟩
  | 7 => ⟨((210505119/8589934592), (360829471/34359738368)), (87/17179869184), by norm_num⟩
  | 8 => ⟨((-608438051/68719476736), (-65183207/17179869184)), (253/137438953472), by norm_num⟩
  | 9 => ⟨((195401351/68719476736), (41867489/34359738368)), (41/68719476736), by norm_num⟩
  | 10 => ⟨((-451826037/549755813888), (-387240345/1099511627776)), (191/1099511627776), by norm_num⟩
  | 11 => ⟨((237444585/1099511627776), (101751687/1099511627776)), (101/2199023255552), by norm_num⟩
  | 12 => ⟨((-457535415/8796093022208), (-392133603/17592186044416)), (197/17592186044416), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395170341040317/2535301200456458802993406410752), (-3564906068827/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889029621731719/316912650057057350374175801344), (-2107858373027/316912650057057350374175801344)), (11577/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888943316330013/39614081257132168796771975168), (-4741620537203/39614081257132168796771975168)), (104219/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944334024654333/1237940039285380274899124224), (-1259167473899/618970019642690137449562112)), (27691/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110645863342707/9671406556917033397649408), (-5035205505357/154742504910672534362390528)), (110799/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774374795465201/4835703278458516698824704), (-2359474808537/4835703278458516698824704)), (103911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157260601737233/75557863725914323419136), (-4127525786847/604462909807314587353088)), (90959/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943323646521857/37778931862957161709568), (-6704314422797/75557863725914323419136)), (73939/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648340023516889/2361183241434822606848), (-5025686093351/4722366482869645213696)), (110969/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620265064014801/590295810358705651712), (-431636045997/36893488147419103232)), (152681/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455498439464413/18446744073709551616), (-8626511359591/73786976294838206464)), (190999/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910494051624135/4611686018427387904), (-4848145926453/4611686018427387904)), (107539/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796116542906285/576460752303423488), (-9685632149715/1152921504606846976)), (215333/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596521567119893/72057594037927936), (-4231472851501/72057594037927936)), (188703/144115188075855872), by norm_num⟩
  | 4 => ⟨((372330772876563/9007199254740992), (-12670478052513/36028797018963968)), (141815/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486351102320543/9007199254740992), (-7898128253789/4503599627370496)), (355545/9007199254740992), by norm_num⟩
  | 2 => ⟨((555523539244139/1125899906842624), (-15733604620345/2251799813685248)), (89265/562949953421312), by norm_num⟩
  | 1 => ⟨((1103610996981225/1125899906842624), (-11722080711767/562949953421312)), (539389/1125899906842624), by norm_num⟩
  | 0 => ⟨((540643111064387/562949953421312), (-23132824069177/562949953421312)), (1094033/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((540643111064387/562949953421312), (-23132824069177/562949953421312)), (4173404697898482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2073078391560753/2251799813685248), (-177729503611559/2251799813685248)), (2191277/1125899906842624), by norm_num⟩
  | 2 => ⟨((947256993089531/1125899906842624), (-327246846047961/2251799813685248)), (273789/70368744177664), by norm_num⟩
  | 3 => ⟨((773179908004571/1125899906842624), (-550647284898929/2251799813685248)), (17288747/2251799813685248), by norm_num⟩
  | 4 => ⟨((14488523215903/35184372088832), (-756282888902719/2251799813685248)), (32200577/2251799813685248), by norm_num⟩
  | 5 => ⟨((255668795594011/4503599627370496), (-155714334847193/562949953421312)), (48149245/2251799813685248), by norm_num⟩
  | 6 => ⟨((-330055655668759/4503599627370496), (-282876274916819/9007199254740992)), (256827389/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84861685/33554432), (-1356801955/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-86449105/33554432), (-691091129/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1286186973552811/18014398509481984), (471736075532779/18014398509481984)), (243098819/18014398509481984), by norm_num⟩
  | 1 => ⟨((902914777/4294967296), (-331162951/4294967296)), (173/4294967296), by norm_num⟩
  | 2 => ⟨((-332322183/1073741824), (487544551/4294967296)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((326167463/1073741824), (-119628765/1073741824)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((-30011881/134217728), (352239599/4294967296)), (189/4294967296), by norm_num⟩
  | 5 => ⟨((1131112349/8589934592), (-207429601/4294967296)), (7/268435456), by norm_num⟩
  | 6 => ⟨((-1110163763/17179869184), (101793967/4294967296)), (111/8589934592), by norm_num⟩
  | 7 => ⟨((933945559/34359738368), (-171272071/17179869184)), (47/8589934592), by norm_num⟩
  | 8 => ⟨((-687486427/68719476736), (252150081/68719476736)), (279/137438953472), by norm_num⟩
  | 9 => ⟨((449835963/137438953472), (-5155837/4294967296)), (23/34359738368), by norm_num⟩
  | 10 => ⟨((-1059611635/1099511627776), (194317407/549755813888)), (109/549755813888), by norm_num⟩
  | 11 => ⟨((283632891/1099511627776), (-416113271/4398046511104)), (235/4398046511104), by norm_num⟩
  | 12 => ⟨((-1113519653/17592186044416), (51050839/2199023255552)), (233/17592186044416), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395154934790955/2535301200456458802993406410752), (908589829883/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888992998085851/316912650057057350374175801344), (4297513595157/633825300114114700748351602688)), (5789/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1888860911902349/39614081257132168796771975168), (604200228381/4951760157141521099596496896)), (104229/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236072561242943/309485009821345068724781056), (5134349916371/2475880078570760549798248448)), (110775/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885123124457677/77371252455336267181195264), (320801823659/9671406556917033397649408)), (55405/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387166873411827/2417851639229258349412352), (1202602990631/2417851639229258349412352)), (51961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629006486652671/302231454903657293676544), (2103747757339/302231454903657293676544)), (45485/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235816317736299/9444732965739290427392), (6834153110135/75557863725914323419136)), (18487/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296592474817479/4722366482869645213696), (5122967053959/4722366482869645213696)), (13873/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620144637956411/590295810358705651712), (1759944703047/147573952589676412928)), (1193/4611686018427387904), by norm_num⟩
  | 8 => ⟨((455460801026773/18446744073709551616), (4396637626797/36893488147419103232)), (191031/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455204675376687/2305843009213693952), (9883573288593/9223372036854775808)), (215117/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99503978039089/72057594037927936), (4936252029021/576460752303423488)), (107689/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192894837537501/144115188075855872), (4312999230115/72057594037927936)), (188749/144115188075855872), by norm_num⟩
  | 4 => ⟨((744550284951499/18014398509481984), (12914138253317/36028797018963968)), (70927/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486072820339985/9007199254740992), (16099226752033/9007199254740992)), (355663/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110768609481783/2251799813685248), (16034173619669/2251799813685248)), (357209/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103192853545901/1125899906842624), (23889033758953/1125899906842624)), (539685/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080448340221877/1125899906842624), (47131600029057/1125899906842624)), (1094931/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080448340221877/1125899906842624), (47131600029057/1125899906842624)), (4176830296043014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034858623831267/1125899906842624), (11307234931345/140737488355328)), (1096565/562949953421312), by norm_num⟩
  | 2 => ⟨((1887822775194109/2251799813685248), (10392921705805/70368744177664)), (8767975/2251799813685248), by norm_num⟩
  | 3 => ⟨((1533559813023101/2251799813685248), (278816888468155/1125899906842624)), (17291395/2251799813685248), by norm_num⟩
  | 4 => ⟨((906319584243673/2251799813685248), (759538876854483/2251799813685248)), (16058113/1125899906842624), by norm_num⟩
  | 5 => ⟨((108586865423923/2251799813685248), (1222817330215629/4503599627370496)), (95037023/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1286186973552811/18014398509481984), (471736075532779/18014398509481984)), (243098819/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-86449105/33554432), (-691091129/16777216)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-87955083/33554432), (-1406260421/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-314947482494187/9007199254740992), (1148440376806919/18014398509481984)), (58974393/9007199254740992), by norm_num⟩
  | 1 => ⟨((224947533/2147483648), (-102532503/536870912)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((-673882585/4294967296), (1228639713/4294967296)), (131/4294967296), by norm_num⟩
  | 3 => ⟨((21028873/134217728), (-153361485/536870912)), (133/4294967296), by norm_num⟩
  | 4 => ⟨((-125993747/1073741824), (229714975/1073741824)), (51/2147483648), by norm_num⟩
  | 5 => ⟨((603909655/8589934592), (-1101063303/8589934592)), (31/2147483648), by norm_num⟩
  | 6 => ⟨((-150762637/4294967296), (1099496957/17179869184)), (63/8589934592), by norm_num⟩
  | 7 => ⟨((129041285/8589934592), (-941085291/34359738368)), (55/17179869184), by norm_num⟩
  | 8 => ⟨((-193286571/34359738368), (704809895/68719476736)), (21/17179869184), by norm_num⟩
  | 9 => ⟨((514697617/274877906944), (-469204833/137438953472)), (57/137438953472), by norm_num⟩
  | 10 => ⟨((-616758505/1099511627776), (1124489649/1099511627776)), (69/549755813888), by norm_num⟩
  | 11 => ⟨((83983789/549755813888), (-1224970885/4398046511104)), (19/549755813888), by norm_num⟩
  | 12 => ⟨((-335457263/8796093022208), (76451767/1099511627776)), (77/8796093022208), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (2699624508691/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888960653169747/316912650057057350374175801344), (797995736353/158456325028528675187087900672)), (23129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888788397889141/39614081257132168796771975168), (224384937675/2475880078570760549798248448)), (26025/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944251895567175/1237940039285380274899124224), (476690416863/309485009821345068724781056)), (55315/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770169940480381/154742504910672534362390528), (1906187772707/77371252455336267181195264)), (1729/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774298184475097/4835703278458516698824704), (893220733935/2417851639229258349412352)), (12971/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257951153305251/604462909807314587353088), (1562526933633/302231454903657293676544)), (45413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886430860101237/75557863725914323419136), (2537964198241/37778931862957161709568)), (36911/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324129597869535/1180591620717411303424), (3804948603995/4722366482869645213696)), (27695/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620043873723765/590295810358705651712), (5228559816763/590295810358705651712)), (76197/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910859448457531/36893488147419103232), (6377769571/72057594037927936)), (95303/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910340559045333/4611686018427387904), (7340507855131/9223372036854775808)), (107293/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795964443496471/576460752303423488), (3666080947861/576460752303423488)), (53695/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192780087464977/144115188075855872), (6406262628745/144115188075855872)), (94075/144115188075855872), by norm_num⟩
  | 4 => ⟨((744467378579821/18014398509481984), (9590661300693/36028797018963968)), (141329/36028797018963968), by norm_num⟩
  | 3 => ⟨((371469138838551/2251799813685248), (11955601641133/9007199254740992)), (44261/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221177509453951/4503599627370496), (23813256635429/4503599627370496)), (177617/2251799813685248), by norm_num⟩
  | 1 => ⟨((551481889391225/562949953421312), (17737908141377/1125899906842624)), (267865/1125899906842624), by norm_num⟩
  | 0 => ⟨((540075559200951/562949953421312), (8747517065131/281474976710656)), (541513/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((540075559200951/562949953421312), (8747517065131/281474976710656)), (2065708164695357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2070347686547797/2251799813685248), (134273255144151/2251799813685248)), (2145355/2251799813685248), by norm_num⟩
  | 2 => ⟨((1895510520165371/2251799813685248), (61726695566685/562949953421312)), (2100407/1125899906842624), by norm_num⟩
  | 3 => ⟨((1568521833718375/2251799813685248), (415680293108155/2251799813685248)), (7993515/2251799813685248), by norm_num⟩
  | 4 => ⟨((126980128454955/281474976710656), (289547770465235/1125899906842624)), (1760897/281474976710656), by norm_num⟩
  | 5 => ⟨((4833504068591/35184372088832), (1044975678255507/4503599627370496)), (39911457/4503599627370496), by norm_num⟩
  | 6 => ⟨((-314947482494187/9007199254740992), (1148440376806919/18014398509481984)), (58974393/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-1406260421/33554432)), (1/33554432), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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
  | _ => zero

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5586723/2097152), (-1429163561/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((225801612572211/18014398509481984), (1234619960155079/18014398509481984)), (23999325/2251799813685248), by norm_num⟩
  | 1 => ⟨((-327805555/8589934592), (-1792348943/8589934592)), (281/8589934592), by norm_num⟩
  | 2 => ⟨((124751421/2147483648), (341052911/1073741824)), (27/536870912), by norm_num⟩
  | 3 => ⟨((-253205667/4294967296), (-692228827/2147483648)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((24090323/536870912), (526876549/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((-234699293/8589934592), (-320817495/2147483648)), (209/8589934592), by norm_num⟩
  | 6 => ⟨((238182421/17179869184), (1302314749/17179869184)), (107/8589934592), by norm_num⟩
  | 7 => ⟨((-207186207/34359738368), (-141604517/4294967296)), (47/8589934592), by norm_num⟩
  | 8 => ⟨((39423941/17179869184), (1724472517/137438953472)), (9/4294967296), by norm_num⟩
  | 9 => ⟨((-213381463/274877906944), (-291677515/68719476736)), (197/274877906944), by norm_num⟩
  | 10 => ⟨((259857861/1099511627776), (1420829983/1099511627776)), (121/549755813888), by norm_num⟩
  | 11 => ⟨((-71922099/1099511627776), (-1572999551/4398046511104)), (135/2199023255552), by norm_num⟩
  | 12 => ⟨((145978963/8796093022208), (1596344143/17592186044416)), (69/4398046511104), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790252832762771/5070602400912917605986812821504), (905252546125/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888929281229455/316912650057057350374175801344), (535138666093/158456325028528675187087900672)), (92411/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472179498241593/9903520314283042199192993792), (2407568663565/39614081257132168796771975168)), (103977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472107306861485/618970019642690137449562112), (1278673319911/1237940039285380274899124224)), (110491/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770095648245159/154742504910672534362390528), (2556565039777/154742504910672534362390528)), (27627/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774263504089815/4835703278458516698824704), (1197974791249/4835703278458516698824704)), (103621/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257890750584413/604462909807314587353088), (65488315271/18889465931478580854784)), (90687/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886333245068945/75557863725914323419136), (850959315521/18889465931478580854784)), (147401/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296445651646179/4722366482869645213696), (79734935663/147573952589676412928)), (55291/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619944621568363/590295810358705651712), (3506128538139/590295810358705651712)), (38025/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821595977677569/73786976294838206464), (4379350135493/73786976294838206464)), (23775/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820544406857613/9223372036854775808), (1230555206541/2305843009213693952)), (107039/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397948534432405/288230376151711744), (2458270797175/576460752303423488)), (214209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596332191677587/72057594037927936), (4295592813459/144115188075855872)), (187579/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488765589711779/36028797018963968), (803830896007/4503599627370496)), (281661/36028797018963968), by norm_num⟩
  | 3 => ⟨((742836372127143/4503599627370496), (8016055551661/9007199254740992)), (352589/9007199254740992), by norm_num⟩
  | 2 => ⟨((277599088008603/562949953421312), (15965531274409/4503599627370496)), (706721/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102703472901405/1125899906842624), (11891238610681/1125899906842624)), (1063955/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159484737234941/2251799813685248), (46905442955931/2251799813685248)), (8373/8796093022208), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2159484737234941/2251799813685248), (46905442955931/2251799813685248)), (31940460238632557/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((2069977171791035/2251799813685248), (89965002697825/2251799813685248)), (2100263/1125899906842624), by norm_num⟩
  | 2 => ⟨((118702597474307/140737488355328), (82700735968107/1125899906842624)), (8058349/2251799813685248), by norm_num⟩
  | 3 => ⟨((1589733169438581/2251799813685248), (279010014664071/2251799813685248)), (14777171/2251799813685248), by norm_num⟩
  | 4 => ⟨((135969289257209/281474976710656), (393952848047457/2251799813685248)), (24526815/2251799813685248), by norm_num⟩
  | 5 => ⟨((913056831267743/4503599627370496), (761211378373133/4503599627370496)), (8069447/562949953421312), by norm_num⟩
  | 6 => ⟨((225801612572211/18014398509481984), (1234619960155079/18014398509481984)), (23999325/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5586723/2097152), (-1429163561/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log22 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-45376701/16777216), (-725500523/16777216)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((890615009813139/18014398509481984), (811736407391903/18014398509481984)), (67307939/9007199254740992), by norm_num⟩
  | 1 => ⟨((-328174687/2147483648), (-598218845/4294967296)), (101/4294967296), by norm_num⟩
  | 2 => ⟨((507200945/2147483648), (924559923/4294967296)), (79/2147483648), by norm_num⟩
  | 3 => ⟨((-261296609/1073741824), (-952617991/4294967296)), (165/4294967296), by norm_num⟩
  | 4 => ⟨((807678911/4294967296), (736145663/4294967296)), (129/4294967296), by norm_num⟩
  | 5 => ⟨((-998627921/8589934592), (-455091499/4294967296)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((514466883/8589934592), (468902381/8589934592)), (169/17179869184), by norm_num⟩
  | 7 => ⟨((-454353993/17179869184), (-103528369/4294967296)), (151/34359738368), by norm_num⟩
  | 8 => ⟨((702213741/68719476736), (640021167/68719476736)), (119/68719476736), by norm_num⟩
  | 9 => ⟨((-482349441/137438953472), (-879258933/274877906944)), (83/137438953472), by norm_num⟩
  | 10 => ⟨((37274065/34359738368), (271782669/274877906944)), (13/68719476736), by norm_num⟩
  | 11 => ⟨((-83793249/274877906944), (-610975831/2199023255552)), (119/2199023255552), by norm_num⟩
  | 12 => ⟨((690689307/8796093022208), (629517411/8796093022208)), (125/8796093022208), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (481377655613/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888898819191049/316912650057057350374175801344), (569093067755/316912650057057350374175801344)), (92313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236081195768481/4951760157141521099596496896), (40005037127/1237940039285380274899124224)), (103859/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888356673622595/2475880078570760549798248448), (339949047795/618970019642690137449562112)), (110359/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885011631310241/77371252455336267181195264), (1359374451407/154742504910672534362390528)), (3449/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548459325232453/9671406556917033397649408), (1273965630263/9671406556917033397649408)), (103481/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257831706429421/604462909807314587353088), (278568052949/151115727451828646838272)), (90555/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943118816269283/37778931862957161709568), (452463327703/18889465931478580854784)), (147171/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296374234369347/4722366482869645213696), (1356656260341/4722366482869645213696)), (55197/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809923448452253/295147905179352825856), (466052716711/147573952589676412928)), (151819/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455368632982063/18446744073709551616), (2328477760441/73786976294838206464)), (94907/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820408755034573/9223372036854775808), (654271067187/2305843009213693952)), (53399/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591659701642905/1152921504606846976), (326752649135/144115188075855872)), (106833/576460752303423488), by norm_num⟩
  | 5 => ⟨((596274057977621/72057594037927936), (2283827306731/144115188075855872)), (46759/36028797018963968), by norm_num⟩
  | 4 => ⟨((93037119260223/2251799813685248), (3418870275757/36028797018963968)), (140355/18014398509481984), by norm_num⟩
  | 3 => ⟨((742731440892199/4503599627370496), (4261590627597/9007199254740992)), (351163/9007199254740992), by norm_num⟩
  | 2 => ⟨((555096779694047/1125899906842624), (8487295290279/4503599627370496)), (703155/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204833642488205/2251799813685248), (6320798433771/1125899906842624)), (1056819/2251799813685248), by norm_num⟩
  | 0 => ⟨((539619197783917/562949953421312), (6232003522381/562949953421312)), (530513/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539619197783917/562949953421312), (6232003522381/562949953421312)), (2023746492625999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2068745464704983/2251799813685248), (47789807543577/2251799813685248)), (4115197/2251799813685248), by norm_num⟩
  | 2 => ⟨((1899557814170009/2251799813685248), (87809712936337/2251799813685248)), (7735999/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598991758417325/2251799813685248), (148147828554319/2251799813685248)), (13655099/2251799813685248), by norm_num⟩
  | 4 => ⟨((1125689259309745/2251799813685248), (210398060650067/2251799813685248)), (21189597/2251799813685248), by norm_num⟩
  | 5 => ⟨((271540337903889/1125899906842624), (105179348365683/1125899906842624)), (50290709/4503599627370496), by norm_num⟩
  | 6 => ⟨((890615009813139/18014398509481984), (811736407391903/18014398509481984)), (67307939/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-725500523/16777216)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5753657/2097152), (-5749483/131072)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((575555460398065/9007199254740992), (135558148332771/18014398509481984)), (80746197/18014398509481984), by norm_num⟩
  | 1 => ⟨((-860524567/4294967296), (-202675719/8589934592)), (123/8589934592), by norm_num⟩
  | 2 => ⟨((1349084901/4294967296), (19859017/536870912)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((-44062999/134217728), (-83023777/2147483648)), (105/4294967296), by norm_num⟩
  | 4 => ⟨((276318557/1073741824), (65080143/2147483648)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((-1386232379/8589934592), (-81623365/4294967296)), (27/2147483648), by norm_num⟩
  | 6 => ⟨((724420601/8589934592), (85309863/8589934592)), (115/17179869184), by norm_num⟩
  | 7 => ⟨((-1297952345/34359738368), (-76425309/17179869184)), (105/34359738368), by norm_num⟩
  | 8 => ⟨((1017430517/68719476736), (119815557/68719476736)), (21/17179869184), by norm_num⟩
  | 9 => ⟨((-708921667/137438953472), (-166969327/274877906944)), (119/274877906944), by norm_num⟩
  | 10 => ⟨((1778255829/1099511627776), (3272071/17179869184)), (151/1099511627776), by norm_num⟩
  | 11 => ⟨((-253441403/549755813888), (-119383967/2199023255552)), (11/274877906944), by norm_num⟩
  | 12 => ⟨((1059552071/8796093022208), (124775913/8796093022208)), (47/4398046511104), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790200988601433/5070602400912917605986812821504), (152696035801/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888869210049989/316912650057057350374175801344), (45127079795/158456325028528675187087900672)), (46109/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944291499162615/19807040628566084398385987584), (101512003231/19807040628566084398385987584)), (103747/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944143007410619/1237940039285380274899124224), (53913169605/618970019642690137449562112)), (13779/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884976340968907/77371252455336267181195264), (215584845625/154742504910672534362390528)), (55117/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387098309696163/2417851639229258349412352), (101019375305/4835703278458516698824704)), (51673/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628886981831723/302231454903657293676544), (44177974649/151115727451828646838272)), (45215/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886143955795191/75557863725914323419136), (287021892023/75557863725914323419136)), (146951/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648152056257985/2361183241434822606848), (215148415833/4722366482869645213696)), (13777/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809875349805847/295147905179352825856), (295637451707/590295810358705651712)), (37/144115188075855872), by norm_num⟩
  | 8 => ⟨((1821354615234707/73786976294838206464), (369259620795/73786976294838206464)), (94723/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910137150824869/4611686018427387904), (415022565417/9223372036854775808)), (13321/576460752303423488), by norm_num⟩
  | 6 => ⟨((795762906628519/576460752303423488), (207265002573/576460752303423488)), (53287/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192431597703815/144115188075855872), (362160413385/144115188075855872)), (93259/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488420395123033/36028797018963968), (135533976937/9007199254740992)), (69951/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485248194464923/9007199254740992), (168935265495/2251799813685248)), (87451/2251799813685248), by norm_num⟩
  | 2 => ⟨((554991080440649/1125899906842624), (1345713309345/4503599627370496)), (174939/1125899906842624), by norm_num⟩
  | 1 => ⟨((275526971428183/281474976710656), (1002104763103/1125899906842624)), (525009/1125899906842624), by norm_num⟩
  | 0 => ⟨((2157305633255629/2251799813685248), (987836347469/562949953421312)), (2101639/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157305633255629/2251799813685248), (987836347469/562949953421312)), (8017116555220793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033384929215693/1125899906842624), (3785531740749/1125899906842624)), (4034269/2251799813685248), by norm_num⟩
  | 2 => ⟨((1896918323182395/2251799813685248), (13897901318521/2251799813685248)), (7432677/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597880038579213/2251799813685248), (5853802701435/562949953421312)), (12614337/2251799813685248), by norm_num⟩
  | 4 => ⟨((566807122480213/1125899906842624), (33230927294895/2251799813685248)), (18164639/2251799813685248), by norm_num⟩
  | 5 => ⟨((1140400628905807/4503599627370496), (33458615926507/2251799813685248)), (37650455/4503599627370496), by norm_num⟩
  | 6 => ⟨((575555460398065/9007199254740992), (135558148332771/18014398509481984)), (80746197/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5753657/2097152), (-5749483/131072)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-93308067/33554432), (-372961509/8388608)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((495720408255275/9007199254740992), (-32116420516869/1125899906842624)), (104831517/18014398509481984), by norm_num⟩
  | 1 => ⟨((-187805431/1073741824), (389357427/4294967296)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((1193711539/4294967296), (-618699431/4294967296)), (33/1073741824), by norm_num⟩
  | 3 => ⟨((-1264559843/4294967296), (5120469/33554432)), (71/2147483648), by norm_num⟩
  | 4 => ⟨((1004709813/4294967296), (-130185009/1073741824)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((-319302187/2147483648), (330987973/4294967296)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((676506359/8589934592), (-701265063/17179869184)), (5/536870912), by norm_num⟩
  | 7 => ⟨((-1228556357/34359738368), (636759463/34359738368)), (147/34359738368), by norm_num⟩
  | 8 => ⟨((976104559/68719476736), (-505913963/68719476736)), (119/68719476736), by norm_num⟩
  | 9 => ⟨((-689358407/137438953472), (357293735/137438953472)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((438163625/274877906944), (-454199489/549755813888)), (55/274877906944), by norm_num⟩
  | 11 => ⟨((-506366395/1099511627776), (524898337/2199023255552)), (129/2199023255552), by norm_num⟩
  | 12 => ⟨((536419887/4398046511104), (-556051723/8796093022208)), (139/8796093022208), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580353468412699/10141204801825835211973625643008), (-622882015069/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888840402111059/316912650057057350374175801344), (-736289368485/633825300114114700748351602688)), (92273/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888518180902317/39614081257132168796771975168), (-12939496019/618970019642690137449562112)), (25953/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888217145579849/2475880078570760549798248448), (-879636302615/2475880078570760549798248448)), (55153/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884941905946301/77371252455336267181195264), (-879355849757/154742504910672534362390528)), (13789/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774164336136917/4835703278458516698824704), (-824098253307/9671406556917033397649408)), (101/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1257717467135035/604462909807314587353088), (-720788256873/604462909807314587353088)), (90503/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((7367391200793/295147905179352825856), (-146340375229/9444732965739290427392)), (147079/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648117627452709/2361183241434822606848), (-438777187327/2361183241434822606848)), (6895/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619656018305591/590295810358705651712), (-1205845026491/590295810358705651712)), (151707/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227654532568477/9223372036854775808), (-753059453053/36893488147419103232)), (47415/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910070574281105/4611686018427387904), (-846376359291/4611686018427387904)), (213403/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795696327645175/576460752303423488), (-1690716291395/1152921504606846976)), (213449/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192315079270685/144115188075855872), (-369272262829/36028797018963968)), (186819/144115188075855872), by norm_num⟩
  | 4 => ⟨((372061401934647/9007199254740992), (-1105533174667/18014398509481984)), (280331/36028797018963968), by norm_num⟩
  | 3 => ⟨((371257423686189/2251799813685248), (-1377929328897/4503599627370496)), (175297/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219527282009013/4503599627370496), (-1371966945871/1125899906842624)), (175433/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203560132425511/2251799813685248), (-4086216816007/1125899906842624)), (1053971/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155994165215207/2251799813685248), (-16108923601561/2251799813685248)), (2113507/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155994165215207/2251799813685248), (-16108923601561/2251799813685248)), (8062389382369231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064149448265347/2251799813685248), (-30847098469223/2251799813685248)), (4077411/2251799813685248), by norm_num⟩
  | 2 => ⟨((945857037424373/1125899906842624), (-3534562713949/140737488355328)), (7586965/2251799813685248), by norm_num⟩
  | 3 => ⟨((793894705260959/1125899906842624), (-95019203661379/2251799813685248)), (1641069/281474976710656), by norm_num⟩
  | 4 => ⟨((278893193328533/562949953421312), (-133999909275107/2251799813685248)), (19622385/2251799813685248), by norm_num⟩
  | 5 => ⟨((544696126813647/2251799813685248), (-132770816930859/2251799813685248)), (21777777/2251799813685248), by norm_num⟩
  | 6 => ⟨((495720408255275/9007199254740992), (-32116420516869/1125899906842624)), (104831517/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-93308067/33554432), (-372961509/8388608)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47253303/16777216), (-377752187/8388608)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((536818601723945/18014398509481984), (-934269061115265/18014398509481984)), (143000895/18014398509481984), by norm_num⟩
  | 1 => ⟨((-411975961/4294967296), (358497631/2147483648)), (111/4294967296), by norm_num⟩
  | 2 => ⟨((663049731/4294967296), (-576979679/2147483648)), (181/4294967296), by norm_num⟩
  | 3 => ⟨((-711424917/4294967296), (1238150627/4294967296)), (49/1073741824), by norm_num⟩
  | 4 => ⟨((572497117/4294967296), (-62272705/268435456)), (5/134217728), by norm_num⟩
  | 5 => ⟨((-184279713/2147483648), (641433935/4294967296)), (13/536870912), by norm_num⟩
  | 6 => ⟨((395449009/8589934592), (-344116031/4294967296)), (113/8589934592), by norm_num⟩
  | 7 => ⟨((-363686073/17179869184), (316476221/8589934592)), (105/17179869184), by norm_num⟩
  | 8 => ⟨((292665077/34359738368), (-1018697657/68719476736)), (171/68719476736), by norm_num⟩
  | 9 => ⟨((-209345009/68719476736), (91085035/17179869184)), (31/34359738368), by norm_num⟩
  | 10 => ⟨((539084471/549755813888), (-938212535/549755813888)), (161/549755813888), by norm_num⟩
  | 11 => ⟨((-630998535/2199023255552), (549089027/1099511627776)), (95/1099511627776), by norm_num⟩
  | 12 => ⟨((338517655/4398046511104), (-1178299597/8796093022208)), (103/4398046511104), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940107137/10141204801825835211973625643008), (-341698707093/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888812348264765/316912650057057350374175801344), (-1615550108755/633825300114114700748351602688)), (11545/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888455014434191/39614081257132168796771975168), (-454263383979/9903520314283042199192993792)), (103915/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472037492174621/618970019642690137449562112), (-1930064949895/2475880078570760549798248448)), (55211/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221227070599389/19342813113834066795298816), (-1929441537147/154742504910672534362390528)), (110435/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548265553589631/9671406556917033397649408), (-904094668489/4835703278458516698824704)), (103547/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257662163839795/604462909807314587353088), (-1581503871829/604462909807314587353088)), (45309/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885962140138737/75557863725914323419136), (-2568703570483/75557863725914323419136)), (9205/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648083813825761/2361183241434822606848), (-1925443133959/4722366482869645213696)), (27621/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809781416614953/295147905179352825856), (-661430785675/147573952589676412928)), (151953/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455279870845569/18446744073709551616), (-3304514307379/73786976294838206464)), (94999/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227501171055079/1152921504606846976), (-464244071641/1152921504606846976)), (106913/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397815092329641/288230376151711744), (-3709425223803/1152921504606846976)), (213925/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192198761902435/144115188075855872), (-405082614427/18014398509481984)), (187295/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488070002234881/36028797018963968), (-4850836818085/36028797018963968)), (70291/9007199254740992), by norm_num⟩
  | 3 => ⟨((371202055542641/2251799813685248), (-3022907715653/4503599627370496)), (351845/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219078482996249/4503599627370496), (-12038598256937/4503599627370496)), (176215/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101436224893535/1125899906842624), (-1120366961245/140737488355328)), (530117/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154561760927023/2251799813685248), (-4415869897755/281474976710656)), (1066161/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154561760927023/2251799813685248), (-4415869897755/281474976710656)), (4067081455710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060968457053349/2251799813685248), (-16900728679537/562949953421312)), (4147393/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884279766391149/2251799813685248), (-61873828211643/1125899906842624)), (1960215/562949953421312), by norm_num⟩
  | 3 => ⟨((1569942733841513/2251799813685248), (-103550592605793/1125899906842624)), (6992035/1125899906842624), by norm_num⟩
  | 4 => ⟨((1075508254289357/2251799813685248), (-144389833819545/1125899906842624)), (22071507/2251799813685248), by norm_num⟩
  | 5 => ⟨((476651744120281/2251799813685248), (-137927410034057/1125899906842624)), (6686183/562949953421312), by norm_num⟩
  | 6 => ⟨((536818601723945/18014398509481984), (-934269061115265/18014398509481984)), (143000895/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/16777216), (-377752187/8388608)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-95658131/33554432), (-1529419785/33554432)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-14141409006275/9007199254740992), (-2081554521565843/36028797018963968)), (170892411/18014398509481984), by norm_num⟩
  | 1 => ⟨((43939663/8589934592), (404233073/2147483648)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((-8947479/1073741824), (-164628797/536870912)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((4858625/536870912), (715168685/2147483648)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((-31659739/4294967296), (-1165044309/4294967296)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((20630097/4294967296), (379582683/2147483648)), (65/2147483648), by norm_num⟩
  | 6 => ⟨((-22404949/8589934592), (-824478017/8589934592)), (71/4294967296), by norm_num⟩
  | 7 => ⟨((20856425/17179869184), (1534987985/34359738368)), (133/17179869184), by norm_num⟩
  | 8 => ⟨((-33976123/68719476736), (-156285595/8589934592)), (109/34359738368), by norm_num⟩
  | 9 => ⟨((12299721/68719476736), (1810465977/274877906944)), (159/137438953472), by norm_num⟩
  | 10 => ⟨((-32058943/549755813888), (-1179734587/549755813888)), (209/549755813888), by norm_num⟩
  | 11 => ⟨((18991115/1099511627776), (698852577/1099511627776)), (125/1099511627776), by norm_num⟩
  | 12 => ⟨((-10312481/2199023255552), (-1517952775/8796093022208)), (273/8796093022208), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580262236925127/10141204801825835211973625643008), (-260190872185/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444392502797879/158456325028528675187087900672), (-1230111634251/316912650057057350374175801344)), (92443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888393407955671/39614081257132168796771975168), (-2767070132281/39614081257132168796771975168)), (52007/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944042197391549/1237940039285380274899124224), (-2939157112153/2475880078570760549798248448)), (110533/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769750859405149/154742504910672534362390528), (-734548950029/38685626227668133590597632)), (55277/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548203815227691/9671406556917033397649408), (-2753537567483/9671406556917033397649408)), (103665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628804001681965/302231454903657293676544), (-2408324825253/604462909807314587353088)), (90729/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471468467072769/18889465931478580854784), (-3911615270075/75557863725914323419136)), (147475/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324025298910801/1180591620717411303424), (-2932038905827/4722366482869645213696)), (55321/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619471119113987/590295810358705651712), (-4028837392677/590295810358705651712)), (76095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910502143310057/36893488147419103232), (-2515987854679/36893488147419103232)), (47581/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819879011858711/9223372036854775808), (-5655380075415/9223372036854775808)), (107117/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795564532491009/576460752303423488), (-5648396927759/1152921504606846976)), (214383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192082807850513/144115188075855872), (-308406356811/9007199254740992)), (187753/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487893954288255/36028797018963968), (-7386087421149/36028797018963968)), (140983/18014398509481984), by norm_num⟩
  | 3 => ⟨((185573059639447/1125899906842624), (-9205253830715/9007199254740992)), (44131/1125899906842624), by norm_num⟩
  | 2 => ⟨((69331875463749/140737488355328), (-4582168773129/1125899906842624)), (22121/140737488355328), by norm_num⟩
  | 1 => ⟨((275269696477031/281474976710656), (-13644623702697/1125899906842624)), (133283/281474976710656), by norm_num⟩
  | 0 => ⟨((2153024908459043/2251799813685248), (-26884157519749/1125899906842624)), (1075227/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153024908459043/2251799813685248), (-26884157519749/1125899906842624)), (4101665501121139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((128581179724221/140737488355328), (-102819549821753/2251799813685248)), (4214947/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874903256501611/2251799813685248), (-46969216124617/562949953421312)), (4043337/1125899906842624), by norm_num⟩
  | 3 => ⟨((772707343671757/1125899906842624), (-312861687729695/2251799813685248)), (3703933/562949953421312), by norm_num⟩
  | 4 => ⟨((508576318882343/1125899906842624), (-429435196136075/2251799813685248)), (24453085/2251799813685248), by norm_num⟩
  | 5 => ⟨((755115881673189/4503599627370496), (-387957348467797/2251799813685248)), (62836023/4503599627370496), by norm_num⟩
  | 6 => ⟨((-14141409006275/9007199254740992), (-2081554521565843/36028797018963968)), (170892411/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95658131/33554432), (-1529419785/33554432)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 12 := fun k =>
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
  | _ => zero

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 12 := fun k =>
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6047887/2097152), (-1547135897/33554432)), (1/16777216), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-33183710389867/1125899906842624), (-214015057222451/4503599627370496)), (91618595/9007199254740992), by norm_num⟩
  | 1 => ⟨((417206177/4294967296), (672682491/4294967296)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((-687521749/4294967296), (-277131469/1073741824)), (241/4294967296), by norm_num⟩
  | 3 => ⟨((377659921/2147483648), (608920075/2147483648)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-622352745/4294967296), (-125431327/536870912)), (111/2147483648), by norm_num⟩
  | 5 => ⟨((1602479/16777216), (1322883813/8589934592)), (295/8589934592), by norm_num⟩
  | 6 => ⟨((-450688799/8589934592), (-726668207/8589934592)), (41/2147483648), by norm_num⟩
  | 7 => ⟨((212199537/8589934592), (342139981/8589934592)), (39/4294967296), by norm_num⟩
  | 8 => ⟨((-699375057/68719476736), (-1127637563/68719476736)), (259/68719476736), by norm_num⟩
  | 9 => ⟨((512228021/137438953472), (825890989/137438953472)), (191/137438953472), by norm_num⟩
  | 10 => ⟨((-337643999/274877906944), (-272200197/137438953472)), (127/274877906944), by norm_num⟩
  | 11 => ⟨((809323301/2199023255552), (652456323/1099511627776)), (307/2199023255552), by norm_num⟩
  | 12 => ⟨((-222283131/2199023255552), (-358398267/2199023255552)), (85/2199023255552), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395054805263161/2535301200456458802993406410752), (-692320386441/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888758334817305/316912650057057350374175801344), (-1636461881993/316912650057057350374175801344)), (92523/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472083319468729/9903520314283042199192993792), (-1840559155579/19807040628566084398385987584)), (104109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888020341274787/2475880078570760549798248448), (-3910037167783/2475880078570760549798248448)), (6915/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769686620192637/154742504910672534362390528), (-977185694411/38685626227668133590597632)), (110667/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548143393842161/9671406556917033397649408), (-3663071562463/9671406556917033397649408)), (103779/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257554937738239/604462909807314587353088), (-3203813385571/604462909807314587353088)), (22709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885787267883643/75557863725914323419136), (-2601810628465/37778931862957161709568)), (73831/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648017961557055/2361183241434822606848), (-3900463574059/4722366482869645213696)), (55397/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619380846609529/590295810358705651712), (-1339869886005/147573952589676412928)), (152417/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820890663285907/73786976294838206464), (-3346933261475/36893488147419103232)), (190637/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819750111762513/9223372036854775808), (-7523067172449/9223372036854775808)), (214625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590998826132243/1152921504606846976), (-7513660830981/1152921504606846976)), (214823/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595983673817795/72057594037927936), (-3281942066437/72057594037927936)), (94097/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487717773687497/36028797018963968), (-2456180145137/9007199254740992)), (282739/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484359045674143/9007199254740992), (-12244039091953/9007199254740992)), (11069/281474976710656), by norm_num⟩
  | 2 => ⟨((2218153643707239/4503599627370496), (-24377785665381/4503599627370496)), (355387/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100709811864537/1125899906842624), (-36291968679189/2251799813685248)), (67005/140737488355328), by norm_num⟩
  | 0 => ⟨((2151397709078047/2251799813685248), (-71491212050491/2251799813685248)), (2167953/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2151397709078047/2251799813685248), (-71491212050491/2251799813685248)), (8270084389693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1026601272707999/1125899906842624), (-68303598254999/1125899906842624)), (2140119/1125899906842624), by norm_num⟩
  | 2 => ⟨((931916580873973/1125899906842624), (-249118275871459/2251799813685248)), (8324815/2251799813685248), by norm_num⟩
  | 3 => ⟨((1515149845347253/2251799813685248), (-206197238735361/1125899906842624)), (15622997/2251799813685248), by norm_num⟩
  | 4 => ⟨((471980199103207/1125899906842624), (-554968896404007/2251799813685248)), (26746623/2251799813685248), by norm_num⟩
  | 5 => ⟨((129467715971583/1125899906842624), (-465288838961531/2251799813685248)), (71216451/4503599627370496), by norm_num⟩
  | 6 => ⟨((-33183710389867/1125899906842624), (-214015057222451/4503599627370496)), (91618595/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6047887/2097152), (-1547135897/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((509842359/1073741824), (314852387/2147483648)), (51/2147483648), by norm_num⟩
  | 1 => ⟨((1563461297/4294967296), (-54559761/536870912)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((-541854395/4294967296), (75635889/2147483648)), (51/8589934592), by norm_num⟩
  | 3 => ⟨((500779795/17179869184), (-279609617/34359738368)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((-347114103/68719476736), (387621235/274877906944)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((384961859/549755813888), (-214942853/1099511627776)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((-355780303/4398046511104), (397298753/17592186044416)), (19/4398046511104), by norm_num⟩
  | 7 => ⟨((563675689/70368744177664), (-314727441/140737488355328)), (31/70368744177664), by norm_num⟩
  | 8 => ⟨((-781420429/1125899906842624), (436304877/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 9 => ⟨((962914431/18014398509481984), (-268820885/18014398509481984)), (7/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1067906277/288230376151711744), (149065951/144115188075855872)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((538339073/2305843009213693952), (-150290391/2305843009213693952)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-995061895/73786976294838206464), (277795629/73786976294838206464)), (1/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial2 : Sound J_initial2 F_initial2 c := by
  apply sound_round (sound_add (A_q0 hcre) (A_term2 hcre) S_q0 S_term2)
  intro k
  fin_cases k <;> norm_num [J_initial2, J_q0, J_term2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((490196683/4294967296), (84233071/4294967296)), (61/1073741824), by norm_num⟩
  | 1 => ⟨((204087595/268435456), (40695957/1073741824)), (29/536870912), by norm_num⟩
  | 2 => ⟨((-738370309/2147483648), (-177906475/4294967296)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((467554113/4294967296), (171190445/8589934592)), (5/536870912), by norm_num⟩
  | 4 => ⟨((-462898511/17179869184), (-216414913/34359738368)), (85/34359738368), by norm_num⟩
  | 5 => ⟨((757376525/137438953472), (411843109/274877906944)), (73/137438953472), by norm_num⟩
  | 6 => ⟨((-528694005/549755813888), (-79040643/274877906944)), (107/1099511627776), by norm_num⟩
  | 7 => ⟨((1286394671/8796093022208), (51058323/1099511627776)), (67/4398046511104), by norm_num⟩
  | 8 => ⟨((-1384680141/70368744177664), (-28545131/4398046511104)), (37/17592186044416), by norm_num⟩
  | 9 => ⟨((166824911/70368744177664), (225461703/281474976710656)), (73/281474976710656), by norm_num⟩
  | 10 => ⟨((-581602519/2251799813685248), (-199518467/2251799813685248)), (65/2251799813685248), by norm_num⟩
  | 11 => ⟨((7222419/281474976710656), (160100241/18014398509481984)), (105/36028797018963968), by norm_num⟩
  | 12 => ⟨((-337407703/144115188075855872), (-117576111/144115188075855872)), (39/144115188075855872), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial3 : Sound J_initial3 F_initial3 c := by
  apply sound_round (sound_add (A_initial2 hcre) (A_term3 hcre) S_initial2 S_term3)
  intro k
  fin_cases k <;> norm_num [J_initial3, J_initial2, J_term3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((791225155/2147483648), (-144293485/1073741824)), (77/1073741824), by norm_num⟩
  | 1 => ⟨((437804119/1073741824), (269922159/1073741824)), (5/67108864), by norm_num⟩
  | 2 => ⟨((-106796881/1073741824), (-406728229/2147483648)), (179/4294967296), by norm_num⟩
  | 3 => ⟨((-17442399/4294967296), (379281675/4294967296)), (35/2147483648), by norm_num⟩
  | 4 => ⟨((209449419/17179869184), (-1030686659/34359738368)), (171/34359738368), by norm_num⟩
  | 5 => ⟨((-733938905/137438953472), (554488909/68719476736)), (43/34359738368), by norm_num⟩
  | 6 => ⟨((849574109/549755813888), (-496341245/274877906944)), (37/137438953472), by norm_num⟩
  | 7 => ⟨((-96277689/274877906944), (763261185/2199023255552)), (55/1099511627776), by norm_num⟩
  | 8 => ⟨((583707061/8796093022208), (-515360735/8796093022208)), (37/4398046511104), by norm_num⟩
  | 9 => ⟨((-191435237/17592186044416), (621074557/70368744177664)), (89/70368744177664), by norm_num⟩
  | 10 => ⟨((888848003/562949953421312), (-169040521/140737488355328)), (97/562949953421312), by norm_num⟩
  | 11 => ⟨((-927185331/4503599627370496), (335725931/2251799813685248)), (97/4503599627370496), by norm_num⟩
  | 12 => ⟨((879348191/36028797018963968), (-612956305/36028797018963968)), (45/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial4 : Sound J_initial4 F_initial4 c := by
  apply sound_round (sound_add (A_initial3 hcre) (A_term4 hcre) S_initial3 S_term4)
  intro k
  fin_cases k <;> norm_num [J_initial4, J_initial3, J_term4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1346618515/8589934592), (-25511313/2147483648)), (201/2147483648), by norm_num⟩
  | 1 => ⟨((1607211277/2147483648), (58220191/1073741824)), (237/2147483648), by norm_num⟩
  | 2 => ⟨((-200582149/536870912), (-132014111/4294967296)), (305/4294967296), by norm_num⟩
  | 3 => ⟨((614245709/4294967296), (13701959/4294967296)), (139/4294967296), by norm_num⟩
  | 4 => ⟨((-807213371/17179869184), (146069051/34359738368)), (397/34359738368), by norm_num⟩
  | 5 => ⟨((471017529/34359738368), (-25384649/8589934592)), (235/68719476736), by norm_num⟩
  | 6 => ⟨((-244930151/68719476736), (316495825/274877906944)), (237/274877906944), by norm_num⟩
  | 7 => ⟨((226646293/274877906944), (-182959217/549755813888)), (207/1099511627776), by norm_num⟩
  | 8 => ⟨((-186899667/1099511627776), (171943253/2199023255552)), (161/4398046511104), by norm_num⟩
  | 9 => ⟨((276045443/8796093022208), (-137517799/8796093022208)), (225/35184372088832), by norm_num⟩
  | 10 => ⟨((-91889413/17592186044416), (384997841/140737488355328)), (143/140737488355328), by norm_num⟩
  | 11 => ⟨((888755565/1125899906842624), (-3754993/8796093022208)), (165/1125899906842624), by norm_num⟩
  | 12 => ⟨((-982468757/9007199254740992), (271288401/4503599627370496)), (175/9007199254740992), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial5 : Sound J_initial5 F_initial5 c := by
  apply sound_round (sound_add (A_initial4 hcre) (A_term5 hcre) S_initial4 S_term5)
  intro k
  fin_cases k <;> norm_num [J_initial5, J_initial4, J_term5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1566865975/4294967296), (2078181/1073741824)), (27/268435456), by norm_num⟩
  | 1 => ⟨((403345961/1073741824), (63283045/2147483648)), (33/268435456), by norm_num⟩
  | 2 => ⟨((-170319057/4294967296), (-36768949/4294967296)), (355/4294967296), by norm_num⟩
  | 3 => ⟨((-484834539/8589934592), (-86367029/8589934592)), (85/2147483648), by norm_num⟩
  | 4 => ⟨((727720633/17179869184), (349919223/34359738368)), (511/34359738368), by norm_num⟩
  | 5 => ⟨((-314537743/17179869184), (-174588691/34359738368)), (319/68719476736), by norm_num⟩
  | 6 => ⟨((824207749/137438953472), (491013425/274877906944)), (341/274877906944), by norm_num⟩
  | 7 => ⟨((-892132485/549755813888), (-272300235/549755813888)), (159/549755813888), by norm_num⟩
  | 8 => ⟨((415769861/1099511627776), (251982061/2199023255552)), (33/549755813888), by norm_num⟩
  | 9 => ⟨((-341905649/4398046511104), (-402511413/17592186044416)), (49/4398046511104), by norm_num⟩
  | 10 => ⟨((63019267/4398046511104), (35482665/8796093022208)), (133/70368744177664), by norm_num⟩
  | 11 => ⟨((-674255035/281474976710656), (-359373693/562949953421312)), (41/140737488355328), by norm_num⟩
  | 12 => ⟨((206297685/562949953421312), (413499325/4503599627370496)), (47/1125899906842624), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial6 : Sound J_initial6 F_initial6 c := by
  apply sound_round (sound_add (A_initial5 hcre) (A_term6 hcre) S_initial5 S_term6)
  intro k
  fin_cases k <;> norm_num [J_initial6, J_initial5, J_term6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((589211747/2147483648), (-167748979/1073741824)), (503/4294967296), by norm_num⟩
  | 1 => ⟨((296157251/536870912), (724219833/2147483648)), (167/1073741824), by norm_num⟩
  | 2 => ⟨((-452875331/2147483648), (-165361569/536870912)), (123/1073741824), by norm_num⟩
  | 3 => ⟨((469221343/8589934592), (1582086953/8589934592)), (65/1073741824), by norm_num⟩
  | 4 => ⟨((-200532879/17179869184), (-362092789/4294967296)), (217/8589934592), by norm_num⟩
  | 5 => ⟨((46721843/17179869184), (272238409/8589934592)), (75/8589934592), by norm_num⟩
  | 6 => ⟨((-113097177/137438953472), (-348413295/34359738368)), (355/137438953472), by norm_num⟩
  | 7 => ⟨((150102469/549755813888), (1550361405/549755813888)), (367/549755813888), by norm_num⟩
  | 8 => ⟨((-91254033/1099511627776), (-1521385831/2199023255552)), (169/1099511627776), by norm_num⟩
  | 9 => ⟨((24148359/1099511627776), (666219831/4398046511104)), (279/8796093022208), by norm_num⟩
  | 10 => ⟨((-22308715/4398046511104), (-1051842693/35184372088832)), (209/35184372088832), by norm_num⟩
  | 11 => ⟨((291799285/281474976710656), (754875007/140737488355328)), (287/281474976710656), by norm_num⟩
  | 12 => ⟨((-53505733/281474976710656), (-496227973/562949953421312)), (91/562949953421312), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial7 : Sound J_initial7 F_initial7 c := by
  apply sound_round (sound_add (A_initial6 hcre) (A_term7 hcre) S_initial6 S_term7)
  intro k
  fin_cases k <;> norm_num [J_initial7, J_initial6, J_term7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((350887023/2147483648), (-163502981/4294967296)), (299/2147483648), by norm_num⟩
  | 1 => ⟨((210026417/268435456), (24571111/268435456)), (435/2147483648), by norm_num⟩
  | 2 => ⟨((-968142575/2147483648), (-28209157/536870912)), (351/2147483648), by norm_num⟩
  | 3 => ⟨((1897845493/8589934592), (61018029/8589934592)), (51/536870912), by norm_num⟩
  | 4 => ⟨((-1685903081/17179869184), (66557899/8589934592)), (373/8589934592), by norm_num⟩
  | 5 => ⟨((83058743/2147483648), (-28311279/4294967296)), (141/8589934592), by norm_num⟩
  | 6 => ⟨((-456464649/34359738368), (107484809/34359738368)), (363/68719476736), by norm_num⟩
  | 7 => ⟨((546323795/137438953472), (-19266453/17179869184)), (51/34359738368), by norm_num⟩
  | 8 => ⟨((-1149270099/1099511627776), (182893131/549755813888)), (203/549755813888), by norm_num⟩
  | 9 => ⟨((1074407907/4398046511104), (-374867991/4398046511104)), (361/4398046511104), by norm_num⟩
  | 10 => ⟨((-112819759/2199023255552), (42503895/2199023255552)), (73/4398046511104), by norm_num⟩
  | 11 => ⟨((687952757/70368744177664), (-554723257/140737488355328)), (215/70368744177664), by norm_num⟩
  | 12 => ⟨((-119948321/70368744177664), (411516371/562949953421312)), (73/140737488355328), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial8 : Sound J_initial8 F_initial8 c := by
  apply sound_round (sound_add (A_initial7 hcre) (A_term8 hcre) S_initial7 S_term8)
  intro k
  fin_cases k <;> norm_num [J_initial8, J_initial7, J_term8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((148909557/536870912), (114997365/2147483648)), (333/2147483648), by norm_num⟩
  | 1 => ⟨((571218987/1073741824), (-235732533/2147483648)), (255/1073741824), by norm_num⟩
  | 2 => ⟨((-754676301/4294967296), (724190051/4294967296)), (869/4294967296), by norm_num⟩
  | 3 => ⟨((167005491/8589934592), (-1330357307/8589934592)), (533/4294967296), by norm_num⟩
  | 4 => ⟨((215619015/17179869184), (103856115/1073741824)), (513/8589934592), by norm_num⟩
  | 5 => ⟨((-171144273/17179869184), (-392486361/8589934592)), (407/17179869184), by norm_num⟩
  | 6 => ⟨((155546049/34359738368), (599463611/34359738368)), (551/68719476736), by norm_num⟩
  | 7 => ⟨((-222090461/137438953472), (-192959751/34359738368)), (81/34359738368), by norm_num⟩
  | 8 => ⟨((33694287/68719476736), (430757025/274877906944)), (169/274877906944), by norm_num⟩
  | 9 => ⟨((-17949019/137438953472), (-212534339/549755813888)), (315/2199023255552), by norm_num⟩
  | 10 => ⟨((68316855/2199023255552), (752458825/8796093022208)), (265/8796093022208), by norm_num⟩
  | 11 => ⟨((-117464771/17592186044416), (-604047583/35184372088832)), (409/70368744177664), by norm_num⟩
  | 12 => ⟨((184098797/140737488355328), (443717527/140737488355328)), (291/281474976710656), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial9 : Sound J_initial9 F_initial9 c := by
  apply sound_round (sound_add (A_initial8 hcre) (A_term9 hcre) S_initial8 S_term9)
  intro k
  fin_cases k <;> norm_num [J_initial9, J_initial8, J_term9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1591590701/4294967296), (-179618695/4294967296)), (733/4294967296), by norm_num⟩
  | 1 => ⟨((681559167/2147483648), (117926175/1073741824)), (1173/4294967296), by norm_num⟩
  | 2 => ⟨((153268185/2147483648), (-361674271/4294967296)), (131/536870912), by norm_num⟩
  | 3 => ⟨((-1462016161/8589934592), (336506027/8589934592)), (673/4294967296), by norm_num⟩
  | 4 => ⟨((522774875/4294967296), (-64337373/4294967296)), (339/4294967296), by norm_num⟩
  | 5 => ⟨((-1034834955/17179869184), (49390617/8589934592)), (35/1073741824), by norm_num⟩
  | 6 => ⟨((409226573/17179869184), (-78842617/34359738368)), (791/68719476736), by norm_num⟩
  | 7 => ⟨((-136789879/17179869184), (120651173/137438953472)), (121/34359738368), by norm_num⟩
  | 8 => ⟨((1273744549/549755813888), (-166003239/549755813888)), (525/549755813888), by norm_num⟩
  | 9 => ⟨((-1314843641/2199023255552), (50348549/549755813888)), (509/2199023255552), by norm_num⟩
  | 10 => ⟨((152472081/1099511627776), (-108018763/4398046511104)), (223/4398046511104), by norm_num⟩
  | 11 => ⟨((-1027445193/35184372088832), (103438983/17592186044416)), (359/35184372088832), by norm_num⟩
  | 12 => ⟨((396188519/70368744177664), (-178690833/140737488355328)), (531/281474976710656), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial10 : Sound J_initial10 F_initial10 c := by
  apply sound_round (sound_add (A_initial9 hcre) (A_term10 hcre) S_initial9 S_term10)
  intro k
  fin_cases k <;> norm_num [J_initial10, J_initial9, J_term10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((655971291/2147483648), (-313101333/2147483648)), (829/4294967296), by norm_num⟩
  | 1 => ⟨((508421309/1073741824), (771283147/2147483648)), (351/1073741824), by norm_num⟩
  | 2 => ⟨((-497438233/4294967296), (-25712207/67108864)), (1325/4294967296), by norm_num⟩
  | 3 => ⟨((-345283/16777216), (597238919/2147483648)), (449/2147483648), by norm_num⟩
  | 4 => ⟨((34385907/1073741824), (-1359064573/8589934592)), (949/8589934592), by norm_num⟩
  | 5 => ⟨((-147919803/8589934592), (639459807/8589934592)), (411/8589934592), by norm_num⟩
  | 6 => ⟨((7117979/1073741824), (-1022125365/34359738368)), (19/1073741824), by norm_num⟩
  | 7 => ⟨((-284957005/137438953472), (1413161597/137438953472)), (777/137438953472), by norm_num⟩
  | 8 => ⟨((303361859/549755813888), (-1715655557/549755813888)), (881/549755813888), by norm_num⟩
  | 9 => ⟨((-280676501/2199023255552), (926453535/1099511627776)), (893/2199023255552), by norm_num⟩
  | 10 => ⟨((113923425/4398046511104), (-450024873/2199023255552)), (409/4398046511104), by norm_num⟩
  | 11 => ⟨((-162520185/35184372088832), (397029919/8796093022208)), (687/35184372088832), by norm_num⟩
  | 12 => ⟨((50521921/70368744177664), (-1282715155/140737488355328)), (265/70368744177664), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial11 : Sound J_initial11 F_initial11 c := by
  apply sound_round (sound_add (A_initial10 hcre) (A_term11 hcre) S_initial10 S_term11)
  intro k
  fin_cases k <;> norm_num [J_initial11, J_initial10, J_term11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((833971909/4294967296), (-263177761/2147483648)), (913/4294967296), by norm_num⟩
  | 1 => ⟨((805349435/1073741824), (161806933/536870912)), (405/1073741824), by norm_num⟩
  | 2 => ⟨((-493278895/1073741824), (-83582195/268435456)), (795/2147483648), by norm_num⟩
  | 3 => ⟨((566957185/2147483648), (939140321/4294967296)), (559/2147483648), by norm_num⟩
  | 4 => ⟨((-621785957/4294967296), (-520909813/4294967296)), (613/4294967296), by norm_num⟩
  | 5 => ⟨((606825451/8589934592), (30112187/536870912)), (275/4294967296), by norm_num⟩
  | 6 => ⟨((-1022539005/34359738368), (-760937133/34359738368)), (105/4294967296), by norm_num⟩
  | 7 => ⟨((372605663/34359738368), (65143015/8589934592)), (555/68719476736), by norm_num⟩
  | 8 => ⟨((-475616125/137438953472), (-9803615/4294967296)), (325/137438953472), by norm_num⟩
  | 9 => ⟨((269430581/274877906944), (336001525/549755813888)), (679/1099511627776), by norm_num⟩
  | 10 => ⟨((-1096783303/4398046511104), (-647135465/4398046511104)), (321/2199023255552), by norm_num⟩
  | 11 => ⟨((506368717/8796093022208), (282762941/8796093022208)), (139/4398046511104), by norm_num⟩
  | 12 => ⟨((-855638655/70368744177664), (-113015599/17592186044416)), (111/17592186044416), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial12 : Sound J_initial12 F_initial12 c := by
  apply sound_round (sound_add (A_initial11 hcre) (A_term12 hcre) S_initial11 S_term12)
  intro k
  fin_cases k <;> norm_num [J_initial12, J_initial11, J_term12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1447025403/8589934592), (-169398249/8589934592)), (1983/8589934592), by norm_num⟩
  | 1 => ⟨((876180003/1073741824), (80814585/2147483648)), (57/134217728), by norm_num⟩
  | 2 => ⟨((-584117305/1073741824), (57752959/2147483648)), (927/2147483648), by norm_num⟩
  | 3 => ⟨((1444575599/4294967296), (-151498571/2147483648)), (1345/4294967296), by norm_num⟩
  | 4 => ⟨((-820993537/4294967296), (275595109/4294967296)), (95/536870912), by norm_num⟩
  | 5 => ⟨((811208393/8589934592), (-83850731/2147483648)), (351/4294967296), by norm_num⟩
  | 6 => ⟨((-171503367/4294967296), (636443713/34359738368)), (551/17179869184), by norm_num⟩
  | 7 => ⟨((250332749/17179869184), (-502916195/68719476736)), (749/68719476736), by norm_num⟩
  | 8 => ⟨((-639849621/137438953472), (21434377/8589934592)), (901/274877906944), by norm_num⟩
  | 9 => ⟨((726083651/549755813888), (-206291303/274877906944)), (485/549755813888), by norm_num⟩
  | 10 => ⟨((-185119533/549755813888), (222232211/1099511627776)), (59/274877906944), by norm_num⟩
  | 11 => ⟨((685529479/8796093022208), (-108396863/2199023255552)), (105/2199023255552), by norm_num⟩
  | 12 => ⟨((-1161997509/70368744177664), (48304537/4398046511104)), (687/70368744177664), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial13 : Sound J_initial13 F_initial13 c := by
  apply sound_round (sound_add (A_initial12 hcre) (A_term13 hcre) S_initial12 S_term13)
  intro k
  fin_cases k <;> norm_num [J_initial13, J_initial12, J_term13, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((256777119/1073741824), (215103631/4294967296)), (1041/4294967296), by norm_num⟩
  | 1 => ⟨((168969585/268435456), (-153703/1048576)), (489/1073741824), by norm_num⟩
  | 2 => ⟨((-319813519/1073741824), (289878147/1073741824)), (1015/2147483648), by norm_num⟩
  | 3 => ⟨((514558473/4294967296), (-1221394961/4294967296)), (375/1073741824), by norm_num⟩
  | 4 => ⟨((-207401409/4294967296), (881521233/4294967296)), (27/134217728), by norm_num⟩
  | 5 => ⟨((20435809/1073741824), (-975032435/8589934592)), (407/4294967296), by norm_num⟩
  | 6 => ⟨((-116221707/17179869184), (1761789679/34359738368)), (651/17179869184), by norm_num⟩
  | 7 => ⟨((71033177/34359738368), (-675722743/34359738368)), (451/34359738368), by norm_num⟩
  | 8 => ⟨((-36468729/68719476736), (902779393/137438953472)), (1107/274877906944), by norm_num⟩
  | 9 => ⟨((61144229/549755813888), (-1069214507/549755813888)), (19/17179869184), by norm_num⟩
  | 10 => ⟨((-19276415/1099511627776), (568810057/1099511627776)), (151/549755813888), by norm_num⟩
  | 11 => ⟨((5960901/4398046511104), (-549389655/4398046511104)), (549/8796093022208), by norm_num⟩
  | 12 => ⟨((23128675/70368744177664), (60724757/2199023255552)), (917/70368744177664), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial14 : Sound J_initial14 F_initial14 c := by
  apply sound_round (sound_add (A_initial13 hcre) (A_term14 hcre) S_initial13 S_term14)
  intro k
  fin_cases k <;> norm_num [J_initial14, J_initial13, J_term14, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((355463387/1073741824), (70393377/2147483648)), (1071/4294967296), by norm_num⟩
  | 1 => ⟨((102157743/268435456), (-214156827/2147483648)), (1019/2147483648), by norm_num⟩
  | 2 => ⟨((168184501/4294967296), (887009845/4294967296)), (2143/4294967296), by norm_num⟩
  | 3 => ⟨((-792020303/4294967296), (-487705629/2147483648)), (401/1073741824), by norm_num⟩
  | 4 => ⟨((169292205/1073741824), (714987179/4294967296)), (117/536870912), by norm_num⟩
  | 5 => ⟨((-397348881/4294967296), (-198659851/2147483648)), (447/4294967296), by norm_num⟩
  | 6 => ⟨((23397353/536870912), (718057045/17179869184)), (725/17179869184), by norm_num⟩
  | 7 => ⟨((-9346771/536870912), (-34358155/2147483648)), (255/17179869184), by norm_num⟩
  | 8 => ⟨((833212049/137438953472), (366091353/68719476736)), (317/68719476736), by norm_num⟩
  | 9 => ⟨((-514738631/274877906944), (-431944055/274877906944)), (353/274877906944), by norm_num⟩
  | 10 => ⟨((1142830269/2199023255552), (457603219/1099511627776)), (89/274877906944), by norm_num⟩
  | 11 => ⟨((-1151439921/8796093022208), (-879758437/8796093022208)), (657/8796093022208), by norm_num⟩
  | 12 => ⟨((530855827/17592186044416), (386944803/17592186044416)), (279/17592186044416), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial15 : Sound J_initial15 F_initial15 c := by
  apply sound_round (sound_add (A_initial14 hcre) (A_term15 hcre) S_initial14 S_term15)
  intro k
  fin_cases k <;> norm_num [J_initial15, J_initial14, J_term15, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((798885389/2147483648), (-195618231/4294967296)), (1123/4294967296), by norm_num⟩
  | 1 => ⟨((1146777759/4294967296), (504399015/4294967296)), (1091/2147483648), by norm_num⟩
  | 2 => ⟨((844344209/4294967296), (-406004469/4294967296)), (2345/4294967296), by norm_num⟩
  | 3 => ⟨((-1416924563/4294967296), (109793855/2147483648)), (1793/4294967296), by norm_num⟩
  | 4 => ⟨((555159723/2147483648), (-56661493/2147483648)), (1069/4294967296), by norm_num⟩
  | 5 => ⟨((-637538589/4294967296), (123985965/8589934592)), (1043/8589934592), by norm_num⟩
  | 6 => ⟨((596340073/8589934592), (-32733267/4294967296)), (865/17179869184), by norm_num⟩
  | 7 => ⟨((-949888183/34359738368), (122812495/34359738368)), (311/17179869184), by norm_num⟩
  | 8 => ⟨((1320764621/137438953472), (-50039957/34359738368)), (791/137438953472), by norm_num⟩
  | 9 => ⟨((-1630269601/549755813888), (285001843/549755813888)), (451/274877906944), by norm_num⟩
  | 10 => ⟨((904565147/1099511627776), (-89738323/549755813888)), (467/1099511627776), by norm_num⟩
  | 11 => ⟨((-455803247/2199023255552), (25304209/549755813888)), (441/4398046511104), by norm_num⟩
  | 12 => ⟨((1682561797/35184372088832), (-413356713/35184372088832)), (767/35184372088832), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial16 : Sound J_initial16 F_initial16 c := by
  apply sound_round (sound_add (A_initial15 hcre) (A_term16 hcre) S_initial15 S_term16)
  intro k
  fin_cases k <;> norm_num [J_initial16, J_initial15, J_term16, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1468826363/4294967296), (-531746225/4294967296)), (297/1073741824), by norm_num⟩
  | 1 => ⟨((378026199/1073741824), (364180333/1073741824)), (1183/2147483648), by norm_num⟩
  | 2 => ⟨((81704873/1073741824), (-1755070617/4294967296)), (2605/4294967296), by norm_num⟩
  | 3 => ⟨((-464085959/2147483648), (373412945/1073741824)), (1021/2147483648), by norm_num⟩
  | 4 => ⟨((764134317/4294967296), (-507873409/2147483648)), (623/2147483648), by norm_num⟩
  | 5 => ⟨((-882750647/8589934592), (573344831/4294967296)), (1245/8589934592), by norm_num⟩
  | 6 => ⟨((822165225/17179869184), (-1096778989/17179869184)), (529/8589934592), by norm_num⟩
  | 7 => ⟨((-649960235/34359738368), (904654653/34359738368)), (195/8589934592), by norm_num⟩
  | 8 => ⟨((55992793/8589934592), (-653861323/68719476736)), (509/68719476736), by norm_num⟩
  | 9 => ⟨((-34226821/17179869184), (209956439/68719476736)), (595/274877906944), by norm_num⟩
  | 10 => ⟨((601404899/1099511627776), (-969744657/1099511627776)), (631/1099511627776), by norm_num⟩
  | 11 => ⟨((-599272799/4398046511104), (1016614717/4398046511104)), (153/1099511627776), by norm_num⟩
  | 12 => ⟨((34144473/1099511627776), (-975594557/17592186044416)), (547/17592186044416), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial17 : Sound J_initial17 F_initial17 c := by
  apply sound_round (sound_add (A_initial16 hcre) (A_term17 hcre) S_initial16 S_term17)
  intro k
  fin_cases k <;> norm_num [J_initial17, J_initial16, J_term17, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1154060761/4294967296), (-41664509/268435456)), (625/2147483648), by norm_num⟩
  | 1 => ⟨((1210947201/2147483648), (230823973/536870912)), (1273/2147483648), by norm_num⟩
  | 2 => ⟨((-61749725/268435456), (-72453309/134217728)), (1433/2147483648), by norm_num⟩
  | 3 => ⟨((84649055/1073741824), (1018248789/2147483648)), (287/536870912), by norm_num⟩
  | 4 => ⟨((-151223395/4294967296), (-1408003359/4294967296)), (715/2147483648), by norm_num⟩
  | 5 => ⟨((175538985/8589934592), (1600196553/8589934592)), (365/2147483648), by norm_num⟩
  | 6 => ⟨((-197451597/17179869184), (-383428373/4294967296)), (1267/17179869184), by norm_num⟩
  | 7 => ⟨((192060241/34359738368), (316371031/8589934592)), (477/17179869184), by norm_num⟩
  | 8 => ⟨((-160495707/68719476736), (-914594151/68719476736)), (159/17179869184), by norm_num⟩
  | 9 => ⟨((58494067/68719476736), (293691417/68719476736)), (759/274877906944), by norm_num⟩
  | 10 => ⟨((-302247175/1099511627776), (-678492501/549755813888)), (411/549755813888), by norm_num⟩
  | 11 => ⟨((350505541/4398046511104), (1423621465/4398046511104)), (407/2199023255552), by norm_num⟩
  | 12 => ⟨((-184379631/8796093022208), (-42741505/549755813888)), (93/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial18 : Sound J_initial18 F_initial18 c := by
  apply sound_round (sound_add (A_initial17 hcre) (A_term18 hcre) S_initial17 S_term18)
  intro k
  fin_cases k <;> norm_num [J_initial18, J_initial17, J_term18, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((423704945/2147483648), (-554161499/4294967296)), (1309/4294967296), by norm_num⟩
  | 1 => ⟨((831202295/1073741824), (47357151/134217728)), (681/1073741824), by norm_num⟩
  | 2 => ⟨((-579321083/1073741824), (-228870167/536870912)), (781/1073741824), by norm_num⟩
  | 3 => ⟨((205408259/536870912), (778991259/2147483648)), (1275/2147483648), by norm_num⟩
  | 4 => ⟨((-277900897/1073741824), (-65985235/268435456)), (405/1073741824), by norm_num⟩
  | 5 => ⟨((653325667/4294967296), (148167169/1073741824)), (843/4294967296), by norm_num⟩
  | 6 => ⟨((-10215745/134217728), (-140817203/2147483648)), (745/8589934592), by norm_num⟩
  | 7 => ⟨((140750725/4294967296), (461469991/17179869184)), (571/17179869184), by norm_num⟩
  | 8 => ⟨((-423991067/34359738368), (-331222035/34359738368)), (97/8589934592), by norm_num⟩
  | 9 => ⟨((566824097/137438953472), (211198025/68719476736)), (943/274877906944), by norm_num⟩
  | 10 => ⟨((-680929405/549755813888), (-242087547/274877906944)), (65/68719476736), by norm_num⟩
  | 11 => ⟨((92814819/274877906944), (503754097/2199023255552)), (525/2199023255552), by norm_num⟩
  | 12 => ⟨((-370569729/4398046511104), (-119915181/2199023255552)), (489/8796093022208), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial19 : Sound J_initial19 F_initial19 c := by
  apply sound_round (sound_add (A_initial18 hcre) (A_term19 hcre) S_initial18 S_term19)
  intro k
  fin_cases k <;> norm_num [J_initial19, J_initial18, J_term19, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1394462455/8589934592), (-35043997/536870912)), (2675/8589934592), by norm_num⟩
  | 1 => ⟨((471838031/536870912), (86896101/536870912)), (703/1073741824), by norm_num⟩
  | 2 => ⟨((-747791729/1073741824), (-75290203/536870912)), (1629/2147483648), by norm_num⟩
  | 3 => ⟨((289523751/536870912), (165545319/2147483648)), (671/1073741824), by norm_num⟩
  | 4 => ⟨((-100973661/268435456), (-34225965/1073741824)), (861/2147483648), by norm_num⟩
  | 5 => ⟨((1910560989/8589934592), (84274049/8589934592)), (905/4294967296), by norm_num⟩
  | 6 => ⟨((-477666477/4294967296), (-27040667/17179869184)), (101/1073741824), by norm_num⟩
  | 7 => ⟨((410542735/8589934592), (-18145309/34359738368)), (313/8589934592), by norm_num⟩
  | 8 => ⟨((-308638819/17179869184), (42365825/68719476736)), (215/17179869184), by norm_num⟩
  | 9 => ⟨((1648345811/274877906944), (-46808783/137438953472)), (1057/274877906944), by norm_num⟩
  | 10 => ⟨((-1978617315/1099511627776), (156139461/1099511627776)), (589/549755813888), by norm_num⟩
  | 11 => ⟨((269613427/549755813888), (-54365673/1099511627776)), (301/1099511627776), by norm_num⟩
  | 12 => ⟨((-1076596721/8796093022208), (32988353/2199023255552)), (283/4398046511104), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial20 : Sound J_initial20 F_initial20 c := by
  apply sound_round (sound_add (A_initial19 hcre) (A_term20 hcre) S_initial19 S_term20)
  intro k
  fin_cases k <;> norm_num [J_initial20, J_initial19, J_term20, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((751066527/4294967296), (28008721/8589934592)), (173/536870912), by norm_num⟩
  | 1 => ⟨((1805400735/2147483648), (-6281427/134217728)), (1477/2147483648), by norm_num⟩
  | 2 => ⟨((-1370832037/2147483648), (190472505/1073741824)), (1737/2147483648), by norm_num⟩
  | 3 => ⟨((515746085/1073741824), (-131670877/536870912)), (1453/2147483648), by norm_num⟩
  | 4 => ⟨((-177856999/536870912), (458424619/2147483648)), (473/1073741824), by norm_num⟩
  | 5 => ⟨((26185339/134217728), (-299748983/2147483648)), (505/2147483648), by norm_num⟩
  | 6 => ⟨((-52265109/536870912), (637637041/8589934592)), (229/2147483648), by norm_num⟩
  | 7 => ⟨((358746183/8589934592), (-287745361/8589934592)), (721/17179869184), by norm_num⟩
  | 8 => ⟨((-134607439/8589934592), (226150521/17179869184)), (1005/68719476736), by norm_num⟩
  | 9 => ⟨((358741087/68719476736), (-630163813/137438953472)), (627/137438953472), by norm_num⟩
  | 10 => ⟨((-859379727/549755813888), (394242361/274877906944)), (355/274877906944), by norm_num⟩
  | 11 => ⟨((467304755/1099511627776), (-447615561/1099511627776)), (369/1099511627776), by norm_num⟩
  | 12 => ⟨((-465308879/4398046511104), (232531371/2199023255552)), (705/8796093022208), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial21 : Sound J_initial21 F_initial21 c := by
  apply sound_round (sound_add (A_initial20 hcre) (A_term21 hcre) S_initial20 S_term21)
  intro k
  fin_cases k <;> norm_num [J_initial21, J_initial20, J_term21, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((240851423/1073741824), (207537401/4294967296)), (1417/4294967296), by norm_num⟩
  | 1 => ⟨((23081657/33554432), (-199806127/1073741824)), (191/268435456), by norm_num⟩
  | 2 => ⟨((-215907773/536870912), (210806243/536870912)), (1817/2147483648), by norm_num⟩
  | 3 => ⟨((63612369/268435456), (-125374063/268435456)), (3/4194304), by norm_num⟩
  | 4 => ⟨((-76897135/536870912), (413248725/1073741824)), (253/536870912), by norm_num⟩
  | 5 => ⟨((42327111/536870912), (-1054589465/4294967296)), (273/1073741824), by norm_num⟩
  | 6 => ⟨((-321774861/8589934592), (553269711/4294967296)), (1001/8589934592), by norm_num⟩
  | 7 => ⟨((263138373/17179869184), (-494802099/8589934592)), (797/17179869184), by norm_num⟩
  | 8 => ⟨((-374645771/68719476736), (1544623251/68719476736)), (281/17179869184), by norm_num⟩
  | 9 => ⟨((235132733/137438953472), (-65295/8388608)), (711/137438953472), by norm_num⟩
  | 10 => ⟨((-262994687/549755813888), (333012515/137438953472)), (407/274877906944), by norm_num⟩
  | 11 => ⟨((132131759/1099511627776), (-1506206953/2199023255552)), (857/2199023255552), by norm_num⟩
  | 12 => ⟨((-239928451/8796093022208), (1559642895/8796093022208)), (415/4398046511104), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial22 : Sound J_initial22 F_initial22 c := by
  apply sound_round (sound_add (A_initial21 hcre) (A_term22 hcre) S_initial21 S_term22)
  intro k
  fin_cases k <;> norm_num [J_initial22, J_initial21, J_term22, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((618925961/2147483648), (119928491/2147483648)), (1437/4294967296), by norm_num⟩
  | 1 => ⟨((261740941/536870912), (-14071287/67108864)), (195/268435456), by norm_num⟩
  | 2 => ⟨((-94544321/1073741824), (57666315/134217728)), (1867/2147483648), by norm_num⟩
  | 3 => ⟨((-24513629/268435456), (-1086016281/2147483648)), (1589/2147483648), by norm_num⟩
  | 4 => ⟨((122524287/1073741824), (891577593/2147483648)), (527/1073741824), by norm_num⟩
  | 5 => ⟨((-177249651/2147483648), (-568106415/2147483648)), (1147/4294967296), by norm_num⟩
  | 6 => ⟨((100661435/2147483648), (1191849285/8589934592)), (1059/8589934592), by norm_num⟩
  | 7 => ⟨((-48229725/2147483648), (-1066029507/17179869184)), (425/8589934592), by norm_num⟩
  | 8 => ⟨((321392373/34359738368), (208054851/8589934592)), (151/8589934592), by norm_num⟩
  | 9 => ⟨((-236894467/68719476736), (-144159743/17179869184)), (771/137438953472), by norm_num⟩
  | 10 => ⟨((156533307/137438953472), (359189083/137438953472)), (445/274877906944), by norm_num⟩
  | 11 => ⟨((-374751047/1099511627776), (-203198865/274877906944)), (473/1099511627776), by norm_num⟩
  | 12 => ⟨((204905905/2199023255552), (210552351/1099511627776)), (231/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial23 : Sound J_initial23 F_initial23 c := by
  apply sound_round (sound_add (A_initial22 hcre) (A_term23 hcre) S_initial22 S_term23)
  intro k
  fin_cases k <;> norm_num [J_initial23, J_initial22, J_term23, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1474229833/4294967296), (3666955/134217728)), (1463/4294967296), by norm_num⟩
  | 1 => ⟨((335676451/1073741824), (-511204941/4294967296)), (1601/2147483648), by norm_num⟩
  | 2 => ⟨((815534255/4294967296), (1226622649/4294967296)), (1933/2147483648), by norm_num⟩
  | 3 => ⟨((-414194477/1073741824), (-758306265/2147483648)), (1661/2147483648), by norm_num⟩
  | 4 => ⟨((93425435/268435456), (631207575/2147483648)), (139/268435456), by norm_num⟩
  | 5 => ⟨((-248275919/1073741824), (-805224857/4294967296)), (611/2147483648), by norm_num⟩
  | 6 => ⟨((1079152099/8589934592), (420608377/4294967296)), (285/2147483648), by norm_num⟩
  | 7 => ⟨((-500057989/8589934592), (-46728111/1073741824)), (925/17179869184), by norm_num⟩
  | 8 => ⟨((202361163/8589934592), (289631211/17179869184)), (665/34359738368), by norm_num⟩
  | 9 => ⟨((-1163147341/137438953472), (-795984209/137438953472)), (107/17179869184), by norm_num⟩
  | 10 => ⟨((751230239/274877906944), (245639211/137438953472)), (501/274877906944), by norm_num⟩
  | 11 => ⟨((-440558721/549755813888), (-137586573/274877906944)), (269/549755813888), by norm_num⟩
  | 12 => ⟨((946231697/4398046511104), (282091771/2199023255552)), (133/1099511627776), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial24 : Sound J_initial24 F_initial24 c := by
  apply sound_round (sound_add (A_initial23 hcre) (A_term24 hcre) S_initial23 S_term24)
  intro k
  fin_cases k <;> norm_num [J_initial24, J_initial23, J_term24, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1602217361/4294967296), (-52702271/2147483648)), (749/2147483648), by norm_num⟩
  | 1 => ⟨((930729843/4294967296), (205790321/4294967296)), (3313/4294967296), by norm_num⟩
  | 2 => ⟨((739291993/2147483648), (72663291/4294967296)), (4047/4294967296), by norm_num⟩
  | 3 => ⟨((-296025353/536870912), (-17403869/268435456)), (55/67108864), by norm_num⟩
  | 4 => ⟨((516826019/1073741824), (133025935/2147483648)), (1193/2147483648), by norm_num⟩
  | 5 => ⟨((-680831551/2147483648), (-81895461/2147483648)), (663/2147483648), by norm_num⟩
  | 6 => ⟨((368650277/2147483648), (38246173/2147483648)), (1253/8589934592), by norm_num⟩
  | 7 => ⟨((-1363802051/17179869184), (-57348667/8589934592)), (515/8589934592), by norm_num⟩
  | 8 => ⟨((1102109729/34359738368), (34956797/17179869184)), (751/34359738368), by norm_num⟩
  | 9 => ⟨((-1581837359/137438953472), (-67303929/137438953472)), (245/34359738368), by norm_num⟩
  | 10 => ⟨((2041544949/549755813888), (44344309/549755813888)), (1163/549755813888), by norm_num⟩
  | 11 => ⟨((-598308355/549755813888), (-1257265/1099511627776)), (317/549755813888), by norm_num⟩
  | 12 => ⟨((160593669/549755813888), (-1560391/274877906944)), (159/1099511627776), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial25 : Sound J_initial25 F_initial25 c := by
  apply sound_round (sound_add (A_initial24 hcre) (A_term25 hcre) S_initial24 S_term25)
  intro k
  fin_cases k <;> norm_num [J_initial25, J_initial24, J_term25, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initial26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((398868553/1073741824), (-176772589/2147483648)), (385/1073741824), by norm_num⟩
  | 1 => ⟨((476349837/2147483648), (1014256467/4294967296)), (431/536870912), by norm_num⟩
  | 2 => ⟨((721397035/2147483648), (-311091771/1073741824)), (1067/1073741824), by norm_num⟩
  | 3 => ⟨((-36395841/67108864), (575937733/2147483648)), (1881/2147483648), by norm_num⟩
  | 4 => ⟨((127227771/268435456), (-112374055/536870912)), (1293/2147483648), by norm_num⟩
  | 5 => ⟨((-1341033005/4294967296), (148843611/1073741824)), (91/268435456), by norm_num⟩
  | 6 => ⟨((1452196159/8589934592), (-671493325/8589934592)), (1395/8589934592), by norm_num⟩
  | 7 => ⟨((-671472813/8589934592), (326398329/8589934592)), (291/4294967296), by norm_num⟩
  | 8 => ⟨((271280417/8589934592), (-277614393/17179869184)), (861/34359738368), by norm_num⟩
  | 9 => ⟨((-389309479/34359738368), (209482265/34359738368)), (571/68719476736), by norm_num⟩
  | 10 => ⟨((1004743003/274877906944), (-567695139/274877906944)), (343/137438953472), by norm_num⟩
  | 11 => ⟨((-1177625595/1099511627776), (43599707/68719476736)), (759/1099511627776), by norm_num⟩
  | 12 => ⟨((632062195/2199023255552), (-195985661/1099511627776)), (773/4398046511104), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initial26 : Sound J_initial26 F_initial26 c := by
  apply sound_round (sound_add (A_initial25 hcre) (A_term26 hcre) S_initial25 S_term26)
  intro k
  fin_cases k <;> norm_num [J_initial26, J_initial25, J_term26, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_endpointHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-506343237/34359738368), (-408201327/17179869184)), (11/2147483648), by norm_num⟩
  | 1 => ⟨((417206177/8589934592), (672682491/8589934592)), (145/8589934592), by norm_num⟩
  | 2 => ⟨((-687521749/8589934592), (-277131469/2147483648)), (241/8589934592), by norm_num⟩
  | 3 => ⟨((377659921/4294967296), (608920075/4294967296)), (267/8589934592), by norm_num⟩
  | 4 => ⟨((-622352745/8589934592), (-125431327/1073741824)), (111/4294967296), by norm_num⟩
  | 5 => ⟨((1602479/33554432), (1322883813/17179869184)), (295/17179869184), by norm_num⟩
  | 6 => ⟨((-450688799/17179869184), (-726668207/17179869184)), (41/4294967296), by norm_num⟩
  | 7 => ⟨((212199537/17179869184), (342139981/17179869184)), (39/8589934592), by norm_num⟩
  | 8 => ⟨((-699375057/137438953472), (-1127637563/137438953472)), (259/137438953472), by norm_num⟩
  | 9 => ⟨((512228021/274877906944), (825890989/274877906944)), (191/274877906944), by norm_num⟩
  | 10 => ⟨((-337643999/549755813888), (-272200197/274877906944)), (127/549755813888), by norm_num⟩
  | 11 => ⟨((809323301/4398046511104), (652456323/2199023255552)), (307/4398046511104), by norm_num⟩
  | 12 => ⟨((-222283131/4398046511104), (-358398267/4398046511104)), (85/4398046511104), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_endpointHalf : Sound J_endpointHalf F_endpointHalf c := by
  apply sound_round (sound_scale (A_term27 hcre) S_term27)
  intro k
  fin_cases k <;> norm_num [J_endpointHalf, J_term27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_initialHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1532181307/4294967296), (-227797755/2147483648)), (1563/4294967296), by norm_num⟩
  | 1 => ⟨((580651381/2147483648), (84412357/268435456)), (1761/2147483648), by norm_num⟩
  | 2 => ⟨((274758299/1073741824), (-899315011/2147483648)), (2195/2147483648), by norm_num⟩
  | 3 => ⟨((-121979619/268435456), (440198885/1073741824)), (1949/2147483648), by norm_num⟩
  | 4 => ⟨((431116991/1073741824), (-350179437/1073741824)), (1349/2147483648), by norm_num⟩
  | 5 => ⟨((-1135915693/4294967296), (926095397/4294967296)), (765/2147483648), by norm_num⟩
  | 6 => ⟨((76678235/536870912), (-258706857/2147483648)), (739/4294967296), by norm_num⟩
  | 7 => ⟨((-1130746089/17179869184), (994936639/17179869184)), (621/8589934592), by norm_num⟩
  | 8 => ⟨((56892369/2147483648), (-837138177/34359738368)), (927/34359738368), by norm_num⟩
  | 9 => ⟨((-650561953/68719476736), (625437277/68719476736)), (155/17179869184), by norm_num⟩
  | 10 => ⟨((208980251/68719476736), (-104986917/34359738368)), (375/137438953472), by norm_num⟩
  | 11 => ⟨((-487647385/549755813888), (511911737/549755813888)), (837/1099511627776), by norm_num⟩
  | 12 => ⟨((260460315/1099511627776), (-71396307/274877906944)), (215/1099511627776), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_initialHalf : Sound J_initialHalf F_initialHalf c := by
  apply sound_round (sound_add (A_initial26 hcre) (A_endpointHalf hcre) S_initial26 S_endpointHalf)
  intro k
  fin_cases k <;> norm_num [J_initialHalf, J_initial26, J_endpointHalf, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor1 : Sound J_risingFactor1 F_risingFactor1 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q0 hcre) S_variable S_q0)
  intro k
  fin_cases k <;> norm_num [J_risingFactor1, J_variable, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-317972649/1638400), (196977/5120)), 0, by norm_num⟩
  | 1 => ⟨((11/4), (17907/640)), 0, by norm_num⟩
  | 2 => ⟨(1, 0), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising2 : Sound J_rising2 F_rising2 c := by
  apply sound_round (sound_mul (A_variable hcre) (A_risingFactor1 hcre) S_variable S_risingFactor1)
  intro k
  fin_cases k <;> norm_num [J_rising2, J_variable, J_risingFactor1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor2 : Sound J_risingFactor2 F_risingFactor2 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q3 hcre) S_variable S_q3)
  intro k
  fin_cases k <;> norm_num [J_risingFactor2, J_variable, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2873581041/2621440), (-5461976110443/2097152000)), 0, by norm_num⟩
  | 1 => ⟨((-946340347/1638400), (161163/1024)), 0, by norm_num⟩
  | 2 => ⟨((45/8), (53721/1280)), 0, by norm_num⟩
  | 3 => ⟨(1, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising3 : Sound J_rising3 F_rising3 c := by
  apply sound_round (sound_mul (A_rising2 hcre) (A_risingFactor2 hcre) S_rising2 S_risingFactor2)
  intro k
  fin_cases k <;> norm_num [J_rising3, J_rising2, J_risingFactor2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((31/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor3 : Sound J_risingFactor3 F_risingFactor3 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q4 hcre) S_variable S_q4)
  intro k
  fin_cases k <;> norm_num [J_risingFactor3, J_variable, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((86405236639014801/2684354560000), (-106651834482417/4194304000)), 0, by norm_num⟩
  | 1 => ⟨((-18140978593/3276800), (-5282275784043/524288000)), 0, by norm_num⟩
  | 2 => ⟨((-936305147/819200), (1020699/2560)), 0, by norm_num⟩
  | 3 => ⟨((19/2), (17907/320)), 0, by norm_num⟩
  | 4 => ⟨(1, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising4 : Sound J_rising4 F_rising4 c := by
  apply sound_round (sound_mul (A_rising3 hcre) (A_risingFactor3 hcre) S_rising3 S_risingFactor3)
  intro k
  fin_cases k <;> norm_num [J_rising4, J_rising3, J_risingFactor3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor4 : Sound J_risingFactor4 F_risingFactor4 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q5 hcre) S_variable S_q5)
  intro k
  fin_cases k <;> norm_num [J_risingFactor4, J_variable, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1049905951/2048), (83545879/256)), (1/2048), by norm_num⟩
  | 1 => ⟨((78463254877888401/536870912000), (-127502218744989/838860800)), 0, by norm_num⟩
  | 2 => ⟨((-21870634381/1310720), (-5058567214443/209715200)), 0, by norm_num⟩
  | 3 => ⟨((-307937449/163840), (411861/512)), 0, by norm_num⟩
  | 4 => ⟨((115/8), (17907/256)), 0, by norm_num⟩
  | 5 => ⟨(1, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising5 : Sound J_rising5 F_rising5 c := by
  apply sound_round (sound_mul (A_rising4 hcre) (A_risingFactor4 hcre) S_rising4 S_risingFactor4)
  intro k
  fin_cases k <;> norm_num [J_rising5, J_rising4, J_risingFactor4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((47/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor5 : Sound J_risingFactor5 F_risingFactor5 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q6 hcre) S_variable S_q6)
  intro k
  fin_cases k <;> norm_num [J_risingFactor5, J_variable, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-198884555/128), (581708641/64)), (1/64), by norm_num⟩
  | 1 => ⟨((447699853/128), (94591229/64)), (1/256), by norm_num⟩
  | 2 => ⟨((207001286521511603/536870912000), (-442197273214683/838860800)), 0, by norm_num⟩
  | 3 => ⟨((-25547042169/655360), (-4790850401643/104857600)), 0, by norm_num⟩
  | 4 => ⟨((-908861947/327680), (1450467/1024)), 0, by norm_num⟩
  | 5 => ⟨((81/4), (53721/640)), 0, by norm_num⟩
  | 6 => ⟨(1, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising6 : Sound J_rising6 F_rising6 c := by
  apply sound_round (sound_mul (A_rising5 hcre) (A_risingFactor5 hcre) S_rising5 S_risingFactor5)
  intro k
  fin_cases k <;> norm_num [J_rising6, J_rising5, J_risingFactor5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor6 : Sound J_risingFactor6 F_risingFactor6 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q7 hcre) S_variable S_q7)
  intro k
  fin_cases k <;> norm_num [J_risingFactor6, J_variable, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(-137838729, (326008123/8)), (1/2), by norm_num⟩
  | 1 => ⟨((29052363/16), (1090912209/16)), (3/16), by norm_num⟩
  | 2 => ⟨((108184463/8), (415739153/128)), (1/128), by norm_num⟩
  | 3 => ⟨((406279377594588407/536870912000), (-1163164929425331/838860800)), 0, by norm_num⟩
  | 4 => ⟨((-204122600899/2621440), (-31353877419501/419430400)), 0, by norm_num⟩
  | 5 => ⟨((-6240177629/1638400), (11657457/5120)), 0, by norm_num⟩
  | 6 => ⟨((217/8), (125349/1280)), 0, by norm_num⟩
  | 7 => ⟨(1, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising7 : Sound J_rising7 F_rising7 c := by
  apply sound_round (sound_mul (A_rising6 hcre) (A_risingFactor6 hcre) S_rising6 S_risingFactor6)
  intro k
  fin_cases k <;> norm_num [J_rising7, J_rising6, J_risingFactor6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((63/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor7 : Sound J_risingFactor7 F_risingFactor7 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q8 hcre) S_variable S_q8)
  intro k
  fin_cases k <;> norm_num [J_risingFactor7, J_variable, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(-1655580328, -1607428036), 14, by norm_num⟩
  | 1 => ⟨(-1077395228, 603086744), 6, by norm_num⟩
  | 2 => ⟨((251485483/4), (565890363/2)), (1/2), by norm_num⟩
  | 3 => ⟨((77761649/2), (93291411/32)), (1/32), by norm_num⟩
  | 4 => ⟨((319262164907842807/268435456000), (-257079435235707/83886080)), 0, by norm_num⟩
  | 5 => ⟨((-45781109003/327680), (-28863744325101/262144000)), 0, by norm_num⟩
  | 6 => ⟨((-2033706143/409600), (877443/256)), 0, by norm_num⟩
  | 7 => ⟨(35, (17907/160)), 0, by norm_num⟩
  | 8 => ⟨(1, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising8 : Sound J_rising8 F_rising8 c := by
  apply sound_round (sound_mul (A_rising7 hcre) (A_risingFactor7 hcre) S_rising7 S_risingFactor7)
  intro k
  fin_cases k <;> norm_num [J_rising8, J_rising7, J_risingFactor7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((71/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor8 : Sound J_risingFactor8 F_risingFactor8 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q9 hcre) S_variable S_q9)
  intro k
  fin_cases k <;> norm_num [J_risingFactor8, J_variable, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7794391648, -37427233920), 352, by norm_num⟩
  | 1 => ⟨(-19654552288, -11327624080), 160, by norm_num⟩
  | 2 => ⟨(-4477770692, 3993785884), 20, by norm_num⟩
  | 3 => ⟨(367153305, 852755631), 2, by norm_num⟩
  | 4 => ⟨((738479113/8), (-122311299/16)), (1/16), by norm_num⟩
  | 5 => ⟨((1999528228580492463/1342177280000), (-12575323322558451/2097152000)), 0, by norm_num⟩
  | 6 => ⟨((-759327944193/3276800), (-78196660584903/524288000)), 0, by norm_num⟩
  | 7 => ⟨((-2547795441/409600), (6285357/1280)), 0, by norm_num⟩
  | 8 => ⟨((351/8), (161163/1280)), 0, by norm_num⟩
  | 9 => ⟨(1, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising9 : Sound J_rising9 F_rising9 c := by
  apply sound_round (sound_mul (A_rising8 hcre) (A_risingFactor8 hcre) S_rising8 S_risingFactor8)
  intro k
  fin_cases k <;> norm_num [J_rising9, J_rising8, J_risingFactor8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor9 : Sound J_risingFactor9 F_risingFactor9 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q10 hcre) S_variable S_q10)
  intro k
  fin_cases k <;> norm_num [J_risingFactor9, J_variable, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(600570771968, -260551613440), 9216, by norm_num⟩
  | 1 => ⟨(-27822621184, -424251637248), 4352, by norm_num⟩
  | 2 => ⟨(-119744978304, -34532300800), 768, by norm_num⟩
  | 3 => ⟨(-12782049840, 17551165104), 80, by norm_num⟩
  | 4 => ⟨(1385658208, 2068667552), 6, by norm_num⟩
  | 5 => ⟨((1527278033/8), (-368137189/8)), (1/8), by norm_num⟩
  | 6 => ⟨((345746752419272421/268435456000), (-4492546832798829/419430400)), 0, by norm_num⟩
  | 7 => ⟨((-118570755963/327680), (-9839702155329/52428800)), 0, by norm_num⟩
  | 8 => ⟨((-2473453041/327680), (6930009/1024)), 0, by norm_num⟩
  | 9 => ⟨((215/4), (17907/128)), 0, by norm_num⟩
  | 10 => ⟨(1, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising10 : Sound J_rising10 F_rising10 c := by
  apply sound_round (sound_mul (A_rising9 hcre) (A_risingFactor9 hcre) S_rising9 S_risingFactor9)
  intro k
  fin_cases k <;> norm_num [J_rising10, J_rising9, J_risingFactor9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_risingFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_risingFactor10 : Sound J_risingFactor10 F_risingFactor10 c := by
  apply sound_round (sound_add (A_variable hcre) (A_q11 hcre) S_variable S_q11)
  intro k
  fin_cases k <;> norm_num [J_risingFactor10, J_variable, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_rising11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10176283508736, 5568392462336), 237568, by norm_num⟩
  | 1 => ⟨(6233213886464, -5263522291712), 122880, by norm_num⟩
  | 2 => ⟨(-846947768320, -2475003944960), 24576, by norm_num⟩
  | 3 => ⟨(-504287827712, -22482260480), 3072, by norm_num⟩
  | 4 => ⟨(-26653352640, 59433066560), 256, by norm_num⟩
  | 5 => ⟨(4105574504, 4239028692), 12, by norm_num⟩
  | 6 => ⟨((1419051899/4), -144480978), (1/4), by norm_num⟩
  | 7 => ⟨((-5778212321996367/268435456000), (-7471847447341893/419430400)), 0, by norm_num⟩
  | 8 => ⟨((-1411947804597/2621440), (-92140708758219/419430400)), 0, by norm_num⟩
  | 9 => ⟨((-2923235139/327680), (9257919/1024)), 0, by norm_num⟩
  | 10 => ⟨((517/8), (196977/1280)), 0, by norm_num⟩
  | 11 => ⟨(1, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_rising11 : Sound J_rising11 F_rising11 c := by
  apply sound_round (sound_mul (A_rising10 hcre) (A_risingFactor10 hcre) S_rising10 S_risingFactor10)
  intro k
  fin_cases k <;> norm_num [J_rising11, J_rising10, J_risingFactor10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((171535863/268435456), (-487375943/1073741824)), (163/1073741824), by norm_num⟩
  | 1 => ⟨((-286632917/134217728), (388821609/268435456)), (69/134217728), by norm_num⟩
  | 2 => ⟨((239433257/67108864), (-77465621/33554432)), (117/134217728), by norm_num⟩
  | 3 => ⟨((-266625161/67108864), (657743177/268435456)), (33/33554432), by norm_num⟩
  | 4 => ⟨((890554907/268435456), (-2042675/1048576)), (7/8388608), by norm_num⟩
  | 5 => ⟨((-148701037/67108864), (166075917/134217728)), (303/536870912), by norm_num⟩
  | 6 => ⟨((1324011403/1073741824), (-702252093/1073741824)), (171/536870912), by norm_num⟩
  | 7 => ⟨((-631437385/1073741824), (635335661/2147483648)), (83/536870912), by norm_num⟩
  | 8 => ⟨((1053819777/4294967296), (-125526731/1073741824)), (281/4294967296), by norm_num⟩
  | 9 => ⟨((-195384945/2147483648), (44010699/1073741824)), (211/8589934592), by norm_num⟩
  | 10 => ⟨((1043136749/34359738368), (-221759697/17179869184)), (285/34359738368), by norm_num⟩
  | 11 => ⟨((-1265532383/137438953472), (506806371/137438953472)), (349/137438953472), by norm_num⟩
  | 12 => ⟨((1407190329/549755813888), (-529598027/549755813888)), (197/274877906944), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct1 : Sound J_zetaCorrProduct1 F_zetaCorrProduct1 c := by
  apply sound_round (sound_mul (A_variable hcre) (A_term27 hcre) S_variable S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct1, J_variable, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((135534509/68719476736), (-385087165/274877906944)), (259/549755813888), by norm_num⟩
  | 1 => ⟨((-905901565/137438953472), (153608537/34359738368)), (219/137438953472), by norm_num⟩
  | 2 => ⟨((756727331/68719476736), (-244829617/34359738368)), (93/34359738368), by norm_num⟩
  | 3 => ⟨((-105333397/8589934592), (519698313/68719476736)), (105/34359738368), by norm_num⟩
  | 4 => ⟨((351824161/34359738368), (-413175151/68719476736)), (89/34359738368), by norm_num⟩
  | 5 => ⟨((-939937419/137438953472), (524881911/137438953472)), (15/8589934592), by norm_num⟩
  | 6 => ⟨((1046132467/274877906944), (-554865851/274877906944)), (271/274877906944), by norm_num⟩
  | 7 => ⟨((-997826979/549755813888), (501993609/549755813888)), (263/549755813888), by norm_num⟩
  | 8 => ⟨((832647725/1099511627776), (-198363229/549755813888)), (223/1099511627776), by norm_num⟩
  | 9 => ⟨((-1235025825/4398046511104), (278191085/2199023255552)), (167/2199023255552), by norm_num⟩
  | 10 => ⟨((412103407/4398046511104), (-350435077/8796093022208)), (113/4398046511104), by norm_num⟩
  | 11 => ⟨((-999926821/35184372088832), (200219801/17592186044416)), (277/35184372088832), by norm_num⟩
  | 12 => ⟨((1111854087/140737488355328), (-26152989/8796093022208)), (39/17592186044416), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr1 : Sound J_zetaCorr1 F_zetaCorr1 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct1 hcre) S_zetaCorrProduct1)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr1, J_zetaCorrProduct1, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((770326107/2147483648), (-461612497/4294967296)), (783/2147483648), by norm_num⟩
  | 1 => ⟨((566496669/2147483648), (342449695/1073741824)), (1765/2147483648), by norm_num⟩
  | 2 => ⟨((573164327/2147483648), (-457308431/1073741824)), (2201/2147483648), by norm_num⟩
  | 3 => ⟨((-1002170301/2147483648), (448319171/1073741824)), (1957/2147483648), by norm_num⟩
  | 4 => ⟨((55263937/134217728), (-713270597/2147483648)), (339/536870912), by norm_num⟩
  | 5 => ⟨((-1165288737/4294967296), (942497957/4294967296)), (1539/4294967296), by norm_num⟩
  | 6 => ⟨((157442925/1073741824), (-526083493/4294967296)), (93/536870912), by norm_num⟩
  | 7 => ⟨((-580964091/8589934592), (252655985/4294967296)), (313/4294967296), by norm_num⟩
  | 8 => ⟨((936298145/34359738368), (-849535879/34359738368)), (935/34359738368), by norm_num⟩
  | 9 => ⟨((-20933101/2147483648), (158532687/17179869184)), (627/68719476736), by norm_num⟩
  | 10 => ⟨((861677467/274877906944), (-26588951/8589934592)), (379/137438953472), by norm_num⟩
  | 11 => ⟨((-1006542483/1099511627776), (259084303/274877906944)), (847/1099511627776), by norm_num⟩
  | 12 => ⟨((269146675/1099511627776), (-577708703/2199023255552)), (109/549755813888), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart1 : Sound J_zetaPart1 F_zetaPart1 c := by
  apply sound_round (sound_add (A_initialHalf hcre) (A_zetaCorr1 hcre) S_initialHalf S_zetaCorr1)
  intro k
  fin_cases k <;> norm_num [J_zetaPart1, J_initialHalf, J_zetaCorr1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-767213555/8388608), (270225225/2097152)), (317/8388608), by norm_num⟩
  | 1 => ⟨((683538685/2097152), (-842783393/2097152)), (279/2097152), by norm_num⟩
  | 2 => ⟨((-603630499/1048576), (326713909/524288)), (245/1048576), by norm_num⟩
  | 3 => ⟨((705427077/1048576), (-335573597/524288)), (287/1048576), by norm_num⟩
  | 4 => ⟨((-307143117/524288), (513159593/1048576)), (253/1048576), by norm_num⟩
  | 5 => ⟨((26593993/65536), (-622275897/2097152)), (177/1048576), by norm_num⟩
  | 6 => ⟨((-977499211/4194304), (155555211/1048576)), (413/4194304), by norm_num⟩
  | 7 => ⟨((119753351/1048576), (-526421497/8388608)), (415/8388608), by norm_num⟩
  | 8 => ⟨((-818190317/16777216), (191696731/8388608)), (363/16777216), by norm_num⟩
  | 9 => ⟨((9668415/524288), (-485960905/67108864)), (281/33554432), by norm_num⟩
  | 10 => ⟨((-209849749/33554432), (134638595/67108864)), (393/134217728), by norm_num⟩
  | 11 => ⟨((1031787129/536870912), (-130081571/268435456)), (249/268435456), by norm_num⟩
  | 12 => ⟨((-579505835/1073741824), (53908475/536870912)), (579/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct2 : Sound J_zetaCorrProduct2 F_zetaCorrProduct2 c := by
  apply sound_round (sound_mul (A_rising3 hcre) (A_term27 hcre) S_rising3 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct2, J_rising3, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((227066143/35184372088832), (-639811423/70368744177664)), (189/70368744177664), by norm_num⟩
  | 1 => ⟨((-809206207/35184372088832), (997727807/35184372088832)), (331/35184372088832), by norm_num⟩
  | 2 => ⟨((357303513/8796093022208), (-48347469/1099511627776)), (291/17592186044416), by norm_num⟩
  | 3 => ⟨((-417559373/8796093022208), (49658535/1099511627776)), (341/17592186044416), by norm_num⟩
  | 4 => ⟨((727221801/17592186044416), (-607503185/17592186044416)), (75/4398046511104), by norm_num⟩
  | 5 => ⟨((-503732115/17592186044416), (736680351/35184372088832)), (105/8796093022208), by norm_num⟩
  | 6 => ⟨((578605459/35184372088832), (-736615177/70368744177664)), (245/35184372088832), by norm_num⟩
  | 7 => ⟨((-70884909/8796093022208), (623203269/140737488355328)), (123/35184372088832), by norm_num⟩
  | 8 => ⟨((242153333/70368744177664), (-453879753/281474976710656)), (431/281474976710656), by norm_num⟩
  | 9 => ⟨((-1465080069/1125899906842624), (143826015/281474976710656)), (333/562949953421312), by norm_num⟩
  | 10 => ⟨((496860597/1125899906842624), (-159391691/1125899906842624)), (233/1125899906842624), by norm_num⟩
  | 11 => ⟨((-1221479585/9007199254740992), (153996865/4503599627370496)), (591/9007199254740992), by norm_num⟩
  | 12 => ⟨((85755885/2251799813685248), (-255277857/36028797018963968)), (343/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr2 : Sound J_zetaCorr2 F_zetaCorr2 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct2 hcre) S_zetaCorrProduct2)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr2, J_zetaCorrProduct2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((385169983/1073741824), (-115412887/1073741824)), (1567/4294967296), by norm_num⟩
  | 1 => ⟨((566447279/2147483648), (342480143/1073741824)), (883/1073741824), by norm_num⟩
  | 2 => ⟨((573251559/2147483648), (-914711291/2147483648)), (1101/1073741824), by norm_num⟩
  | 3 => ⟨((-250568061/536870912), (896735331/2147483648)), (979/1073741824), by norm_num⟩
  | 4 => ⟨((221077941/536870912), (-713344755/2147483648)), (1357/2147483648), by norm_num⟩
  | 5 => ⟨((-582705859/2147483648), (235646971/1073741824)), (385/1073741824), by norm_num⟩
  | 6 => ⟨((629842331/4294967296), (-131532113/1073741824)), (745/4294967296), by norm_num⟩
  | 7 => ⟨((-581033315/8589934592), (505350007/8589934592)), (627/8589934592), by norm_num⟩
  | 8 => ⟨((7315753/268435456), (-212397821/8589934592)), (117/4294967296), by norm_num⟩
  | 9 => ⟨((-669948653/68719476736), (317082931/34359738368)), (157/17179869184), by norm_num⟩
  | 10 => ⟨((861798771/274877906944), (-425442673/137438953472)), (759/274877906944), by norm_num⟩
  | 11 => ⟨((-1006691589/1099511627776), (1036374809/1099511627776)), (53/68719476736), by norm_num⟩
  | 12 => ⟨((67297137/274877906944), (-144431071/549755813888)), (437/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart2 : Sound J_zetaPart2 F_zetaPart2 c := by
  apply sound_round (sound_add (A_zetaPart1 hcre) (A_zetaCorr2 hcre) S_zetaPart1 S_zetaCorr2)
  intro k
  fin_cases k <;> norm_num [J_zetaPart2, J_zetaPart1, J_zetaCorr2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6539673/16384), (-1113460521/32768)), (141/16384), by norm_num⟩
  | 1 => ⟨((-210467387/16384), (897249519/8192)), (517/16384), by norm_num⟩
  | 2 => ⟨((40464037/1024), (-716496093/4096)), (237/4096), by norm_num⟩
  | 3 => ⟨((-514093993/8192), (188900887/1024)), (289/4096), by norm_num⟩
  | 4 => ⟨((548063475/8192), (-1182941037/8192)), (529/8192), by norm_num⟩
  | 5 => ⟨((-438911271/8192), (22884491/256)), (193/4096), by norm_num⟩
  | 6 => ⟨((281127543/8192), (-745688973/16384)), (235/8192), by norm_num⟩
  | 7 => ⟨((-18735917/1024), (640848431/32768)), (489/32768), by norm_num⟩
  | 8 => ⟨((1094208199/131072), (-236449421/32768)), (887/131072), by norm_num⟩
  | 9 => ⟨((-435987313/131072), (302846519/131072)), (357/131072), by norm_num⟩
  | 10 => ⟨((1232578779/1048576), (-676179641/1048576)), (129/131072), by norm_num⟩
  | 11 => ⟨((-782088575/2097152), (327727085/2097152)), (339/1048576), by norm_num⟩
  | 12 => ⟨((899787763/8388608), (-135403061/4194304)), (815/8388608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct3 : Sound J_zetaCorrProduct3 F_zetaCorrProduct3 c := by
  apply sound_round (sound_mul (A_rising5 hcre) (A_term27 hcre) S_rising5 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct3, J_rising5, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16571249/18014398509481984), (-705365235/9007199254740992)), (359/18014398509481984), by norm_num⟩
  | 1 => ⟨((-33332205/1125899906842624), (71049737/281474976710656)), (329/4503599627370496), by norm_num⟩
  | 2 => ⟨((205068249/2251799813685248), (-907785099/2251799813685248)), (301/2251799813685248), by norm_num⟩
  | 3 => ⟨((-162836501/1125899906842624), (478666701/1125899906842624)), (367/2251799813685248), by norm_num⟩
  | 4 => ⟨((173596151/1125899906842624), (-749380393/2251799813685248)), (21/140737488355328), by norm_num⟩
  | 5 => ⟨((-139022779/1125899906842624), (231953253/1125899906842624)), (245/2251799813685248), by norm_num⟩
  | 6 => ⟨((356182535/4503599627370496), (-944771849/9007199254740992)), (597/9007199254740992), by norm_num⟩
  | 7 => ⟨((-379808045/9007199254740992), (811941143/18014398509481984)), (155/4503599627370496), by norm_num⟩
  | 8 => ⟨((86646137/4503599627370496), (-599152635/36028797018963968)), (563/36028797018963968), by norm_num⟩
  | 9 => ⟨((-138096631/18014398509481984), (383700009/72057594037927936)), (905/144115188075855872), by norm_num⟩
  | 10 => ⟨((780825367/288230376151711744), (-418313/281474976710656)), (327/144115188075855872), by norm_num⟩
  | 11 => ⟨((-61930585/72057594037927936), (207611575/576460752303423488)), (215/288230376151711744), by norm_num⟩
  | 12 => ⟨((1140011693/4611686018427387904), (-343105517/4611686018427387904)), (1033/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr3 : Sound J_zetaCorr3 F_zetaCorr3 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct3 hcre) S_zetaCorrProduct3)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr3, J_zetaCorrProduct3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6018281/16777216), (-115412971/1073741824)), (49/134217728), by norm_num⟩
  | 1 => ⟨((566447215/2147483648), (171240207/536870912)), (1767/2147483648), by norm_num⟩
  | 2 => ⟨((573251755/2147483648), (-914712157/2147483648)), (2203/2147483648), by norm_num⟩
  | 3 => ⟨((-1002272555/2147483648), (224184061/536870912)), (1959/2147483648), by norm_num⟩
  | 4 => ⟨((884312095/2147483648), (-356672735/1073741824)), (679/1073741824), by norm_num⟩
  | 5 => ⟨((-145676531/536870912), (942588769/4294967296)), (1541/4294967296), by norm_num⟩
  | 6 => ⟨((629842671/4294967296), (-526128903/4294967296)), (373/2147483648), by norm_num⟩
  | 7 => ⟨((-581033677/8589934592), (252675197/4294967296)), (157/2147483648), by norm_num⟩
  | 8 => ⟨((936417045/34359738368), (-849591855/34359738368)), (937/34359738368), by norm_num⟩
  | 9 => ⟨((-167487295/17179869184), (158541557/17179869184)), (629/68719476736), by norm_num⟩
  | 10 => ⟨((215449879/68719476736), (-850885755/274877906944)), (95/34359738368), by norm_num⟩
  | 11 => ⟨((-503346267/549755813888), (1036375205/1099511627776)), (849/1099511627776), by norm_num⟩
  | 12 => ⟨((67297205/274877906944), (-18053889/68719476736)), (219/1099511627776), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart3 : Sound J_zetaPart3 F_zetaPart3 c := by
  apply sound_round (sound_add (A_zetaPart2 hcre) (A_zetaCorr3 hcre) S_zetaPart2 S_zetaCorr3)
  intro k
  fin_cases k <;> norm_num [J_zetaPart3, J_zetaPart2, J_zetaCorr3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((767878781/128), (342346367/64)), (239/128), by norm_num⟩
  | 1 => ⟨((-530731087/32), (-631225109/32)), (221/32), by norm_num⟩
  | 2 => ⟨((698748739/32), (1127099789/32)), (411/32), by norm_num⟩
  | 3 => ⟨((-35543531/2), (-1307592331/32)), (511/32), by norm_num⟩
  | 4 => ⟨((151093143/16), (69567751/2)), (477/32), by norm_num⟩
  | 5 => ⟨((-89357073/32), (-371622309/16)), (89/8), by norm_num⟩
  | 6 => ⟨((-5272243/16), (1623910969/128)), (889/128), by norm_num⟩
  | 7 => ⟨((258802751/256), (-1493001409/256)), (119/32), by norm_num⟩
  | 8 => ⟨((-96735859/128), (1178506015/512)), (445/256), by norm_num⟩
  | 9 => ⟨((404038811/1024), (-202513415/256)), (185/256), by norm_num⟩
  | 10 => ⟨((-681036595/4096), (978972767/4096)), (69/256), by norm_num⟩
  | 11 => ⟨((979021047/16384), (-1045534983/16384)), (1497/16384), by norm_num⟩
  | 12 => ⟨((-19306701/1024), (493487725/32768)), (931/32768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct4 : Sound J_zetaCorrProduct4 F_zetaCorrProduct4 c := by
  apply sound_round (sound_mul (A_rising7 hcre) (A_term27 hcre) S_rising7 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct4, J_rising7, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-273315533/576460752303423488), (-487413285/1152921504606846976)), (341/2305843009213693952), by norm_num⟩
  | 1 => ⟨((377812367/288230376151711744), (449351203/288230376151711744)), (79/144115188075855872), by norm_num⟩
  | 2 => ⟨((-497419355/288230376151711744), (-802350285/288230376151711744)), (293/288230376151711744), by norm_num⟩
  | 3 => ⟨((202419431/144115188075855872), (930837793/288230376151711744)), (365/288230376151711744), by norm_num⟩
  | 4 => ⟨((-215117823/288230376151711744), (-792372855/288230376151711744)), (85/72057594037927936), by norm_num⟩
  | 5 => ⟨((63610759/288230376151711744), (264547353/144115188075855872)), (127/144115188075855872), by norm_num⟩
  | 6 => ⟨((30025279/1152921504606846976), (-1156016035/1152921504606846976)), (317/576460752303423488), by norm_num⟩
  | 7 => ⟨((-92117159/1152921504606846976), (531412621/1152921504606846976)), (679/2305843009213693952), by norm_num⟩
  | 8 => ⟨((68863507/1152921504606846976), (-209736229/1152921504606846976)), (635/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-287623739/9223372036854775808), (576654163/9223372036854775808)), (1055/18446744073709551616), by norm_num⟩
  | 10 => ⟨((484810583/36893488147419103232), (-696902871/36893488147419103232)), (787/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-87117155/18446744073709551616), (186071655/36893488147419103232)), (1067/147573952589676412928), by norm_num⟩
  | 12 => ⟨((879609047/590295810358705651712), (-351299877/295147905179352825856)), (1327/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr4 : Sound J_zetaCorr4 F_zetaCorr4 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct4 hcre) S_zetaCorrProduct4)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr4, J_zetaCorrProduct4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((770339967/2147483648), (-230825943/2147483648)), (1569/4294967296), by norm_num⟩
  | 1 => ⟨((283223609/1073741824), (684960831/2147483648)), (221/268435456), by norm_num⟩
  | 2 => ⟨((573251751/2147483648), (-914712163/2147483648)), (551/536870912), by norm_num⟩
  | 3 => ⟨((-125284069/268435456), (896736251/2147483648)), (245/268435456), by norm_num⟩
  | 4 => ⟨((884312093/2147483648), (-178336369/536870912)), (1359/2147483648), by norm_num⟩
  | 5 => ⟨((-1165412247/4294967296), (942588777/4294967296)), (771/2147483648), by norm_num⟩
  | 6 => ⟨((629842671/4294967296), (-526128907/4294967296)), (747/4294967296), by norm_num⟩
  | 7 => ⟨((-290516839/4294967296), (252675199/4294967296)), (629/8589934592), by norm_num⟩
  | 8 => ⟨((936417047/34359738368), (-849591861/34359738368)), (469/17179869184), by norm_num⟩
  | 9 => ⟨((-334974591/34359738368), (79270779/8589934592)), (315/34359738368), by norm_num⟩
  | 10 => ⟨((26931235/8589934592), (-6647545/2147483648)), (761/274877906944), by norm_num⟩
  | 11 => ⟨((-1006692539/1099511627776), (1036375211/1099511627776)), (425/549755813888), by norm_num⟩
  | 12 => ⟨((538377643/2199023255552), (-577724451/2199023255552)), (439/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart4 : Sound J_zetaPart4 F_zetaPart4 c := by
  apply sound_round (sound_add (A_zetaPart3 hcre) (A_zetaCorr4 hcre) S_zetaPart3 S_zetaCorr4)
  intro k
  fin_cases k <;> norm_num [J_zetaPart4, J_zetaPart3, J_zetaCorr4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(-2008299960, 732698522), 488, by norm_num⟩
  | 1 => ⟨(6660009992, -1146993312), 1948, by norm_num⟩
  | 2 => ⟨(-10720924640, -104102328), 3864, by norm_num⟩
  | 3 => ⟨(11175051976, 2158244512), 5088, by norm_num⟩
  | 4 => ⟨(-8471636256, -3310301752), 5000, by norm_num⟩
  | 5 => ⟨(4961155248, 3074107532), 3912, by norm_num⟩
  | 6 => ⟨(-2318898380, -2105922680), 2548, by norm_num⟩
  | 7 => ⟨(876133209, 1150769858), 1415, by norm_num⟩
  | 8 => ⟨((-528997549/2), -523428738), (1369/2), by norm_num⟩
  | 9 => ⟨((477388279/8), (407145089/2)), 293, by norm_num⟩
  | 10 => ⟨((-113577453/16), (-1103096105/16)), (1801/16), by norm_num⟩
  | 11 => ⟨((-6571185/4), (164735345/8)), (2507/64), by norm_num⟩
  | 12 => ⟨((187320471/128), (-700288129/128)), (399/32), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct5 : Sound J_zetaCorrProduct5 F_zetaCorrProduct5 c := by
  apply sound_round (sound_mul (A_rising9 hcre) (A_term27 hcre) S_rising9 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct5, J_rising9, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-202846471/36893488147419103232), (296022133/147573952589676412928)), (99/73786976294838206464), by norm_num⟩
  | 1 => ⟨((672688119/36893488147419103232), (-231701987/73786976294838206464)), (395/73786976294838206464), by norm_num⟩
  | 2 => ⟨((-1082857029/36893488147419103232), (-10514759/36893488147419103232)), (391/36893488147419103232), by norm_num⟩
  | 3 => ⟨((564362869/18446744073709551616), (217991481/36893488147419103232)), (515/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-427834873/18446744073709551616), (-10448561/1152921504606846976)), (253/18446744073709551616), by norm_num⟩
  | 5 => ⟨((501096875/36893488147419103232), (155248687/18446744073709551616)), (791/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-468436351/73786976294838206464), (-212706763/36893488147419103232)), (515/73786976294838206464), by norm_num⟩
  | 7 => ⟨((176986041/73786976294838206464), (14529055/4611686018427387904)), (1145/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-213723623/295147905179352825856), (-845894931/590295810358705651712)), (1107/590295810358705651712), by norm_num⟩
  | 9 => ⟨((385745275/2361183241434822606848), (657972981/1180591620717411303424)), (1895/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-183548561/9444732965739290427392), (-1782675149/9444732965739290427392)), (91/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-84955703/18889465931478580854784), (532446093/9444732965739290427392)), (2027/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((302722081/75557863725914323419136), (-565855613/37778931862957161709568)), (645/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr5 : Sound J_zetaCorr5 F_zetaCorr5 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct5 hcre) S_zetaCorrProduct5)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr5, J_zetaCorrProduct5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((770339967/2147483648), (-230825943/2147483648)), (785/2147483648), by norm_num⟩
  | 1 => ⟨((283223609/1073741824), (684960831/2147483648)), (1769/2147483648), by norm_num⟩
  | 2 => ⟨((573251751/2147483648), (-914712163/2147483648)), (2205/2147483648), by norm_num⟩
  | 3 => ⟨((-125284069/268435456), (896736251/2147483648)), (1961/2147483648), by norm_num⟩
  | 4 => ⟨((884312093/2147483648), (-178336369/536870912)), (85/134217728), by norm_num⟩
  | 5 => ⟨((-1165412247/4294967296), (942588777/4294967296)), (1543/4294967296), by norm_num⟩
  | 6 => ⟨((629842671/4294967296), (-526128907/4294967296)), (187/1073741824), by norm_num⟩
  | 7 => ⟨((-290516839/4294967296), (252675199/4294967296)), (315/4294967296), by norm_num⟩
  | 8 => ⟨((936417047/34359738368), (-849591861/34359738368)), (939/34359738368), by norm_num⟩
  | 9 => ⟨((-334974591/34359738368), (79270779/8589934592)), (631/68719476736), by norm_num⟩
  | 10 => ⟨((26931235/8589934592), (-6647545/2147483648)), (381/137438953472), by norm_num⟩
  | 11 => ⟨((-1006692539/1099511627776), (1036375211/1099511627776)), (851/1099511627776), by norm_num⟩
  | 12 => ⟨((538377643/2199023255552), (-577724451/2199023255552)), (55/274877906944), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart5 : Sound J_zetaPart5 F_zetaPart5 c := by
  apply sound_round (sound_add (A_zetaPart4 hcre) (A_zetaCorr5 hcre) S_zetaPart4 S_zetaCorr5)
  intro k
  fin_cases k <;> norm_num [J_zetaPart5, J_zetaPart4, J_zetaCorr5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorrProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(-35311208960, -647703577088), 178688, by norm_num⟩
  | 1 => ⟨(-317459132416, 1993649549312), 720896, by norm_num⟩
  | 2 => ⟨(1145425983488, -2939696820224), 1439744, by norm_num⟩
  | 3 => ⟨(-1826439241728, 2750095134720), 1912832, by norm_num⟩
  | 4 => ⟨(1869977583616, -1809488322560), 1892352, by norm_num⟩
  | 5 => ⟨(-1402565136384, 865084956672), 1495040, by norm_num⟩
  | 6 => ⟨(824603438080, -287856448512), 979968, by norm_num⟩
  | 7 => ⟨(-395673612032, 47184352000), 549376, by norm_num⟩
  | 8 => ⟨(158970306304, 15737229952), 268928, by norm_num⟩
  | 9 => ⟨(-54332437888, -17768949440), 116544, by norm_num⟩
  | 10 => ⟨(15918374064, 9399146128), 45376, by norm_num⟩
  | 11 => ⟨(-3991116952, -3721290976), 16036, by norm_num⟩
  | 12 => ⟨(841572186, 1220421854), 5189, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorrProduct6 : Sound J_zetaCorrProduct6 F_zetaCorrProduct6 c := by
  apply sound_round (sound_mul (A_rising11 hcre) (A_term27 hcre) S_rising11 S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaCorrProduct6, J_rising11, J_term27, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((63402925/18889465931478580854784), (1162982033/18889465931478580854784)), (161/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((17812897/590295810358705651712), (-1789845453/9444732965739290427392)), (81/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((-514166467/4722366482869645213696), (1319590745/4722366482869645213696)), (647/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((819864247/4722366482869645213696), (-617240537/2361183241434822606848)), (859/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-839408029/4722366482869645213696), (812255205/4722366482869645213696)), (425/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((629592807/4722366482869645213696), (-194162557/2361183241434822606848)), (1343/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-740306999/9444732965739290427392), (258429851/9444732965739290427392)), (1761/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((88806307/2361183241434822606848), (-169443417/37778931862957161709568)), (987/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-1141754447/75557863725914323419136), (-56513863/37778931862957161709568)), (1933/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((1560902889/302231454903657293676544), (255239831/151115727451828646838272)), (3349/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-457314949/302231454903657293676544), (-8438303/9444732965739290427392)), (163/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((917278329/2417851639229258349412352), (855264231/2417851639229258349412352)), (3687/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-773674075/9671406556917033397649408), (-1121958121/9671406556917033397649408)), (4771/9671406556917033397649408), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaCorr6 : Sound J_zetaCorr6 F_zetaCorr6 c := by
  apply sound_round (sound_scale (A_zetaCorrProduct6 hcre) S_zetaCorrProduct6)
  intro k
  fin_cases k <;> norm_num [J_zetaCorr6, J_zetaCorrProduct6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaPart6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((770339967/2147483648), (-230825943/2147483648)), (1571/4294967296), by norm_num⟩
  | 1 => ⟨((283223609/1073741824), (684960831/2147483648)), (885/1073741824), by norm_num⟩
  | 2 => ⟨((573251751/2147483648), (-914712163/2147483648)), (1103/1073741824), by norm_num⟩
  | 3 => ⟨((-125284069/268435456), (896736251/2147483648)), (981/1073741824), by norm_num⟩
  | 4 => ⟨((884312093/2147483648), (-178336369/536870912)), (1361/2147483648), by norm_num⟩
  | 5 => ⟨((-1165412247/4294967296), (942588777/4294967296)), (193/536870912), by norm_num⟩
  | 6 => ⟨((629842671/4294967296), (-526128907/4294967296)), (749/4294967296), by norm_num⟩
  | 7 => ⟨((-290516839/4294967296), (252675199/4294967296)), (631/8589934592), by norm_num⟩
  | 8 => ⟨((936417047/34359738368), (-849591861/34359738368)), (235/8589934592), by norm_num⟩
  | 9 => ⟨((-334974591/34359738368), (79270779/8589934592)), (79/8589934592), by norm_num⟩
  | 10 => ⟨((26931235/8589934592), (-6647545/2147483648)), (763/274877906944), by norm_num⟩
  | 11 => ⟨((-1006692539/1099511627776), (1036375211/1099511627776)), (213/274877906944), by norm_num⟩
  | 12 => ⟨((538377643/2199023255552), (-577724451/2199023255552)), (441/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaPart6 : Sound J_zetaPart6 F_zetaPart6 c := by
  apply sound_round (sound_add (A_zetaPart5 hcre) (A_zetaCorr6 hcre) S_zetaPart5 S_zetaCorr6)
  intro k
  fin_cases k <;> norm_num [J_zetaPart6, J_zetaPart5, J_zetaCorr6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_q13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(-1, 0), 0, by norm_num⟩
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
  | _ => zero

private theorem S_q13 : Sound J_q13 F_q13 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (-1, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_sminusone : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/8), (17907/1280)), 0, by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_sminusone : Sound J_sminusone F_sminusone c := by
  apply sound_round (sound_add (A_variable hcre) (A_q13 hcre) S_variable S_q13)
  intro k
  fin_cases k <;> norm_num [J_sminusone, J_variable, J_q13, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaRegularPart : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((195807899/134217728), (1350723627/268435456)), (1387/268435456), by norm_num⟩
  | 1 => ⟨((-1110370117/268435456), (951007753/268435456)), (1611/134217728), by norm_num⟩
  | 2 => ⟨((830716937/134217728), (275593821/67108864)), (1029/67108864), by norm_num⟩
  | 3 => ⟨((-370208257/67108864), (-940527537/134217728)), (935/67108864), by norm_num⟩
  | 4 => ⟨((277086881/67108864), (417415389/67108864)), (1325/134217728), by norm_num⟩
  | 5 => ⟨((-352261531/134217728), (-69720507/16777216)), (1533/268435456), by norm_num⟩
  | 6 => ⟨((191134957/134217728), (1227469431/536870912)), (379/134217728), by norm_num⟩
  | 7 => ⟨((-717182319/1073741824), (-1155499623/1073741824)), (651/536870912), by norm_num⟩
  | 8 => ⟨((590279409/2147483648), (951745547/2147483648)), (247/536870912), by norm_num⟩
  | 9 => ⟨((-432206797/4294967296), (-43558355/268435456)), (169/1073741824), by norm_num⟩
  | 10 => ⟨((569764823/17179869184), (459358321/8589934592)), (13/268435456), by norm_num⟩
  | 11 => ⟨((-682855789/68719476736), (-1101035079/68719476736)), (943/68719476736), by norm_num⟩
  | 12 => ⟨((750199065/274877906944), (1209598135/274877906944)), (31/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaRegularPart : Sound J_zetaRegularPart F_zetaRegularPart c := by
  apply sound_round (sound_mul (A_sminusone hcre) (A_zetaPart6 hcre) S_sminusone S_zetaPart6)
  intro k
  fin_cases k <;> norm_num [J_zetaRegularPart, J_sminusone, J_zetaPart6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaIntegral : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213613553/268435456), (-688839739/536870912)), (37/134217728), by norm_num⟩
  | 1 => ⟨((22001107/8388608), (141893963/33554432)), (123/134217728), by norm_num⟩
  | 2 => ⟨((-145024119/33554432), (-233829677/33554432)), (51/33554432), by norm_num⟩
  | 3 => ⟨((637301117/134217728), (1027552627/134217728)), (227/134217728), by norm_num⟩
  | 4 => ⟨((-525110129/134217728), (-846661457/134217728)), (47/33554432), by norm_num⟩
  | 5 => ⟨((43266933/16777216), (1116183217/268435456)), (125/134217728), by norm_num⟩
  | 6 => ⟨((-190134337/134217728), (-1226252599/536870912)), (139/268435456), by norm_num⟩
  | 7 => ⟨((716173437/1073741824), (288680609/268435456)), (33/134217728), by norm_num⟩
  | 8 => ⟨((-73762213/268435456), (-475722097/1073741824)), (55/536870912), by norm_num⟩
  | 9 => ⟨((432192393/4294967296), (348422761/2147483648)), (81/2147483648), by norm_num⟩
  | 10 => ⟨((-71221781/2147483648), (-918675665/17179869184)), (215/17179869184), by norm_num⟩
  | 11 => ⟨((682866535/68719476736), (1101020045/68719476736)), (65/17179869184), by norm_num⟩
  | 12 => ⟨((-750205567/274877906944), (-1209594151/274877906944)), (9/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaIntegral : Sound J_zetaIntegral F_zetaIntegral c := by
  apply sound_round (sound_scale (A_term27 hcre) S_term27)
  intro k
  fin_cases k <;> norm_num [J_zetaIntegral, J_term27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((178002245/268435456), (503151879/134217728)), (731/134217728), by norm_num⟩
  | 1 => ⟨((-101583673/67108864), (65192483/8388608)), (1735/134217728), by norm_num⟩
  | 2 => ⟨((250620461/134217728), (-192065533/67108864)), (1131/67108864), by norm_num⟩
  | 3 => ⟨((-103115397/134217728), (43512545/67108864)), (2097/134217728), by norm_num⟩
  | 4 => ⟨((29063633/134217728), (-11830679/134217728)), (1513/134217728), by norm_num⟩
  | 5 => ⟨((-6126067/134217728), (655105/268435456)), (1783/268435456), by norm_num⟩
  | 6 => ⟨((250155/33554432), (19013/8388608)), (897/268435456), by norm_num⟩
  | 7 => ⟨((-504441/536870912), (-777187/1073741824)), (783/536870912), by norm_num⟩
  | 8 => ⟨((181705/2147483648), (301353/2147483648)), (151/268435456), by norm_num⟩
  | 9 => ⟨((-3601/1073741824), (-44079/2147483648)), (419/2147483648), by norm_num⟩
  | 10 => ⟨((-9425/17179869184), (40977/17179869184)), (1047/17179869184), by norm_num⟩
  | 11 => ⟨((5373/34359738368), (-7517/34359738368)), (1203/68719476736), by norm_num⟩
  | 12 => ⟨((-3251/137438953472), (249/17179869184)), (5/1073741824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaFinite : Sound J_zetaFinite F_zetaFinite c := by
  apply sound_round (sound_add (A_zetaRegularPart hcre) (A_zetaIntegral hcre) S_zetaRegularPart S_zetaIntegral)
  intro k
  fin_cases k <;> norm_num [J_zetaFinite, J_zetaRegularPart, J_zetaIntegral, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((178002245/268435456), (503151879/134217728)), (1479/268435456), by norm_num⟩
  | 1 => ⟨((-101583673/67108864), (65192483/8388608)), (109/8388608), by norm_num⟩
  | 2 => ⟨((250620461/134217728), (-192065533/67108864)), (4541/268435456), by norm_num⟩
  | 3 => ⟨((-103115397/134217728), (43512545/67108864)), (16841/1073741824), by norm_num⟩
  | 4 => ⟨((29063633/134217728), (-11830679/134217728)), (24337/2147483648), by norm_num⟩
  | 5 => ⟨((-6126067/134217728), (655105/268435456)), (115143/17179869184), by norm_num⟩
  | 6 => ⟨((250155/33554432), (19013/8388608)), (467511/137438953472), by norm_num⟩
  | 7 => ⟨((-504441/536870912), (-777187/1073741824)), (1669555/1099511627776), by norm_num⟩
  | 8 => ⟨((181705/2147483648), (301353/2147483648)), (2737867/4398046511104), by norm_num⟩
  | 9 => ⟨((-3601/1073741824), (-44079/2147483648)), (17951917/70368744177664), by norm_num⟩
  | 10 => ⟨((-9425/17179869184), (40977/17179869184)), (34042547/281474976710656), by norm_num⟩
  | 11 => ⟨((5373/34359738368), (-7517/34359738368)), (174527893/2251799813685248), by norm_num⟩
  | 12 => ⟨((-3251/137438953472), (249/17179869184)), (1164749991/18014398509481984), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := by
  apply sound_round (zeta_sound hc S_zetaFinite)
  intro k
  fin_cases k <;> norm_num [J_zetaActual,J_zetaFinite,inflate,zero,size]

private def J_negativeHalfLogPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negativeHalfLogPi : Sound J_negativeHalfLogPi F_negativeHalfLogPi c := by
  apply sound_round (sound_scale (A_logpi hcre) S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negativeHalfLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piArg : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4201177/8388608), (-1074721093/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul (A_negativeHalfLogPi hcre) (A_variable hcre) S_negativeHalfLogPi S_variable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negativeHalfLogPi, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piPower : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-52101137977583/562949953421312), (-337164994162109/562949953421312)), (55796161/2251799813685248), by norm_num⟩
  | 1 => ⟨((227515143/4294967296), (1472331411/4294967296)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((-32555423/2147483648), (-1685421769/17179869184)), (75/17179869184), by norm_num⟩
  | 3 => ⟨((198758217/68719476736), (1286235113/68719476736)), (59/68719476736), by norm_num⟩
  | 4 => ⟨((-227524471/549755813888), (-1472391775/549755813888)), (35/274877906944), by norm_num⟩
  | 5 => ⟨((208363249/4398046511104), (1348392695/4398046511104)), (67/4398046511104), by norm_num⟩
  | 6 => ⟨((-39753273/8796093022208), (-514515139/17592186044416)), (53/35184372088832), by norm_num⟩
  | 7 => ⟨((208030901/562949953421312), (673120979/281474976710656)), (9/70368744177664), by norm_num⟩
  | 8 => ⟨((-119069595/4503599627370496), (-1541083403/9007199254740992)), (85/9007199254740992), by norm_num⟩
  | 9 => ⟨((121157799/72057594037927936), (1568110425/144115188075855872)), (89/144115188075855872), by norm_num⟩
  | 10 => ⟨((-110954363/1152921504606846976), (-1436050295/2305843009213693952)), (21/576460752303423488), by norm_num⟩
  | 11 => ⟨((184745855/36893488147419103232), (1195556139/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-140989401/590295810358705651712), (-456196281/295147905179352825856)), (7/73786976294838206464), by norm_num⟩
  | _ => zero

private def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-17545678399/79228162514264337593543950336)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890597291339075/316912650057057350374175801344), (-1332373156471/316912650057057350374175801344)), (5779/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946235199194171/19807040628566084398385987584), (-374712193351/4951760157141521099596496896)), (13005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473103853717255/618970019642690137449562112), (-3184890016485/2475880078570760549798248448)), (3455/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774080999451721/154742504910672534362390528), (-796176472069/38685626227668133590597632)), (13823/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((194032798318353/1208925819614629174706176), (-1492733045093/4835703278458516698824704)), (25923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261158318369059/604462909807314587353088), (-1306043549765/302231454903657293676544)), (22689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891641377399067/75557863725914323419136), (-2122137219699/37778931862957161709568)), (2305/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1300425293956527/4722366482869645213696), (-3182884514677/4722366482869645213696)), (13835/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625414262630563/590295810358705651712), (-4375943874795/590295810358705651712)), (38061/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914214739524517/36893488147419103232), (-1367286500243/18446744073709551616)), (47599/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828227215874519/9223372036854775808), (-3075855455147/4611686018427387904)), (26791/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799735424230993/576460752303423488), (-3075181074459/576460752303423488)), (53621/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199374647082721/144115188075855872), (-5380048376127/144115188075855872)), (11741/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498817275003825/36028797018963968), (-4033516344903/18014398509481984)), (70535/36028797018963968), by norm_num⟩
  | 3 => ⟨((46819167857341/281474976710656), (-5039232320935/4503599627370496)), (44163/4503599627370496), by norm_num⟩
  | 2 => ⟨((561450518655785/1125899906842624), (-10070462451761/2251799813685248)), (88563/2251799813685248), by norm_num⟩
  | 1 => ⟨((280342685434719/281474976710656), (-7542821644045/562949953421312)), (33359/281474976710656), by norm_num⟩
  | 0 => ⟨((558359223271277/562949953421312), (-7522704071267/281474976710656)), (134621/562949953421312), by norm_num⟩
  | _ => zero

private def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558359223271277/562949953421312), (-7522704071267/281474976710656)), (513538362743186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1106807651417541/1125899906842624), (-59690864903421/1125899906842624)), (548485/1125899906842624), by norm_num⟩
  | 2 => ⟨((271218642629799/281474976710656), (-117357334507839/1125899906842624)), (568263/562949953421312), by norm_num⟩
  | 3 => ⟨((1033111453982039/1125899906842624), (-226162178534163/1125899906842624)), (1213579/562949953421312), by norm_num⟩
  | 4 => ⟨((451270108103669/562949953421312), (-415047084880581/1125899906842624)), (2714679/562949953421312), by norm_num⟩
  | 5 => ⟨((570490107779627/1125899906842624), (-332708692351553/562949953421312)), (6353721/562949953421312), by norm_num⟩
  | 6 => ⟨((-52101137977583/562949953421312), (-337164994162109/562949953421312)), (55796161/2251799813685248), by norm_num⟩
  | _ => zero

private def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-1074721093/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound (A_piArg hcre) S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue,J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_piPower,J_piArg,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_piGamma : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1402138993/8796093022208), (14049167/4398046511104)), (715/4398046511104), by norm_num⟩
  | 1 => ⟨((273326987/4398046511104), (509518261/4398046511104)), (3733/8796093022208), by norm_num⟩
  | 2 => ⟨((-503736053/17592186044416), (377830633/8796093022208)), (1243/2199023255552), by norm_num⟩
  | 3 => ⟨((-1777306557/140737488355328), (-112440831/70368744177664)), (36193/70368744177664), by norm_num⟩
  | 4 => ⟨((-179367231/281474976710656), (-586973205/281474976710656)), (100591/281474976710656), by norm_num⟩
  | 5 => ⟨((480863123/2251799813685248), (-184958857/1125899906842624)), (907203/4503599627370496), by norm_num⟩
  | 6 => ⟨((669944615/36028797018963968), (542955437/36028797018963968)), (862427/9007199254740992), by norm_num⟩
  | 7 => ⟨((-156488621/144115188075855872), (633924895/576460752303423488)), (2840041/72057594037927936), by norm_num⟩
  | 8 => ⟨((-9563317/576460752303423488), (-1150179497/9223372036854775808)), (132231667/9223372036854775808), by norm_num⟩
  | 9 => ⟨((1099445039/73786976294838206464), (243032363/73786976294838206464)), (43285985/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-149576107/295147905179352825856), (397962853/295147905179352825856)), (836419387/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-431567539/4722366482869645213696), (-153654033/2361183241434822606848)), (1972675217/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((72716191/9444732965739290427392), (-44860575/9444732965739290427392)), (1328961839/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6440923/68719476736), (1318733491/2199023255552)), (3549/2199023255552), by norm_num⟩
  | 1 => ⟨((-181201609/274877906944), (848704699/549755813888)), (3561/549755813888), by norm_num⟩
  | 2 => ⟨((-953975265/1099511627776), (-243536119/1099511627776)), (6961/549755813888), by norm_num⟩
  | 3 => ⟨((8304655/274877906944), (-432309909/2199023255552)), (71799/4398046511104), by norm_num⟩
  | 4 => ⟨((1430860239/70368744177664), (41768007/70368744177664)), (276581/17592186044416), by norm_num⟩
  | 5 => ⟨((346543905/1125899906842624), (23941261/70368744177664)), (27213649/2251799813685248), by norm_num⟩
  | 6 => ⟨((1233014579/9007199254740992), (284793609/9007199254740992)), (69693075/9007199254740992), by norm_num⟩
  | 7 => ⟨((8443693/72057594037927936), (882323681/72057594037927936)), (153234985/36028797018963968), by norm_num⟩
  | 8 => ⟨((7941513/288230376151711744), (57223763/288230376151711744)), (74039995/36028797018963968), by norm_num⟩
  | 9 => ⟨((-1235957/144115188075855872), (136951241/2305843009213693952)), (64344101/72057594037927936), by norm_num⟩
  | 10 => ⟨((-2858225/1152921504606846976), (341587/576460752303423488)), (1661365839/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-119017/2305843009213693952), (303773/2305843009213693952)), (165704061/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-190029/9223372036854775808), (7521/2305843009213693952)), (148659185/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((100639/1073741824), (643913/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-707819/1073741824), (828813/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-29113/33554432), (-59457/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((4055/134217728), (-211089/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21833/1073741824), (637/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((165/536870912), (365/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((147/1073741824), (17/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨(0, (13/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 9 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 10 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 11 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 12 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨43,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨43,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/1048576)) (K:=(2783767/1073741824)) (L:=(667371651/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiRectangle.Tile043
