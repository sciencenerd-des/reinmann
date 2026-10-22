/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile047Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨47,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37201/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37201/1280))
  have he : value ((69/80), (37201/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-4285475141/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((87598312305539/1125899906842624), (-1158309967203987/9007199254740992)), (87556053/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2936907421/17179869184), (4854330307/17179869184)), (185/8589934592), by norm_num⟩
  | 2 => ⟨((403315323/2147483648), (-5333026929/17179869184)), (205/8589934592), by norm_num⟩
  | 3 => ⟨((-1181565787/8589934592), (3905952613/17179869184)), (303/17179869184), by norm_num⟩
  | 4 => ⟨((2596165387/34359738368), (-1072781885/8589934592)), (335/34359738368), by norm_num⟩
  | 5 => ⟨((-1140871679/34359738368), (1885714179/34359738368)), (297/68719476736), by norm_num⟩
  | 6 => ⟨((1671167529/137438953472), (-2762225027/137438953472)), (55/34359738368), by norm_num⟩
  | 7 => ⟨((-524561481/137438953472), (433516337/68719476736)), (139/274877906944), by norm_num⟩
  | 8 => ⟨((2305158757/2199023255552), (-3810131001/2199023255552)), (77/549755813888), by norm_num⟩
  | 9 => ⟨((-2251089545/8796093022208), (1860380773/4398046511104)), (303/8796093022208), by norm_num⟩
  | 10 => ⟨((989229855/17592186044416), (-1635069743/17592186044416)), (67/8796093022208), by norm_num⟩
  | 11 => ⟨((-3161542037/281474976710656), (5225622437/281474976710656)), (431/281474976710656), by norm_num⟩
  | 12 => ⟨((2315539289/1125899906842624), (-956822171/281474976710656)), (159/562949953421312), by norm_num⟩
  | 13 => ⟨((-1565464565/4503599627370496), (2587511619/4503599627370496)), (433/9007199254740992), by norm_num⟩
  | 14 => ⟨((982764919/18014398509481984), (-3248768071/36028797018963968)), (137/18014398509481984), by norm_num⟩
  | 15 => ⟨((-2303312249/288230376151711744), (3807078961/288230376151711744)), (323/288230376151711744), by norm_num⟩
  | 16 => ⟨((2530447141/2305843009213693952), (-4182503731/2305843009213693952)), (179/1152921504606846976), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-83587189023/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779044518107707/633825300114114700748351602688), (-1583206385191/633825300114114700748351602688)), (23089/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945025993732725/19807040628566084398385987584), (-1780810192929/39614081257132168796771975168)), (12989/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889846348966027/2475880078570760549798248448), (-1891744957595/2475880078570760549798248448)), (6901/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771512491179113/154742504910672534362390528), (-1891333470503/154742504910672534362390528)), (55215/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549855002463715/9671406556917033397649408), (-443172009497/2417851639229258349412352)), (51771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314763112412885/151115727451828646838272), (-775332535679/302231454903657293676544)), (45307/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888220451256117/75557863725914323419136), (-2519011710893/75557863725914323419136)), (73637/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162232571364239/590295810358705651712), (-1888542405233/4722366482869645213696)), (55239/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621889346971099/590295810358705651712), (-1297791102709/295147905179352825856)), (18993/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912012850895523/36893488147419103232), (-3242733250357/73786976294838206464)), (5937/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1823276220755255/9223372036854775808), (-911419416499/2305843009213693952)), (13363/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199315490008229/144115188075855872), (-1821341648687/576460752303423488)), (13369/144115188075855872), by norm_num⟩
  | 5 => ⟨((298762664555319/36028797018963968), (-795995554729/36028797018963968)), (93637/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492340434732121/36028797018963968), (-4769249485505/36028797018963968)), (140563/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490133312482399/9007199254740992), (-743726495789/1125899906842624)), (43973/2251799813685248), by norm_num⟩
  | 2 => ⟨((278711236903491/562949953421312), (-11864441511853/4503599627370496)), (176175/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218692935624439/2251799813685248), (-8854470601837/1125899906842624)), (529947/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185817930096577/2251799813685248), (-35068404957997/2251799813685248)), (1065601/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185817930096577/2251799813685248), (-35068404957997/2251799813685248)), (4064945229537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((530305824864617/562949953421312), (-68081672155065/2251799813685248)), (2101945/2251799813685248), by norm_num⟩
  | 2 => ⟨((998080101251473/1125899906842624), (-16033444487797/281474976710656)), (1021805/562949953421312), by norm_num⟩
  | 3 => ⟨((440559032384095/562949953421312), (-227411503285997/2251799813685248)), (7712057/2251799813685248), by norm_num⟩
  | 4 => ⟨((1356141947369133/2251799813685248), (-355939959606713/2251799813685248)), (1703557/281474976710656), by norm_num⟩
  | 5 => ⟨((760470676017507/2251799813685248), (-428728261752143/2251799813685248)), (10361949/1125899906842624), by norm_num⟩
  | 6 => ⟨((87598312305539/1125899906842624), (-1158309967203987/9007199254740992)), (87556053/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-4285475141/67108864)), (1/33554432), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-66638419/33554432), (-4490970689/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-721858504490133/9007199254740992), (250888170229377/2251799813685248)), (111504511/9007199254740992), by norm_num⟩
  | 1 => ⟨((3170281661/17179869184), (-1101858827/4294967296)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((-1824960823/8589934592), (2537123709/8589934592)), (285/8589934592), by norm_num⟩
  | 3 => ⟨((2801418391/17179869184), (-3894628821/17179869184)), (55/2147483648), by norm_num⟩
  | 4 => ⟨((-3225252113/34359738368), (4483857133/34359738368)), (509/34359738368), by norm_num⟩
  | 5 => ⟨((1485283487/34359738368), (-4129785037/68719476736)), (471/68719476736), by norm_num⟩
  | 6 => ⟨((-2279994411/137438953472), (1584863577/68719476736)), (91/34359738368), by norm_num⟩
  | 7 => ⟨((2999932081/549755813888), (-4170609425/549755813888)), (241/274877906944), by norm_num⟩
  | 8 => ⟨((-3453799445/2199023255552), (4801591545/2199023255552)), (279/1099511627776), by norm_num⟩
  | 9 => ⟨((1767259359/4398046511104), (-4913810273/8796093022208)), (287/4398046511104), by norm_num⟩
  | 10 => ⟨((-813853011/8796093022208), (4525786513/35184372088832)), (531/35184372088832), by norm_num⟩
  | 11 => ⟨((681442113/35184372088832), (-1894728829/70368744177664)), (447/140737488355328), by norm_num⟩
  | 12 => ⟨((-2092104601/562949953421312), (1454258119/281474976710656)), (345/562949953421312), by norm_num⟩
  | 13 => ⟨((2964460841/4503599627370496), (-4121296081/4503599627370496)), (491/4503599627370496), by norm_num⟩
  | 14 => ⟨((-487565953/4503599627370496), (2711324263/18014398509481984)), (325/18014398509481984), by norm_num⟩
  | 15 => ⟨((1197506235/72057594037927936), (-3329629243/144115188075855872)), (201/72057594037927936), by norm_num⟩
  | 16 => ⟨((-2757360005/1152921504606846976), (1916688665/576460752303423488)), (465/1152921504606846976), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (2858399195099/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778899614613593/633825300114114700748351602688), (845815423827/158456325028528675187087900672)), (46267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889888726967189/39614081257132168796771975168), (1902747788241/19807040628566084398385987584)), (52061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889672566174859/2475880078570760549798248448), (2021259285165/1237940039285380274899124224)), (1729/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((110708646896765/9671406556917033397649408), (4041595662629/154742504910672534362390528)), (55341/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193711420658169/1208925819614629174706176), (947003880591/2417851639229258349412352)), (51897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629454443606131/302231454903657293676544), (3313533370865/604462909807314587353088)), (45425/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943993225294593/37778931862957161709568), (2691327128511/37778931862957161709568)), (73843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162210556033145/590295810358705651712), (1008845832851/1180591620717411303424)), (55407/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810823084223183/295147905179352825856), (5546040916319/590295810358705651712)), (76223/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911860107874987/36893488147419103232), (3464317897693/36893488147419103232)), (95339/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822930471890149/9223372036854775808), (973666741681/1152921504606846976)), (107337/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594175579582513/1152921504606846976), (7782610668803/1152921504606846976)), (107439/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194742951207893/144115188075855872), (1700556336749/36028797018963968)), (23531/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491873072209787/36028797018963968), (10188231759953/36028797018963968)), (17677/4503599627370496), by norm_num⟩
  | 3 => ⟨((372384748042241/2251799813685248), (12708880117213/9007199254740992)), (177173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114235524100161/2251799813685248), (12669318520581/2251799813685248)), (177779/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108394827773469/1125899906842624), (4726314662171/281474976710656)), (268185/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090857180033081/1125899906842624), (18708375509009/562949953421312)), (271229/562949953421312), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090857180033081/1125899906842624), (18708375509009/562949953421312)), (1034656526805686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((527830834139645/562949953421312), (9063046202743/140737488355328)), (271801/281474976710656), by norm_num⟩
  | 2 => ⟨((246284031892849/281474976710656), (33990625333331/281474976710656)), (2178785/1125899906842624), by norm_num⟩
  | 3 => ⟨((1691104834971127/2251799813685248), (475856055212033/2251799813685248)), (1084747/281474976710656), by norm_num⟩
  | 4 => ⟨((1169463005359701/2251799813685248), (714737136781591/2251799813685248)), (16702049/2251799813685248), by norm_num⟩
  | 5 => ⟨((760986426060659/4503599627370496), (742391605988135/2251799813685248)), (13975489/1125899906842624), by norm_num⟩
  | 6 => ⟨((-721858504490133/9007199254740992), (250888170229377/2251799813685248)), (111504511/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-4490970689/67108864)), (1/33554432), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-4676864025/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((477564902169495/4503599627370496), (-619871678917873/9007199254740992)), (884769/140737488355328), by norm_num⟩
  | 1 => ⟨((-8532037/33554432), (2835058915/17179869184)), (261/17179869184), by norm_num⟩
  | 2 => ⟨((327342899/1073741824), (-1699543593/8589934592)), (79/4294967296), by norm_num⟩
  | 3 => ⟨((-2093157307/8589934592), (339610629/2147483648)), (255/17179869184), by norm_num⟩
  | 4 => ⟨((1254793003/8589934592), (-407175361/4294967296)), (309/34359738368), by norm_num⟩
  | 5 => ⟨((-300886221/4294967296), (3124364395/68719476736)), (299/68719476736), by norm_num⟩
  | 6 => ⟨((3847966117/137438953472), (-1248649769/68719476736)), (241/137438953472), by norm_num⟩
  | 7 => ⟨((-2636291361/274877906944), (213866527/34359738368)), (167/274877906944), by norm_num⟩
  | 8 => ⟨((24693557/8589934592), (-256414767/137438953472)), (101/549755813888), by norm_num⟩
  | 9 => ⟨((-3368536951/4398046511104), (2186153805/4398046511104)), (217/4398046511104), by norm_num⟩
  | 10 => ⟨((807739883/4398046511104), (-1048433575/8796093022208)), (105/8796093022208), by norm_num⟩
  | 11 => ⟨((-2817273669/70368744177664), (1828388301/70368744177664)), (185/70368744177664), by norm_num⟩
  | 12 => ⟨((4503684809/562949953421312), (-91339243/17592186044416)), (149/281474976710656), by norm_num⟩
  | 13 => ⟨((-3322881389/2251799813685248), (2156523707/2251799813685248)), (111/1125899906842624), by norm_num⟩
  | 14 => ⟨((4553098043/18014398509481984), (-2954924573/18014398509481984)), (153/9007199254740992), by norm_num⟩
  | 15 => ⟨((-2911427273/72057594037927936), (472373311/18014398509481984)), (197/72057594037927936), by norm_num⟩
  | 16 => ⟨((218165553/36028797018963968), (-2265403459/576460752303423488)), (119/288230376151711744), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-749869680363/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778778583399151/633825300114114700748351602688), (-887441204453/633825300114114700748351602688)), (46145/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944876457745465/19807040628566084398385987584), (-249547744911/9903520314283042199192993792)), (51915/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889528717084941/2475880078570760549798248448), (-1060354198901/2475880078570760549798248448)), (55163/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771195007822121/154742504910672534362390528), (-16564103259/2417851639229258349412352)), (27583/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774778759777537/4835703278458516698824704), (-993578963179/9671406556917033397649408)), (51723/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258792309768145/604462909807314587353088), (-217278613273/151115727451828646838272)), (45261/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887798019397951/75557863725914323419136), (-1411810296205/75557863725914323419136)), (18389/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297544005377907/4722366482869645213696), (-1058419815103/4722366482869645213696)), (27587/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621454488884437/590295810358705651712), (-363654003887/147573952589676412928)), (75875/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911741378967989/36893488147419103232), (-1817203819019/73786976294838206464)), (94859/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822666272585749/9223372036854775808), (-510722329527/2305843009213693952)), (106737/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49809845318107/36028797018963968), (-1020529832469/576460752303423488)), (26691/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194519108351969/144115188075855872), (-1783871003331/144115188075855872)), (93449/144115188075855872), by norm_num⟩
  | 4 => ⟨((745772764014363/18014398509481984), (-667924870711/9007199254740992)), (70117/18014398509481984), by norm_num⟩
  | 3 => ⟨((372285975188963/2251799813685248), (-1666224582093/4503599627370496)), (175399/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227723696721057/4503599627370496), (-207606908615/140737488355328)), (175559/2251799813685248), by norm_num⟩
  | 1 => ⟨((2215775060553377/2251799813685248), (-1238950902067/281474976710656)), (263741/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180107035569051/2251799813685248), (-19610126306051/2251799813685248)), (33069/70368744177664), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2180107035569051/2251799813685248), (-19610126306051/2251799813685248)), (126148224145388581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((263815754213633/281474976710656), (-18985779316791/1125899906842624)), (1033733/1125899906842624), by norm_num⟩
  | 2 => ⟨((123592200354479/140737488355328), (-71178585724749/2251799813685248)), (1972621/1125899906842624), by norm_num⟩
  | 3 => ⟨((1734320153259545/2251799813685248), (-62507283103071/1125899906842624)), (7178645/2251799813685248), by norm_num⟩
  | 4 => ⟨((332205124768781/562949953421312), (-96285327099071/1125899906842624)), (5927483/1125899906842624), by norm_num⟩
  | 5 => ⟨((1535376680820343/4503599627370496), (-227277603687169/2251799813685248)), (32038445/4503599627370496), by norm_num⟩
  | 6 => ⟨((477564902169495/4503599627370496), (-619871678917873/9007199254740992)), (884769/140737488355328), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-4676864025/67108864)), (1/33554432), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-17978733/8388608), (-302910709/4194304)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-527797288170973/4503599627370496), (-39170175550073/9007199254740992)), (21532585/2251799813685248), by norm_num⟩
  | 1 => ⟨((5003078427/17179869184), (92825155/8589934592)), (205/8589934592), by norm_num⟩
  | 2 => ⟨((-3108045713/8589934592), (-230661845/17179869184)), (511/17179869184), by norm_num⟩
  | 3 => ⟨((5148802307/17179869184), (191057717/17179869184)), (213/8589934592), by norm_num⟩
  | 4 => ⟨((-6397146545/34359738368), (-29672537/4294967296)), (133/8589934592), by norm_num⟩
  | 5 => ⟨((6358524795/68719476736), (117973575/34359738368)), (531/68719476736), by norm_num⟩
  | 6 => ⟨((-2633390091/68719476736), (-195435547/137438953472)), (221/68719476736), by norm_num⟩
  | 7 => ⟨((233704591/17179869184), (69377013/137438953472)), (315/274877906944), by norm_num⟩
  | 8 => ⟨((-2322936369/549755813888), (-172395401/1099511627776)), (393/1099511627776), by norm_num⟩
  | 9 => ⟨((2565457791/2199023255552), (95196995/2199023255552)), (109/1099511627776), by norm_num⟩
  | 10 => ⟨((-5099938499/17592186044416), (-189244517/17592186044416)), (109/4398046511104), by norm_num⟩
  | 11 => ⟨((576039595/8796093022208), (171001803/70368744177664)), (99/17592186044416), by norm_num⟩
  | 12 => ⟨((-3817078987/281474976710656), (-283282345/562949953421312)), (329/281474976710656), by norm_num⟩
  | 13 => ⟨((2918487679/1125899906842624), (108296951/1125899906842624)), (505/2251799813685248), by norm_num⟩
  | 14 => ⟨((-4144096823/9007199254740992), (-76887947/4503599627370496)), (45/1125899906842624), by norm_num⟩
  | 15 => ⟨((5492103335/72057594037927936), (101898331/36028797018963968)), (479/72057594037927936), by norm_num⟩
  | 16 => ⟨((-6823682049/576460752303423488), (-7912745/18014398509481984)), (597/576460752303423488), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-2021980533863/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778651059725549/633825300114114700748351602688), (-2392637873495/316912650057057350374175801344)), (181/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((236201101219491/4951760157141521099596496896), (-672799148713/4951760157141521099596496896)), (52143/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944687382440589/1237940039285380274899124224), (-2858769273669/1237940039285380274899124224)), (13855/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442760027882725/38685626227668133590597632), (-5716127524741/154742504910672534362390528)), (55439/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387352825465901/2417851639229258349412352), (-334835655981/604462909807314587353088)), (12999/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157332920953507/75557863725914323419136), (-4686200296213/604462909807314587353088)), (45517/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887586611918627/75557863725914323419136), (-7612265431663/75557863725914323419136)), (74005/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648691904719797/2361183241434822606848), (-5706740645317/4722366482869645213696)), (27769/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621231556952321/590295810358705651712), (-7842774126895/590295810358705651712)), (19105/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911600052261305/36893488147419103232), (-9797477470763/73786976294838206464)), (95609/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911171405939973/4611686018427387904), (-1376740950721/1152921504606846976)), (26919/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593584757797139/1152921504606846976), (-5501818683787/576460752303423488)), (26955/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194222434523437/144115188075855872), (-4808305123009/72057594037927936)), (94505/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491085225350619/36028797018963968), (-7200890339137/18014398509481984)), (35521/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488541860496359/9007199254740992), (-8980881613975/4503599627370496)), (178175/9007199254740992), by norm_num⟩
  | 2 => ⟨((556610006411803/1125899906842624), (-17901115763449/2251799813685248)), (179033/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106825978725779/1125899906842624), (-26700218901127/1125899906842624)), (67675/281474976710656), by norm_num⟩
  | 0 => ⟨((543769674219419/562949953421312), (-3299725786599/70368744177664)), (550037/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((543769674219419/562949953421312), (-3299725786599/70368744177664)), (2098224644187545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524005042776603/562949953421312), (-50996812205777/562949953421312)), (1114179/1125899906842624), by norm_num⟩
  | 2 => ⟨((966269233516067/1125899906842624), (-23734424880003/140737488355328)), (2276065/1125899906842624), by norm_num⟩
  | 3 => ⟨((1594499757969315/2251799813685248), (-325909532772715/1125899906842624)), (4674413/1125899906842624), by norm_num⟩
  | 4 => ⟨((470193080904943/1125899906842624), (-923106340035649/2251799813685248)), (9326071/1125899906842624), by norm_num⟩
  | 5 => ⟨((14300035959599/2251799813685248), (-385503375021521/1125899906842624)), (30871419/2251799813685248), by norm_num⟩
  | 6 => ⟨((-527797288170973/4503599627370496), (-39170175550073/9007199254740992)), (21532585/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-302910709/4194304)), (1/33554432), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-148462847/67108864), (-5002686945/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((648884622404773/9007199254740992), (742200417964619/9007199254740992)), (29206221/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1587253757/8589934592), (-1815515981/8589934592)), (9/536870912), by norm_num⟩
  | 2 => ⟨((127225797/536870912), (1164176637/4294967296)), (93/4294967296), by norm_num⟩
  | 3 => ⟨((-435103635/2147483648), (-3981405489/17179869184)), (5/268435456), by norm_num⟩
  | 4 => ⟨((1116018789/8589934592), (2553025863/17179869184)), (207/17179869184), by norm_num⟩
  | 5 => ⟨((-2290025341/34359738368), (-2619352819/34359738368)), (107/17179869184), by norm_num⟩
  | 6 => ⟨((1957933009/68719476736), (4479004887/137438953472)), (23/8589934592), by norm_num⟩
  | 7 => ⟨((-1434856861/137438953472), (-820601479/68719476736)), (17/17179869184), by norm_num⟩
  | 8 => ⟨((230020949/68719476736), (4209602473/1099511627776)), (11/34359738368), by norm_num⟩
  | 9 => ⟨((-2097749637/2199023255552), (-2399426035/2199023255552)), (101/1099511627776), by norm_num⟩
  | 10 => ⟨((2152248633/8796093022208), (2461762507/8796093022208)), (209/8796093022208), by norm_num⟩
  | 11 => ⟨((-2007421363/35184372088832), (-2296107695/35184372088832)), (197/35184372088832), by norm_num⟩
  | 12 => ⟨((3432622757/281474976710656), (1963133319/140737488355328)), (339/281474976710656), by norm_num⟩
  | 13 => ⟨((-2709078011/1125899906842624), (-3098669259/1125899906842624)), (135/562949953421312), by norm_num⟩
  | 14 => ⟨((3970655945/9007199254740992), (283854633/562949953421312)), (199/4503599627370496), by norm_num⟩
  | 15 => ⟨((-678968761/9007199254740992), (-1553221885/18014398509481984)), (137/18014398509481984), by norm_num⟩
  | 16 => ⟨((1741520487/144115188075855872), (995983869/72057594037927936)), (177/144115188075855872), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039973471/10141204801825835211973625643008), (138789870959/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778555988530627/633825300114114700748351602688), (1313706266247/633825300114114700748351602688)), (46165/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472375628714119/9903520314283042199192993792), (738817241447/19807040628566084398385987584)), (12985/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889262687445099/2475880078570760549798248448), (196204047763/309485009821345068724781056)), (55191/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885464500930583/77371252455336267181195264), (1569233995423/154742504910672534362390528)), (55197/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387327041033581/2417851639229258349412352), (1470733720995/9671406556917033397649408)), (51753/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314643537238147/151115727451828646838272), (643234504667/302231454903657293676544)), (22645/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((58982611103181/2361183241434822606848), (522429836757/18889465931478580854784)), (36803/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297278198652359/4722366482869645213696), (195824517687/590295810358705651712)), (27607/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101318066991529/36893488147419103232), (1076471789885/295147905179352825856)), (37967/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227878260946431/9223372036854775808), (2689491368485/73786976294838206464)), (94941/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822152657289299/9223372036854775808), (3023358374475/9223372036854775808)), (13355/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593401608629787/1152921504606846976), (3020461700065/1152921504606846976)), (106879/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298517510672617/36028797018963968), (2639648792841/144115188075855872)), (93565/144115188075855872), by norm_num⟩
  | 4 => ⟨((93179520093523/2251799813685248), (1976485849895/18014398509481984)), (35109/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488303079799191/9007199254740992), (4929857015531/9007199254740992)), (175703/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226044121520809/4503599627370496), (1228215131923/562949953421312)), (175939/2251799813685248), by norm_num⟩
  | 1 => ⟨((138328805138019/140737488355328), (14653878007765/2251799813685248)), (529005/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175099521692641/2251799813685248), (28970609964181/2251799813685248)), (531393/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175099521692641/2251799813685248), (28970609964181/2251799813685248)), (2027103428367232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2100639055158497/2251799813685248), (55967639301921/2251799813685248)), (2080519/2251799813685248), by norm_num⟩
  | 2 => ⟨((244779311453955/281474976710656), (104421190754279/2251799813685248)), (1992567/1125899906842624), by norm_num⟩
  | 3 => ⟨((26532793595111/35184372088832), (181615768994693/2251799813685248)), (7300791/2251799813685248), by norm_num⟩
  | 4 => ⟨((316475203082395/562949953421312), (68478893131691/562949953421312)), (380901/70368744177664), by norm_num⟩
  | 5 => ⟨((678335221675053/2251799813685248), (2406061084893/17592186044416)), (16669833/2251799813685248), by norm_num⟩
  | 6 => ⟨((648884622404773/9007199254740992), (742200417964619/9007199254740992)), (29206221/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148462847/67108864), (-5002686945/67108864)), (1/33554432), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-2386755/1048576), (-2573613707/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((246101647810533/9007199254740992), (-891467721701439/9007199254740992)), (8499113/1125899906842624), by norm_num⟩
  | 1 => ⟨((-619388921/8589934592), (2243647027/8589934592)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((204325359/2147483648), (-5921113131/17179869184)), (57/2147483648), by norm_num⟩
  | 3 => ⟨((-1437936897/17179869184), (2604359501/8589934592)), (403/17179869184), by norm_num⟩
  | 4 => ⟨((948699477/17179869184), (-3436527015/17179869184)), (67/4294967296), by norm_num⟩
  | 5 => ⟨((-1001468923/34359738368), (3627676723/34359738368)), (285/34359738368), by norm_num⟩
  | 6 => ⟨((880977967/68719476736), (-3191215615/68719476736)), (63/17179869184), by norm_num⟩
  | 7 => ⟨((-1328543635/274877906944), (4812457691/274877906944)), (191/137438953472), by norm_num⟩
  | 8 => ⟨((1753051409/1099511627776), (-6350175871/1099511627776)), (253/549755813888), by norm_num⟩
  | 9 => ⟨((-1028089593/2199023255552), (3724106261/2199023255552)), (299/2199023255552), by norm_num⟩
  | 10 => ⟨((542637475/4398046511104), (-3931251969/8796093022208)), (159/4398046511104), by norm_num⟩
  | 11 => ⟨((-1041491931/35184372088832), (3772654299/35184372088832)), (307/35184372088832), by norm_num⟩
  | 12 => ⟨((458092819/70368744177664), (-6637500653/281474976710656)), (271/140737488355328), by norm_num⟩
  | 13 => ⟨((-1487917799/1125899906842624), (5389767615/1125899906842624)), (443/1125899906842624), by norm_num⟩
  | 14 => ⟨((140239299/562949953421312), (-4063973065/4503599627370496)), (21/281474976710656), by norm_num⟩
  | 15 => ⟨((-1579091413/36028797018963968), (2860015441/18014398509481984)), (475/36028797018963968), by norm_num⟩
  | 16 => ⟨((32557131/4503599627370496), (-943468089/36028797018963968)), (315/144115188075855872), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-847636567813/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111153515705149/39614081257132168796771975168), (-250700026339/79228162514264337593543950336)), (5775/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889390263542241/39614081257132168796771975168), (-1127925793965/19807040628566084398385987584)), (51981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472285839264997/618970019642690137449562112), (-1198142850525/1237940039285380274899124224)), (55237/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442702400069425/38685626227668133590597632), (-598914933883/38685626227668133590597632)), (55245/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774598074783669/4835703278458516698824704), (-1122633060095/4835703278458516698824704)), (51801/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258476060698029/604462909807314587353088), (-1963943205595/604462909807314587353088)), (45335/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943642010233511/37778931862957161709568), (-797540496153/18889465931478580854784)), (73685/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297158423939913/4722366482869645213696), (-2391531972809/4722366482869645213696)), (55279/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620924181101309/590295810358705651712), (-3286586924151/590295810358705651712)), (76031/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822819673831711/73786976294838206464), (-1026395241121/18446744073709551616)), (47537/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910960014887125/4611686018427387904), (-2307566880691/4611686018427387904)), (53503/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796584233646707/576460752303423488), (-2305290834085/576460752303423488)), (107067/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596932733844743/72057594037927936), (-4029143262875/144115188075855872)), (11719/18014398509481984), by norm_num⟩
  | 4 => ⟨((745282155308323/18014398509481984), (-3016748503879/18014398509481984)), (140765/36028797018963968), by norm_num⟩
  | 3 => ⟨((185989508269533/1125899906842624), (-7524020312609/9007199254740992)), (176195/9007199254740992), by norm_num⟩
  | 2 => ⟨((34769752069787/70368744177664), (-7497304509925/2251799813685248)), (176555/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212076127960333/2251799813685248), (-22358758025581/2251799813685248)), (531471/2251799813685248), by norm_num⟩
  | 0 => ⟨((1086335864500347/1125899906842624), (-44187428567321/2251799813685248)), (133775/281474976710656), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086335864500347/1125899906842624), (-44187428567321/2251799813685248)), (510311127782726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((65483034455353/70368744177664), (-85269370964497/2251799813685248)), (2107189/2251799813685248), by norm_num⟩
  | 2 => ⟨((1946740370280779/2251799813685248), (-79349109069745/1125899906842624)), (4081361/2251799813685248), by norm_num⟩
  | 3 => ⟨((417955997016361/562949953421312), (-274397596150573/2251799813685248)), (7632167/2251799813685248), by norm_num⟩
  | 4 => ⟨((1207790048550909/2251799813685248), (-203723475205929/1125899906842624)), (1649113/281474976710656), by norm_num⟩
  | 5 => ⟨((287046782782837/1125899906842624), (-218540906269319/1125899906842624)), (37853573/4503599627370496), by norm_num⟩
  | 6 => ⟨((246101647810533/9007199254740992), (-891467721701439/9007199254740992)), (8499113/1125899906842624), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-2573613707/33554432)), (1/33554432), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-5281791373/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-859550907890861/9007199254740992), (71567237860433/4503599627370496)), (37002769/4503599627370496), by norm_num⟩
  | 1 => ⟨((4439748781/17179869184), (-23103675/536870912)), (3/134217728), by norm_num⟩
  | 2 => ⟨((-3005765645/8589934592), (250263647/4294967296)), (261/8589934592), by norm_num⟩
  | 3 => ⟨((2713254753/8589934592), (-903635359/17179869184)), (237/8589934592), by norm_num⟩
  | 4 => ⟨((-1793855/8388608), (611772479/17179869184)), (161/8589934592), by norm_num⟩
  | 5 => ⟨((3979550223/34359738368), (-331342117/17179869184)), (175/17179869184), by norm_num⟩
  | 6 => ⟨((-7184547855/137438953472), (1196388115/137438953472)), (635/137438953472), by norm_num⟩
  | 7 => ⟨((5558890361/274877906944), (-115709967/34359738368)), (493/274877906944), by norm_num⟩
  | 8 => ⟨((-940859635/137438953472), (626696799/549755813888)), (335/549755813888), by norm_num⟩
  | 9 => ⟨((4529591331/2199023255552), (-754278397/2199023255552)), (405/2199023255552), by norm_num⟩
  | 10 => ⟨((-2453272143/4398046511104), (408524753/4398046511104)), (55/1099511627776), by norm_num⟩
  | 11 => ⟨((2415848771/17592186044416), (-804585847/35184372088832)), (435/35184372088832), by norm_num⟩
  | 12 => ⟨((-4361493167/140737488355328), (45392893/8796093022208)), (197/70368744177664), by norm_num⟩
  | 13 => ⟨((7268395353/1125899906842624), (-605175301/562949953421312)), (659/1125899906842624), by norm_num⟩
  | 14 => ⟨((-5623765571/4503599627370496), (29265091/140737488355328)), (1/8796093022208), by norm_num⟩
  | 15 => ⟨((4061183863/18014398509481984), (-42267379/1125899906842624)), (93/4503599627370496), by norm_num⟩
  | 16 => ⟨((-5498944889/144115188075855872), (457848737/72057594037927936)), (253/72057594037927936), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1938666727917/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222294429597045/79228162514264337593543950336), (4586645467525/633825300114114700748351602688)), (23163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944638180430455/19807040628566084398385987584), (5158898406537/39614081257132168796771975168)), (52131/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29515963942005/38685626227668133590597632), (2740010179627/1237940039285380274899124224)), (55407/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770687212598415/154742504910672534362390528), (342409226257/9671406556917033397649408)), (27713/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549080643595385/9671406556917033397649408), (2567286934725/4835703278458516698824704)), (25991/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258374226087261/604462909807314587353088), (280699244013/37778931862957161709568)), (711/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1887117102668195/75557863725914323419136), (1823812008213/18889465931478580854784)), (36991/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297031979956877/4722366482869645213696), (5468870875215/4722366482869645213696)), (55519/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((3165523989755/1152921504606846976), (469720640931/36893488147419103232)), (9549/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911298374263137/36893488147419103232), (9388164068941/73786976294838206464)), (95571/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821665048991939/9223372036854775808), (10553095878387/9223372036854775808)), (26907/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398227065007547/288230376151711744), (2635591251981/288230376151711744)), (107767/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193631921357099/144115188075855872), (2303126010569/36028797018963968)), (94453/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490202298147663/36028797018963968), (6897321318709/18014398509481984)), (141991/36028797018963968), by norm_num⟩
  | 3 => ⟨((185930396368057/1125899906842624), (8600571850745/4503599627370496)), (44509/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112128767376443/2251799813685248), (8568991154321/1125899906842624)), (178859/2251799813685248), by norm_num⟩
  | 1 => ⟨((276301921319235/281474976710656), (25549343874361/1125899906842624)), (16897/70368744177664), by norm_num⟩
  | 0 => ⟨((1084376844927999/1125899906842624), (50469819849859/1125899906842624)), (4289/8796093022208), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084376844927999/1125899906842624), (50469819849859/1125899906842624)), (16361236605820057/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((1042122778383291/1125899906842624), (48608498571023/562949953421312)), (553355/562949953421312), by norm_num⟩
  | 2 => ⟨((29880785087699/35184372088832), (22495793487509/140737488355328)), (2239843/1125899906842624), by norm_num⟩
  | 3 => ⟨((97910801988259/140737488355328), (305677517907277/1125899906842624)), (4520475/1125899906842624), by norm_num⟩
  | 4 => ⟨((461940587460875/1125899906842624), (850637062742461/2251799813685248)), (17488711/2251799813685248), by norm_num⟩
  | 5 => ⟨((14429903146115/562949953421312), (349004189529763/1125899906842624)), (13781881/1125899906842624), by norm_num⟩
  | 6 => ⟨((-859550907890861/9007199254740992), (71567237860433/4503599627370496)), (37002769/4503599627370496), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-5281791373/67108864)), (1/33554432), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile047Terms1
