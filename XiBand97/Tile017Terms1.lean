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
namespace Reinmann.XiBand97.Tile017Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53817/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53817/2560))
  have he : value ((69/80), (53817/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-774950323/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-805817226477503/9007199254740992), (-271965334881811/2251799813685248)), (122058253/4503599627370496), by norm_num⟩
  | 1 => ⟨((422134737/2147483648), (1139772259/4294967296)), (129/2147483648), by norm_num⟩
  | 2 => ⟨((-231881205/1073741824), (-626083905/2147483648)), (9/134217728), by norm_num⟩
  | 3 => ⟨((679326777/4294967296), (917097963/4294967296)), (213/4294967296), by norm_num⟩
  | 4 => ⟨((-746316745/8589934592), (-251883773/2147483648)), (237/8589934592), by norm_num⟩
  | 5 => ⟨((327965099/8589934592), (885512347/17179869184)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((-480408651/34359738368), (-324278249/17179869184)), (39/8589934592), by norm_num⟩
  | 7 => ⟨((603180397/137438953472), (814299587/137438953472)), (99/68719476736), by norm_num⟩
  | 8 => ⟨((-662661397/549755813888), (-894599533/549755813888)), (55/137438953472), by norm_num⟩
  | 9 => ⟨((647118181/2199023255552), (218404009/549755813888)), (217/2199023255552), by norm_num⟩
  | 10 => ⟨((-568745589/8796093022208), (-383906125/4398046511104)), (193/8796093022208), by norm_num⟩
  | 11 => ⟨((113605617/8796093022208), (306737445/17592186044416)), (311/70368744177664), by norm_num⟩
  | 12 => ⟨((-665645477/281474976710656), (-898628071/281474976710656)), (115/140737488355328), by norm_num⟩
  | 13 => ⟨((450022339/1125899906842624), (37970917/70368744177664)), (157/1125899906842624), by norm_num⟩
  | 14 => ⟨((-282514327/4503599627370496), (-381397175/4503599627370496)), (25/1125899906842624), by norm_num⟩
  | 15 => ⟨((82766323/9007199254740992), (446941465/36028797018963968)), (237/72057594037927936), by norm_num⟩
  | 16 => ⟨((-181856199/144115188075855872), (-245507693/144115188075855872)), (263/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-44947054039/158456325028528675187087900672)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444759913844931/158456325028528675187087900672), (-3405328676887/633825300114114700748351602688)), (11567/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945023119987085/19807040628566084398385987584), (-1915172738027/19807040628566084398385987584)), (26031/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889839884653299/2475880078570760549798248448), (-4068953877827/2475880078570760549798248448)), (1729/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((442876406210403/38685626227668133590597632), (-4068067265235/154742504910672534362390528)), (27671/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549848138369719/9671406556917033397649408), (-1906435593087/4835703278458516698824704)), (103797/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629523008473235/302231454903657293676544), (-3335320582493/604462909807314587353088)), (22713/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888209198786841/75557863725914323419136), (-5418130609345/75557863725914323419136)), (73845/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648925716373915/2361183241434822606848), (-4062053647489/4722366482869645213696)), (110817/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621875647532879/590295810358705651712), (-5582814938543/590295810358705651712)), (38113/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456001719437551/18446744073709551616), (-6974756616839/73786976294838206464)), (47671/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823252709723751/9223372036854775808), (-3920715145463/4611686018427387904)), (214683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594497496290189/1152921504606846976), (-7834969550195/1152921504606846976)), (214889/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597512133544257/72057594037927936), (-1712083499093/36028797018963968)), (188259/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492294323625843/36028797018963968), (-80140486049/281474976710656)), (282851/36028797018963968), by norm_num⟩
  | 3 => ⟨((372516073099771/2251799813685248), (-12797092285053/9007199254740992)), (354375/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114758928622145/2251799813685248), (-6379529435709/1125899906842624)), (177797/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109175196582959/1125899906842624), (-19043661811669/1125899906842624)), (268221/562949953421312), by norm_num⟩
  | 0 => ⟨((273099743515425/281474976710656), (-37708561474025/1125899906842624)), (271283/281474976710656), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((273099743515425/281474976710656), (-37708561474025/1125899906842624)), (1034862519384288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((529315961249661/562949953421312), (-36586550560329/562949953421312)), (2178375/1125899906842624), by norm_num⟩
  | 2 => ⟨((990627353131931/1125899906842624), (-34400651533861/281474976710656)), (4379601/1125899906842624), by norm_num⟩
  | 3 => ⟨((1709580167311325/2251799813685248), (-484280723966927/2251799813685248)), (4388665/562949953421312), by norm_num⟩
  | 4 => ⟨((1193772427069767/2251799813685248), (-367668882497187/1125899906842624)), (34205957/2251799813685248), by norm_num⟩
  | 5 => ⟨((196369804640355/1125899906842624), (-389833031825667/1125899906842624)), (58608285/2251799813685248), by norm_num⟩
  | 6 => ⟨((-805817226477503/9007199254740992), (-271965334881811/2251799813685248)), (122058253/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-774950323/16777216)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-66638419/33554432), (-1624220919/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-88116263797827/2251799813685248), (148111342658915/1125899906842624)), (213190537/9007199254740992), by norm_num⟩
  | 1 => ⟨((193495937/2147483648), (-1300960425/4294967296)), (237/4294967296), by norm_num⟩
  | 2 => ⟨((-111385215/1073741824), (1497786041/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((5343207/67108864), (-574796635/2147483648)), (107/2147483648), by norm_num⟩
  | 4 => ⟨((-393702041/8589934592), (1323518163/8589934592)), (249/8589934592), by norm_num⟩
  | 5 => ⟨((90653245/4294967296), (-1219005277/17179869184)), (29/2147483648), by norm_num⟩
  | 6 => ⟨((-278315747/34359738368), (467810563/17179869184)), (181/34359738368), by norm_num⟩
  | 7 => ⟨((366197537/137438953472), (-153881947/17179869184)), (15/8589934592), by norm_num⟩
  | 8 => ⟨((-421600495/549755813888), (1417305109/549755813888)), (279/549755813888), by norm_num⟩
  | 9 => ⟨((53931723/274877906944), (-1450429163/2199023255552)), (9/68719476736), by norm_num⟩
  | 10 => ⟨((-397383621/8796093022208), (333973657/2199023255552)), (67/2199023255552), by norm_num⟩
  | 11 => ⟨((83182691/8796093022208), (-1118549475/35184372088832)), (227/35184372088832), by norm_num⟩
  | 12 => ⟨((-255380299/140737488355328), (858518449/140737488355328)), (11/8796093022208), by norm_num⟩
  | 13 => ⟨((90466903/281474976710656), (-1216499559/1125899906842624)), (251/1125899906842624), by norm_num⟩
  | 14 => ⟨((-238065991/4503599627370496), (200078125/1125899906842624)), (333/9007199254740992), by norm_num⟩
  | 15 => ⟨((292355841/36028797018963968), (-982820071/36028797018963968)), (103/18014398509481984), by norm_num⟩
  | 16 => ⟨((-336587101/288230376151711744), (565756711/144115188075855872)), (15/18014398509481984), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (1211381290079/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889450669707169/316912650057057350374175801344), (2867632991335/633825300114114700748351602688)), (46241/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944945382566333/19807040628566084398385987584), (1612759556521/19807040628566084398385987584)), (104061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889674858509123/2475880078570760549798248448), (3426418991085/2475880078570760549798248448)), (55293/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885670392605875/77371252455336267181195264), (1712818600217/77371252455336267181195264)), (55305/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96855862455919/604462909807314587353088), (3210704402199/9671406556917033397649408)), (103721/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258911168228721/604462909807314587353088), (1404268040193/302231454903657293676544)), (45391/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887990440596401/75557863725914323419136), (2281157400003/37778931862957161709568)), (73783/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162210961060715/590295810358705651712), (1710187369595/2361183241434822606848)), (27679/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810825512936401/295147905179352825856), (2350401929193/295147905179352825856)), (152301/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823726889993771/73786976294838206464), (1468172279161/18446744073709551616)), (190477/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822938807622257/9223372036854775808), (825277305491/1152921504606846976)), (214425/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594184947562247/1152921504606846976), (3298262926967/576460752303423488)), (107299/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194752307048007/144115188075855872), (720695083441/18014398509481984)), (2937/2251799813685248), by norm_num⟩
  | 4 => ⟨((1491889417640561/36028797018963968), (4317776931101/18014398509481984)), (141171/18014398509481984), by norm_num⟩
  | 3 => ⟨((372390863949521/2251799813685248), (5386045655299/4503599627370496)), (353611/9007199254740992), by norm_num⟩
  | 2 => ⟨((557133004185407/1125899906842624), (335581803759/70368744177664)), (354637/2251799813685248), by norm_num⟩
  | 1 => ⟨((2216911022147813/2251799813685248), (500763368787/35184372088832)), (534527/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091037807625159/1125899906842624), (495562047487/17592186044416)), (1079375/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091037807625159/1125899906842624), (495562047487/17592186044416)), (4117488865378951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2112723498101865/2251799813685248), (122935700763367/2251799813685248)), (1076359/562949953421312), by norm_num⟩
  | 2 => ⟨((987762625672595/1125899906842624), (230685820453389/2251799813685248)), (8549151/2251799813685248), by norm_num⟩
  | 3 => ⟨((854757169698011/1125899906842624), (404765699564671/2251799813685248)), (4188035/562949953421312), by norm_num⟩
  | 4 => ⟨((1225066272894777/2251799813685248), (614577515546581/2251799813685248)), (7864535/562949953421312), by norm_num⟩
  | 5 => ⟨((124687132881817/562949953421312), (668707921370155/2251799813685248)), (51400461/2251799813685248), by norm_num⟩
  | 6 => ⟨((-88116263797827/2251799813685248), (148111342658915/1125899906842624)), (213190537/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1624220919/33554432)), (1/16777216), by norm_num⟩, -8, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-211431473/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1126908040786567/9007199254740992), (-163070871315711/9007199254740992)), (40205593/4503599627370496), by norm_num⟩
  | 1 => ⟨((-40266029/134217728), (93228071/2147483648)), (47/2147483648), by norm_num⟩
  | 2 => ⟨((772429765/2147483648), (-223551151/4294967296)), (115/4294967296), by norm_num⟩
  | 3 => ⟨((-308700947/1073741824), (178684083/4294967296)), (47/2147483648), by norm_num⟩
  | 4 => ⟨((1480465083/8589934592), (-214232859/8589934592)), (115/8589934592), by norm_num⟩
  | 5 => ⟨((-710000045/8589934592), (12842699/1073741824)), (7/1073741824), by norm_num⟩
  | 6 => ⟨((567501917/17179869184), (-164242385/34359738368)), (23/8589934592), by norm_num⟩
  | 7 => ⟨((-48600363/4294967296), (225049165/137438953472)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((1864617291/549755813888), (-67455541/137438953472)), (39/137438953472), by norm_num⟩
  | 9 => ⟨((-496795221/549755813888), (71889477/549755813888)), (85/1099511627776), by norm_num⟩
  | 10 => ⟨((476505165/2199023255552), (-68953375/2199023255552)), (21/1099511627776), by norm_num⟩
  | 11 => ⟨((-1661977429/35184372088832), (60124717/8796093022208)), (149/35184372088832), by norm_num⟩
  | 12 => ⟨((332103985/35184372088832), (-96115183/70368744177664)), (121/140737488355328), by norm_num⟩
  | 13 => ⟨((-980123785/562949953421312), (70915121/281474976710656)), (91/562949953421312), by norm_num⟩
  | 14 => ⟨((671495483/2251799813685248), (-194339467/4503599627370496)), (127/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1717520901/36028797018963968), (15533523/2251799813685248)), (165/36028797018963968), by norm_num⟩
  | 16 => ⟨((257402203/36028797018963968), (-148991045/144115188075855872)), (101/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-187196903811/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778778978685157/633825300114114700748351602688), (-221540155761/633825300114114700748351602688)), (92223/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472438345624493/9903520314283042199192993792), (-249187701935/39614081257132168796771975168)), (12969/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889529242327711/2475880078570760549798248448), (-264706091255/2475880078570760549798248448)), (110237/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771195565715965/154742504910672534362390528), (-66160823147/38685626227668133590597632)), (110239/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387389519312587/2417851639229258349412352), (-31004548035/1208925819614629174706176)), (12919/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258792832396571/604462909807314587353088), (-216965157425/604462909807314587353088)), (90435/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887798933576109/75557863725914323419136), (-352443408371/75557863725914323419136)), (9185/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297544747752631/4722366482869645213696), (-264223255709/4722366482869645213696)), (110223/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202681950219455/73786976294838206464), (-363129457475/590295810358705651712)), (75781/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823484287011983/73786976294838206464), (-453645708079/73786976294838206464)), (189461/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822668182249279/9223372036854775808), (-509985782971/9223372036854775808)), (106577/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199239649530137/144115188075855872), (-509529136081/1152921504606846976)), (13323/72057594037927936), by norm_num⟩
  | 5 => ⟨((597260625764867/72057594037927936), (-111331204421/36028797018963968)), (93269/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491549272110201/36028797018963968), (-333481125275/18014398509481984)), (139919/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489149503941747/9007199254740992), (-831912198595/9007199254740992)), (349853/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227737659511607/4503599627370496), (-829232452391/2251799813685248)), (349937/2251799813685248), by norm_num⟩
  | 1 => ⟨((553950712755675/562949953421312), (-2474341756639/2251799813685248)), (525119/1125899906842624), by norm_num⟩
  | 0 => ⟨((272523716785695/281474976710656), (-305969943847/140737488355328)), (1051115/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272523716785695/281474976710656), (-305969943847/140737488355328)), (4009685520652389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1055423151403027/1125899906842624), (-4739835408253/1125899906842624)), (2039947/1125899906842624), by norm_num⟩
  | 2 => ⟨((494669000196257/562949953421312), (-2221570493659/281474976710656)), (7683371/2251799813685248), by norm_num⟩
  | 3 => ⟨((434634867213879/562949953421312), (-3904226470879/281474976710656)), (6812087/1125899906842624), by norm_num⟩
  | 4 => ⟨((670917529037789/1125899906842624), (-3014322931249/140737488355328)), (5353873/562949953421312), by norm_num⟩
  | 5 => ⟨((399279558425297/1125899906842624), (-114957975526723/4503599627370496)), (52880207/4503599627370496), by norm_num⟩
  | 6 => ⟨((1126908040786567/9007199254740992), (-163070871315711/9007199254740992)), (40205593/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-211431473/4194304)), (1/16777216), by norm_num⟩, -8, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-1752828755/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-103345558211163/2251799813685248), (-972074761437333/9007199254740992)), (46564467/2251799813685248), by norm_num⟩
  | 1 => ⟨((244907441/2147483648), (575903663/2147483648)), (223/4294967296), by norm_num⟩
  | 2 => ⟨((-608572129/4294967296), (-1431066841/4294967296)), (35/536870912), by norm_num⟩
  | 3 => ⟨((504081643/4294967296), (296338959/1073741824)), (117/2147483648), by norm_num⟩
  | 4 => ⟨((-626297913/8589934592), (-1472749299/8589934592)), (293/8589934592), by norm_num⟩
  | 5 => ⟨((622516739/17179869184), (731928905/8589934592)), (147/8589934592), by norm_num⟩
  | 6 => ⟨((-515631995/34359738368), (-1212516669/34359738368)), (123/17179869184), by norm_num⟩
  | 7 => ⟨((91521241/17179869184), (860854495/68719476736)), (177/68719476736), by norm_num⟩
  | 8 => ⟨((-454843481/274877906944), (-1069571529/274877906944)), (111/137438953472), by norm_num⟩
  | 9 => ⟨((502330485/1099511627776), (1181237957/1099511627776)), (31/137438953472), by norm_num⟩
  | 10 => ⟨((-499297745/4398046511104), (-1174106421/4398046511104)), (249/4398046511104), by norm_num⟩
  | 11 => ⟨((225583325/8796093022208), (1060925401/17592186044416)), (227/17592186044416), by norm_num⟩
  | 12 => ⟨((-5839099/1099511627776), (-878766861/70368744177664)), (95/35184372088832), by norm_num⟩
  | 13 => ⟨((571455643/562949953421312), (1343786841/562949953421312)), (293/562949953421312), by norm_num⟩
  | 14 => ⟨((-405718265/2251799813685248), (-59628301/140737488355328)), (105/1125899906842624), by norm_num⟩
  | 15 => ⟨((537691741/18014398509481984), (1264390499/18014398509481984)), (35/2251799813685248), by norm_num⟩
  | 16 => ⟨((-167014223/36028797018963968), (-392736545/36028797018963968)), (11/4503599627370496), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (-1284951616547/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444664592168457/158456325028528675187087900672), (-1520501237213/316912650057057350374175801344)), (23125/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889617443239123/39614081257132168796771975168), (-13361248699/154742504910672534362390528)), (104081/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889384474779265/2475880078570760549798248448), (-3633464244281/2475880078570760549798248448)), (110609/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771050424904045/154742504910672534362390528), (-3632569619883/154742504910672534362390528)), (55317/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549421611419445/9671406556917033397649408), (-851145926205/2417851639229258349412352)), (51873/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629336514390845/302231454903657293676544), (-1489030340211/302231454903657293676544)), (22701/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943801755414805/37778931862957161709568), (-2418783888661/37778931862957161709568)), (73803/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297397532205821/4722366482869645213696), (-453327268085/590295810358705651712)), (110749/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621252127807885/590295810358705651712), (-4984069711253/590295810358705651712)), (152351/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823228367854841/73786976294838206464), (-6226293542491/73786976294838206464)), (190545/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113898631791773/576460752303423488), (-6999366899459/9223372036854775808)), (214509/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593624422189323/1152921504606846976), (-3496427259003/576460752303423488)), (214693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298565510833067/36028797018963968), (-3055713584635/72057594037927936)), (188063/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491154415800255/36028797018963968), (-4576257209895/18014398509481984)), (282509/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488645396481313/9007199254740992), (-11415080080113/9007199254740992)), (353861/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226697992787709/4503599627370496), (-11376801915455/2251799813685248)), (177475/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107082638820517/1125899906842624), (-33939478436559/2251799813685248)), (133789/281474976710656), by norm_num⟩
  | 0 => ⟨((2176605617685213/2251799813685248), (-67118026679913/2251799813685248)), (540637/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176605617685213/2251799813685248), (-67118026679913/2251799813685248)), (2062366487743186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1050960915057391/1125899906842624), (-129753518080595/2251799813685248)), (4309585/2251799813685248), by norm_num⟩
  | 2 => ⟨((1954542929487061/2251799813685248), (-242234456660203/2251799813685248)), (8542141/2251799813685248), by norm_num⟩
  | 3 => ⟨((208808555513773/281474976710656), (-420514862525447/2251799813685248)), (8333415/1125899906842624), by norm_num⟩
  | 4 => ⟨((145085725276223/281474976710656), (-311953488875401/1125899906842624)), (30953075/2251799813685248), by norm_num⟩
  | 5 => ⟨((106351773450667/562949953421312), (-1286366517261277/4503599627370496)), (12265441/562949953421312), by norm_num⟩
  | 6 => ⟨((-103345558211163/2251799813685248), (-972074761437333/9007199254740992)), (46564467/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1752828755/33554432)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1809290095/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-429241244642621/4503599627370496), (242342990534929/4503599627370496)), (33323805/1125899906842624), by norm_num⟩
  | 1 => ⟨((1049978309/4294967296), (-592801569/4294967296)), (41/536870912), by norm_num⟩
  | 2 => ⟨((-1346570595/4294967296), (380126501/2147483648)), (423/4294967296), by norm_num⟩
  | 3 => ⟨((143911891/536870912), (-650003483/4294967296)), (91/1073741824), by norm_num⟩
  | 4 => ⟨((-738253425/4294967296), (52100813/536870912)), (235/4294967296), by norm_num⟩
  | 5 => ⟨((757433059/8589934592), (-213817515/4294967296)), (243/8589934592), by norm_num⟩
  | 6 => ⟨((-1295184959/34359738368), (91405183/4294967296)), (209/17179869184), by norm_num⟩
  | 7 => ⟨((118645851/8589934592), (-267942475/34359738368)), (309/68719476736), by norm_num⟩
  | 8 => ⟨((-1217282397/274877906944), (687258879/274877906944)), (399/274877906944), by norm_num⟩
  | 9 => ⟨((693837267/549755813888), (-391729827/549755813888)), (229/549755813888), by norm_num⟩
  | 10 => ⟨((-711862981/2199023255552), (401906867/2199023255552)), (237/2199023255552), by norm_num⟩
  | 11 => ⟨((1327921815/17592186044416), (-749724189/17592186044416)), (445/17592186044416), by norm_num⟩
  | 12 => ⟨((-70959421/4398046511104), (320500763/35184372088832)), (383/70368744177664), by norm_num⟩
  | 13 => ⟨((896036043/281474976710656), (-505888139/281474976710656)), (19/17592186044416), by norm_num⟩
  | 14 => ⟨((-1313306899/2251799813685248), (741472833/2251799813685248)), (7/35184372088832), by norm_num⟩
  | 15 => ⟨((898284183/9007199254740992), (-507157405/9007199254740992)), (309/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1152026719/72057594037927936), (325208265/36028797018963968)), (199/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (1711384903399/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778548129787613/633825300114114700748351602688), (2024874956621/316912650057057350374175801344)), (69449/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944746616767483/19807040628566084398385987584), (569383714301/4951760157141521099596496896)), (156299/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472313062245133/618970019642690137449562112), (4838667163557/2475880078570760549798248448)), (5191/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((885458957377193/77371252455336267181195264), (4837436099213/154742504910672534362390528)), (83081/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774648540628971/4835703278458516698824704), (4533788574453/9671406556917033397649408)), (77915/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39330117601533/18889465931478580854784), (247859843789/37778931862957161709568)), (136405/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887425389302967/75557863725914323419136), (3220952469405/37778931862957161709568)), (221757/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297263447195319/4722366482869645213696), (4829284646167/4722366482869645213696)), (166405/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202633369925111/73786976294838206464), (3318391678767/295147905179352825856)), (228949/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455748926710723/18446744073709551616), (8290756512021/73786976294838206464)), (4475/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1822114717217093/9223372036854775808), (9319922910961/9223372036854775808)), (322493/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593358975286629/1152921504606846976), (9310954747603/1152921504606846976)), (80715/288230376151711744), by norm_num⟩
  | 5 => ⟨((298506867708925/36028797018963968), (8137002471757/144115188075855872)), (70729/36028797018963968), by norm_num⟩
  | 4 => ⟨((186349744867239/4503599627370496), (6092676742823/18014398509481984)), (425201/36028797018963968), by norm_num⟩
  | 3 => ⟨((372047952983811/2251799813685248), (3799116051033/2251799813685248)), (266475/4503599627370496), by norm_num⟩
  | 2 => ⟨((556441728993537/1125899906842624), (15143693293447/2251799813685248)), (535129/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106354678153313/1125899906842624), (1411491255627/70368744177664)), (808153/1125899906842624), by norm_num⟩
  | 0 => ⟨((135841207505561/140737488355328), (44642488797561/1125899906842624)), (1638225/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((135841207505561/140737488355328), (44642488797561/1125899906842624)), (6249332432273482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1047152055923533/1125899906842624), (86178738233601/1125899906842624)), (411547/140737488355328), by norm_num⟩
  | 2 => ⟨((241828924285891/281474976710656), (160302425410583/1125899906842624)), (1657053/281474976710656), by norm_num⟩
  | 3 => ⟨((1616489680507669/2251799813685248), (550894627301951/2251799813685248)), (13276655/1125899906842624), by norm_num⟩
  | 4 => ⟨((512824004771957/1125899906842624), (395468315908297/1125899906842624)), (3194735/140737488355328), by norm_num⟩
  | 5 => ⟨((378695371889405/4503599627370496), (1441020781985815/4503599627370496)), (41236395/1125899906842624), by norm_num⟩
  | 6 => ⟨((-429241244642621/4503599627370496), (242342990534929/4503599627370496)), (33323805/1125899906842624), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1809290095/33554432)), (3/33554432), by norm_num⟩, -9, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-1861565131/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((444265999454131/9007199254740992), (811115553802069/9007199254740992)), (61449911/4503599627370496), by norm_num⟩
  | 1 => ⟨((-559064599/4294967296), (-1020708297/4294967296)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((184425441/1073741824), (42089183/134217728)), (13/268435456), by norm_num⟩
  | 3 => ⟨((-648945749/4294967296), (-296202045/1073741824)), (185/4294967296), by norm_num⟩
  | 4 => ⟨((428151259/4294967296), (390847089/2147483648)), (31/1073741824), by norm_num⟩
  | 5 => ⟨((-451966287/8589934592), (-206293575/2147483648)), (133/8589934592), by norm_num⟩
  | 6 => ⟨((198794157/8589934592), (725894095/17179869184)), (119/17179869184), by norm_num⟩
  | 7 => ⟨((-299788101/34359738368), (-1094672075/68719476736)), (91/34359738368), by norm_num⟩
  | 8 => ⟨((395578993/137438953472), (722225591/137438953472)), (61/68719476736), by norm_num⟩
  | 9 => ⟨((-463980285/549755813888), (-847108773/549755813888)), (145/549755813888), by norm_num⟩
  | 10 => ⟨((489788229/2199023255552), (447113723/1099511627776)), (155/2199023255552), by norm_num⟩
  | 11 => ⟨((-235014403/4398046511104), (-107268977/1099511627776)), (151/8796093022208), by norm_num⟩
  | 12 => ⟨((413477655/35184372088832), (377451973/17592186044416)), (135/35184372088832), by norm_num⟩
  | 13 => ⟨((-671502299/281474976710656), (-1225990641/281474976710656)), (221/281474976710656), by norm_num⟩
  | 14 => ⟨((126580933/281474976710656), (924417025/1125899906842624)), (169/1125899906842624), by norm_num⟩
  | 15 => ⟨((-89081157/1125899906842624), (-1301114413/9007199254740992)), (15/562949953421312), by norm_num⟩
  | 16 => ⟨((29386285/2251799813685248), (429214441/18014398509481984)), (5/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (1393408352309/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778456950271897/633825300114114700748351602688), (1648477774035/633825300114114700748351602688)), (92363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889391088931065/39614081257132168796771975168), (115885591531/2475880078570760549798248448)), (103919/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944572142674959/1237940039285380274899124224), (1969597641319/2475880078570760549798248448)), (110425/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770810586242099/154742504910672534362390528), (1969083244069/154742504910672534362390528)), (110439/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96824820946583/604462909807314587353088), (230683646319/1208925819614629174706176)), (103551/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4915925719793/2361183241434822606848), (1614239351849/604462909807314587353088)), (45311/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887285635892353/75557863725914323419136), (655528823731/18889465931478580854784)), (147287/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297159735704299/4722366482869645213696), (982845598523/2361183241434822606848)), (110489/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405231536850875/147573952589676412928), (1350685682407/295147905179352825856)), (151961/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822822375314145/73786976294838206464), (843633634983/18446744073709551616)), (190009/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455480850838847/2305843009213693952), (1896678279279/4611686018427387904)), (13365/576460752303423488), by norm_num⟩
  | 6 => ⟨((1593172258077729/1152921504606846976), (3789616420399/1152921504606846976)), (53485/288230376151711744), by norm_num⟩
  | 5 => ⟨((596934626431161/72057594037927936), (3311711328815/144115188075855872)), (93655/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490570922061417/36028797018963968), (77487069431/562949953421312)), (281189/36028797018963968), by norm_num⟩
  | 3 => ⟨((371981489538329/2251799813685248), (6184300997093/9007199254740992)), (175941/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225288774567073/4503599627370496), (6162355883845/2251799813685248)), (704949/4503599627370496), by norm_num⟩
  | 1 => ⟨((553031287324525/562949953421312), (9188851685567/1125899906842624)), (530199/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086408742183157/1125899906842624), (18160055577429/1125899906842624)), (2132755/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1086408742183157/1125899906842624), (18160055577429/1125899906842624)), (8135814675337981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096019655570227/2251799813685248), (2190385999007/70368744177664)), (2092349/1125899906842624), by norm_num⟩
  | 2 => ⟨((974417315442965/1125899906842624), (32621671459797/562949953421312)), (2012729/562949953421312), by norm_num⟩
  | 3 => ⟨((1679070057817979/2251799813685248), (225861082932381/2251799813685248)), (3717125/562949953421312), by norm_num⟩
  | 4 => ⟨((307338935443267/562949953421312), (168414873859259/1125899906842624)), (25156295/2251799813685248), by norm_num⟩
  | 5 => ⟨((1241550205650457/4503599627370496), (735560207157231/4503599627370496)), (69987439/4503599627370496), by norm_num⟩
  | 6 => ⟨((444265999454131/9007199254740992), (811115553802069/9007199254740992)), (61449911/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-1861565131/33554432)), (1/16777216), by norm_num⟩, -9, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-1910232025/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((809005351748721/9007199254740992), (-161883895306017/4503599627370496)), (75461555/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1044667771/4294967296), (104520253/1073741824)), (99/4294967296), by norm_num⟩
  | 2 => ⟨((1414506383/4294967296), (-70761523/536870912)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((-1276851431/4294967296), (255501009/2147483648)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((216111111/1073741824), (-345954779/4294967296)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((-234095895/2147483648), (374745163/8589934592)), (3/268435456), by norm_num⟩
  | 6 => ⟨((422628957/8589934592), (-169138119/8589934592)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((-654000247/34359738368), (130867005/17179869184)), (139/68719476736), by norm_num⟩
  | 8 => ⟨((442766375/68719476736), (-354394419/137438953472)), (3/4294967296), by norm_num⟩
  | 9 => ⟨((-532903809/274877906944), (426541279/549755813888)), (59/274877906944), by norm_num⟩
  | 10 => ⟨((577252107/1099511627776), (-231019039/1099511627776)), (65/1099511627776), by norm_num⟩
  | 11 => ⟨((-1136892861/8796093022208), (454989931/8796093022208)), (65/4398046511104), by norm_num⟩
  | 12 => ⟨((1026254313/35184372088832), (-205355929/17592186044416)), (119/35184372088832), by norm_num⟩
  | 13 => ⟨((-855122523/140737488355328), (342224101/140737488355328)), (101/140737488355328), by norm_num⟩
  | 14 => ⟨((661632777/562949953421312), (-529577169/1125899906842624)), (159/1125899906842624), by norm_num⟩
  | 15 => ⟨((-119448985/562949953421312), (11951013/140737488355328)), (117/4503599627370496), by norm_num⟩
  | 16 => ⟨((1293895391/36028797018963968), (-258911545/18014398509481984)), (161/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-247940977159/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778366523139955/633825300114114700748351602688), (-586597656381/633825300114114700748351602688)), (46129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472322362513835/9903520314283042199192993792), (-659788649449/39614081257132168796771975168)), (103795/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889036413141527/2475880078570760549798248448), (-700858481025/2475880078570760549798248448)), (55143/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442675711976417/38685626227668133590597632), (-175167683403/38685626227668133590597632)), (110291/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774548136302811/4835703278458516698824704), (-656679401715/9671406556917033397649408)), (103403/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629194435798051/302231454903657293676544), (-143598786221/151115727451828646838272)), (90483/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471785679734345/18889465931478580854784), (-933018532369/75557863725914323419136)), (36761/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297052780645557/4722366482869645213696), (-699437187089/4722366482869645213696)), (110291/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620779461871119/590295810358705651712), (-961195540921/590295810358705651712)), (151665/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911319792109049/36893488147419103232), (-600349545873/36893488147419103232)), (189601/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821718540252945/9223372036854775808), (-1349693790651/9223372036854775808)), (213329/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592968364396511/1152921504606846976), (-1348329275829/1152921504606846976)), (106683/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193691934184205/144115188075855872), (-1178254884039/144115188075855872)), (11671/9007199254740992), by norm_num⟩
  | 4 => ⟨((745153557437805/18014398509481984), (-1764320472587/36028797018963968)), (280185/36028797018963968), by norm_num⟩
  | 3 => ⟨((185949998150815/1125899906842624), (-1100026352875/4503599627370496)), (175187/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112324067621589/2251799813685248), (-4384103108565/4503599627370496)), (701179/4503599627370496), by norm_num⟩
  | 1 => ⟨((552798069247815/562949953421312), (-1634073316919/562949953421312)), (1052855/2251799813685248), by norm_num⟩
  | 0 => ⟨((542765753261873/562949953421312), (-12914004175929/2251799813685248)), (527527/562949953421312), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542765753261873/562949953421312), (-12914004175929/2251799813685248)), (2012355806590843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2093146915846499/2251799813685248), (-24901962107205/2251799813685248)), (4093107/2251799813685248), by norm_num⟩
  | 2 => ⟨((1945396689784627/2251799813685248), (-46294936935729/2251799813685248)), (962497/281474976710656), by norm_num⟩
  | 3 => ⟨((1679734155963387/2251799813685248), (-79991139994955/2251799813685248)), (6810543/1125899906842624), by norm_num⟩
  | 4 => ⟨((625079599688125/1125899906842624), (-119339071979119/2251799813685248)), (10644539/1125899906842624), by norm_num⟩
  | 5 => ⟨((343870756244031/1125899906842624), (-265019719378259/4503599627370496)), (12947579/1125899906842624), by norm_num⟩
  | 6 => ⟨((809005351748721/9007199254740992), (-161883895306017/4503599627370496)), (75461555/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1910232025/33554432)), (1/16777216), by norm_num⟩, -9, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile017Terms1
