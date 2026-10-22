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
namespace Reinmann.XiBand97.Tile016Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53459/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53459/2560))
  have he : value ((69/80), (53459/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log16 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog16 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/8388608), (-1942746831/33554432)), (1/16777216), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term16 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((180748402212057/9007199254740992), (-201035933155703/2251799813685248)), (123689549/9007199254740992), by norm_num⟩
  | 1 => ⟨((-119481321/2147483648), (265784245/1073741824)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((331272563/4294967296), (-1473820801/4294967296)), (29/536870912), by norm_num⟩
  | 3 => ⟨((-306160857/4294967296), (340524911/1073741824)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((212214535/4294967296), (-118016941/536870912)), (19/536870912), by norm_num⟩
  | 5 => ⟨((-235353451/8589934592), (1047079807/8589934592)), (85/4294967296), by norm_num⟩
  | 6 => ⟨((217512775/17179869184), (-967707221/17179869184)), (159/17179869184), by norm_num⟩
  | 7 => ⟨((-172306705/34359738368), (1533173787/68719476736)), (127/34359738368), by norm_num⟩
  | 8 => ⟨((119433907/68719476736), (-66419693/8589934592)), (89/68719476736), by norm_num⟩
  | 9 => ⟨((-2299591/4294967296), (327385763/137438953472)), (111/274877906944), by norm_num⟩
  | 10 => ⟨((81610497/549755813888), (-1452329719/2199023255552)), (31/274877906944), by norm_num⟩
  | 11 => ⟨((-329123409/8796093022208), (1464259273/8796093022208)), (63/2199023255552), by norm_num⟩
  | 12 => ⟨((304174617/35184372088832), (-338315729/8796093022208)), (235/35184372088832), by norm_num⟩
  | 13 => ⟨((-129746325/70368744177664), (1154474307/140737488355328)), (101/70368744177664), by norm_num⟩
  | 14 => ⟨((205561827/562949953421312), (-914537841/562949953421312)), (81/281474976710656), by norm_num⟩
  | 15 => ⟨((-75991787/1125899906842624), (169042487/562949953421312)), (121/2251799813685248), by norm_num⟩
  | 16 => ⟨((52673493/4503599627370496), (-468685293/9007199254740992)), (85/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-879067218723/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889139310099329/316912650057057350374175801344), (-2079573065435/633825300114114700748351602688)), (92405/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889190460669429/39614081257132168796771975168), (-2339032185399/39614081257132168796771975168)), (103969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472232776279559/618970019642690137449562112), (-1242307698315/1237940039285380274899124224)), (55241/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770597391773265/154742504910672534362390528), (-38811461983/2417851639229258349412352)), (110499/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548997250242085/9671406556917033397649408), (-1163981755959/4835703278458516698824704)), (25903/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258302069931053/604462909807314587353088), (-63632629141/18889465931478580854784)), (45339/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887001371977387/75557863725914323419136), (-3307539893465/75557863725914323419136)), (73693/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162118314156915/590295810358705651712), (-619867066785/1180591620717411303424)), (55285/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405158231718531/147573952589676412928), (-1703670808667/295147905179352825856)), (76041/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822455790458589/73786976294838206464), (-4256288002563/73786976294838206464)), (190175/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821510914486871/9223372036854775808), (-4784354615515/9223372036854775808)), (6689/288230376151711744), by norm_num⟩
  | 6 => ⟨((1592759668803711/1152921504606846976), (-4779397398847/1152921504606846976)), (107087/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193508125289007/144115188075855872), (-1044100515373/36028797018963968)), (23443/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490029009272409/36028797018963968), (-6253477266773/36028797018963968)), (281599/36028797018963968), by norm_num⟩
  | 3 => ⟨((743624092623911/4503599627370496), (-7797411218619/9007199254740992)), (352497/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223932105242055/4503599627370496), (-15536655440599/4503599627370496)), (88311/562949953421312), by norm_num⟩
  | 1 => ⟨((2210087414007485/2251799813685248), (-23160051518835/2251799813685248)), (1063483/2251799813685248), by norm_num⟩
  | 0 => ⟨((2168731550507393/2251799813685248), (-45743283633217/2251799813685248)), (267755/281474976710656), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168731550507393/2251799813685248), (-45743283633217/2251799813685248)), (1021404267431163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((260974802333483/281474976710656), (-22027913368731/562949953421312)), (2106535/1125899906842624), by norm_num⟩
  | 2 => ⟨((966146845529969/1125899906842624), (-163388743238319/2251799813685248)), (8142165/2251799813685248), by norm_num⟩
  | 3 => ⟨((823133345283065/1125899906842624), (-280411283304019/2251799813685248)), (7577669/1125899906842624), by norm_num⟩
  | 4 => ⟨((584324484057175/1125899906842624), (-205005681480545/1125899906842624)), (3241791/281474976710656), by norm_num⟩
  | 5 => ⟨((1063710091491221/4503599627370496), (-851157999618899/4503599627370496)), (36363353/2251799813685248), by norm_num⟩
  | 6 => ⟨((180748402212057/9007199254740992), (-201035933155703/2251799813685248)), (123689549/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-1942746831/33554432)), (1/16777216), by norm_num⟩, -9, term16ValuePoly, term16ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log17 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog17 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-81995171/33554432), (-1985226371/33554432)), (1/16777216), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term17 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1353033724466959/18014398509481984), (-785338838884823/18014398509481984)), (8855803/562949953421312), by norm_num⟩
  | 1 => ⟨((913961697/4294967296), (265244541/2147483648)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((-647362119/2147483648), (-751494373/4294967296)), (275/4294967296), by norm_num⟩
  | 3 => ⟨((1222743329/4294967296), (709714629/4294967296)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-866073179/4294967296), (-502693239/4294967296)), (187/4294967296), by norm_num⟩
  | 5 => ⟨((981508035/8589934592), (569694877/8589934592)), (107/4294967296), by norm_num⟩
  | 6 => ⟨((-463470277/8589934592), (-67252797/2147483648)), (51/4294967296), by norm_num⟩
  | 7 => ⟨((750348671/34359738368), (435523479/34359738368)), (167/34359738368), by norm_num⟩
  | 8 => ⟨((-531474467/68719476736), (-308482733/68719476736)), (239/137438953472), by norm_num⟩
  | 9 => ⟨((669235801/274877906944), (388443287/274877906944)), (303/549755813888), by norm_num⟩
  | 10 => ⟨((-758435121/1099511627776), (-220108541/549755813888)), (87/549755813888), by norm_num⟩
  | 11 => ⟨((781384911/4398046511104), (226768893/2199023255552)), (181/4398046511104), by norm_num⟩
  | 12 => ⟨((-368971693/8796093022208), (-214161551/8796093022208)), (173/17592186044416), by norm_num⟩
  | 13 => ⟨((643308015/70368744177664), (186697035/35184372088832)), (19/8796093022208), by norm_num⟩
  | 14 => ⟨((-1041502201/562949953421312), (-302258589/281474976710656)), (31/70368744177664), by norm_num⟩
  | 15 => ⟨((786879449/2251799813685248), (456726969/2251799813685248)), (189/2251799813685248), by norm_num⟩
  | 16 => ⟨((-557349339/9007199254740992), (-80875309/2251799813685248)), (135/9007199254740992), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (-425903298495/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889095836433947/316912650057057350374175801344), (-2014909752903/316912650057057350374175801344)), (92597/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236136538853791/4951760157141521099596496896), (-1133141639535/9903520314283042199192993792)), (104197/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888826376271953/2475880078570760549798248448), (-1203662389911/618970019642690137449562112)), (110739/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885246081605321/77371252455336267181195264), (-4813297105419/154742504910672534362390528)), (27693/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548898067928815/9671406556917033397649408), (-2255514694299/4835703278458516698824704)), (103885/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258214755335525/604462909807314587353088), (-1972857221761/302231454903657293676544)), (90935/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471714623215503/18889465931478580854784), (-6409093761241/75557863725914323419136)), (73917/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((20263101345609/73786976294838206464), (-4804465437313/4722366482869645213696)), (55467/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620482981233631/590295810358705651712), (-412644674377/36893488147419103232)), (38157/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822266249144897/73786976294838206464), (-8247158332853/73786976294838206464)), (190927/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821294785514167/9223372036854775808), (-4635085776353/4611686018427387904)), (53747/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592539928941447/1152921504606846976), (-4630162994129/576460752303423488)), (215231/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193311801443393/144115188075855872), (-8091717782209/144115188075855872)), (94301/72057594037927936), by norm_num⟩
  | 4 => ⟨((186215805936209/4503599627370496), (-6057731885441/18014398509481984)), (70863/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486855910439921/9007199254740992), (-15105681680071/9007199254740992)), (177639/4503599627370496), by norm_num⟩
  | 2 => ⟨((555776394767883/1125899906842624), (-15047808764051/2251799813685248)), (356725/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104371762408657/1125899906842624), (-22427378015521/1125899906842624)), (538715/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082816199804519/1125899906842624), (-11069874987435/281474976710656)), (1092001/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082816199804519/1125899906842624), (-11069874987435/281474976710656)), (4165653233054732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((519819853136783/562949953421312), (-42585099770795/562949953421312)), (1093161/562949953421312), by norm_num⟩
  | 2 => ⟨((953545470113177/1125899906842624), (-157289863328955/1125899906842624)), (8736823/2251799813685248), by norm_num⟩
  | 3 => ⟨((1571203367353957/2251799813685248), (-266423392986407/1125899906842624)), (17239849/2251799813685248), by norm_num⟩
  | 4 => ⟨((970225821578399/2251799813685248), (-743592444866631/2251799813685248)), (32217347/2251799813685248), by norm_num⟩
  | 5 => ⟨((172487988689849/2251799813685248), (-1281557243864415/4503599627370496)), (24520243/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1353033724466959/18014398509481984), (-785338838884823/18014398509481984)), (8855803/562949953421312), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-1985226371/33554432)), (1/16777216), by norm_num⟩, -9, term17ValuePoly, term17ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log18 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog18 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-83649375/33554432), (-1012638573/16777216)), (1/16777216), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term18 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1169373647251977/18014398509481984), (922075216801933/18014398509481984)), (272376471/18014398509481984), by norm_num⟩
  | 1 => ⟨((201459203/1073741824), (-635418931/4294967296)), (95/2147483648), by norm_num⟩
  | 2 => ⟨((-582291991/2147483648), (459149233/2147483648)), (277/4294967296), by norm_num⟩
  | 3 => ⟨((280506721/1073741824), (-884741317/4294967296)), (269/4294967296), by norm_num⟩
  | 4 => ⟨((-12668261/67108864), (639307829/4294967296)), (49/1073741824), by norm_num⟩
  | 5 => ⟨((468684593/4294967296), (-369567459/4294967296)), (229/8589934592), by norm_num⟩
  | 6 => ⟨((-903115141/17179869184), (356062449/8589934592)), (223/17179869184), by norm_num⟩
  | 7 => ⟨((745810999/34359738368), (-588087341/34359738368)), (93/17179869184), by norm_num⟩
  | 8 => ⟨((-269458881/34359738368), (849895521/137438953472)), (271/137438953472), by norm_num⟩
  | 9 => ⟨((692298969/274877906944), (-545892003/274877906944)), (11/17179869184), by norm_num⟩
  | 10 => ⟨((-800400555/1099511627776), (631132331/1099511627776)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((420628211/2199023255552), (-82918503/549755813888)), (219/4398046511104), by norm_num⟩
  | 12 => ⟨((-810514601/17592186044416), (639107465/17592186044416)), (213/17592186044416), by norm_num⟩
  | 13 => ⟨((720827235/70368744177664), (-71048391/8796093022208)), (3/1099511627776), by norm_num⟩
  | 14 => ⟨((-1190547819/562949953421312), (938771487/562949953421312)), (319/562949953421312), by norm_num⟩
  | 15 => ⟨((917633545/2251799813685248), (-361786479/1125899906842624)), (31/281474976710656), by norm_num⟩
  | 16 => ⟨((-663075521/9007199254740992), (522848711/9007199254740992)), (181/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (3222518772885/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778116642093805/633825300114114700748351602688), (1905525243931/316912650057057350374175801344)), (2893/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889007971369389/39614081257132168796771975168), (1071622407237/9903520314283042199192993792)), (26043/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944368427950117/1237940039285380274899124224), (4553235505773/2475880078570760549798248448)), (110711/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885201372184705/77371252455336267181195264), (4551931118085/154742504910672534362390528)), (55371/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548814345580631/9671406556917033397649408), (4266049868661/9671406556917033397649408)), (51927/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314535401507037/151115727451828646838272), (466426060269/75557863725914323419136)), (45453/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886739827118833/75557863725914323419136), (3030471237593/37778931862957161709568)), (18473/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648374831656469/2361183241434822606848), (2271717970013/2361183241434822606848)), (110893/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620361136418625/590295810358705651712), (1560883944637/147573952589676412928)), (152567/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822114372466367/73786976294838206464), (3899444782405/36893488147419103232)), (190843/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56910141056957/288230376151711744), (4383075671335/4611686018427387904)), (107441/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592370393058853/1152921504606846976), (4378329447635/576460752303423488)), (215113/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193164283743115/144115188075855872), (3825703456831/72057594037927936)), (47121/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489506819366527/36028797018963968), (1431974323599/4503599627370496)), (283245/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486584251118179/9007199254740992), (14282493393923/9007199254740992)), (177483/4503599627370496), by norm_num⟩
  | 2 => ⟨((555642713077611/1125899906842624), (28453448344827/4503599627370496)), (712671/4503599627370496), by norm_num⟩
  | 1 => ⟨((68998837185891/70368744177664), (42402065103809/2251799813685248)), (537935/1125899906842624), by norm_num⟩
  | 0 => ⟨((2164155606101151/2251799813685248), (41848065946543/1125899906842624)), (2179311/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164155606101151/2251799813685248), (41848065946543/1125899906842624)), (8313411721236418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1038405904579859/1125899906842624), (80438523861927/1125899906842624)), (4350981/2251799813685248), by norm_num⟩
  | 2 => ⟨((475982127732357/562949953421312), (148375246549493/1125899906842624)), (1080929/281474976710656), by norm_num⟩
  | 3 => ⟨((98168221317903/140737488355328), (501813456959899/2251799813685248)), (8451117/1125899906842624), by norm_num⟩
  | 4 => ⟨((983770918796301/2251799813685248), (350028518192441/1125899906842624)), (7778215/562949953421312), by norm_num⟩
  | 5 => ⟨((212152680524251/2251799813685248), (611684706347911/2251799813685248)), (93061033/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1169373647251977/18014398509481984), (922075216801933/18014398509481984)), (272376471/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1012638573/16777216)), (1/16777216), by norm_num⟩, -10, term18ValuePoly, term18ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log19 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog19 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-42607059/16777216), (-257895241/4194304)), (1/8388608), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term19 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((39804730059791/2251799813685248), (1385198556485655/18014398509481984)), (426818945/18014398509481984), by norm_num⟩
  | 1 => ⟨((-27943277/536870912), (-972421795/4294967296)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((41138637/536870912), (1431618319/4294967296)), (447/4294967296), by norm_num⟩
  | 3 => ⟨((-80753471/1073741824), (-1405104261/4294967296)), (441/4294967296), by norm_num⟩
  | 4 => ⟨((59443417/1073741824), (1034310939/4294967296)), (163/2147483648), by norm_num⟩
  | 5 => ⟨((-140022011/4294967296), (-609093089/4294967296)), (193/4294967296), by norm_num⟩
  | 6 => ⟨((274857511/17179869184), (1195624955/17179869184)), (381/17179869184), by norm_num⟩
  | 7 => ⟨((-231228905/34359738368), (-1005841349/34359738368)), (161/17179869184), by norm_num⟩
  | 8 => ⟨((85104925/34359738368), (1480819237/137438953472)), (477/137438953472), by norm_num⟩
  | 9 => ⟨((-222743341/274877906944), (-968929307/274877906944)), (157/137438953472), by norm_num⟩
  | 10 => ⟨((131170835/549755813888), (142647661/137438953472)), (93/274877906944), by norm_num⟩
  | 11 => ⟨((-4388915/68719476736), (-610934303/2199023255552)), (25/274877906944), by norm_num⟩
  | 12 => ⟨((275688371/17592186044416), (74952449/1099511627776)), (395/17592186044416), by norm_num⟩
  | 13 => ⟨((-31221061/8796093022208), (-135811023/8796093022208)), (359/70368744177664), by norm_num⟩
  | 14 => ⟨((105061153/140737488355328), (914028045/281474976710656)), (19/17592186044416), by norm_num⟩
  | 15 => ⟨((-329969231/2251799813685248), (-1435359895/2251799813685248)), (479/2251799813685248), by norm_num⟩
  | 16 => ⟨((121446783/4503599627370496), (528291203/4503599627370496)), (177/4503599627370496), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1751799244303/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444512572748097/158456325028528675187087900672), (1035786238901/316912650057057350374175801344)), (23101/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888933646985491/39614081257132168796771975168), (2330005270013/39614081257132168796771975168)), (207935/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944329155255645/1237940039285380274899124224), (2474989289341/2475880078570760549798248448)), (110481/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770324675819209/154742504910672534362390528), (618567029181/38685626227668133590597632)), (55249/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387185415645225/2417851639229258349412352), (2318860383449/9671406556917033397649408)), (207221/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258078514247459/604462909807314587353088), (1014118581619/302231454903657293676544)), (90677/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886638250536619/75557863725914323419136), (3294450399833/75557863725914323419136)), (294769/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296674309096871/4722366482869645213696), (154348926753/295147905179352825856)), (13821/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620258868551953/590295810358705651712), (848409566927/147573952589676412928)), (304159/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821988550969623/73786976294838206464), (1059748191677/18446744073709551616)), (380345/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820985728213569/9223372036854775808), (2382334787991/4611686018427387904)), (53511/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592235054782059/1152921504606846976), (4759428111365/1152921504606846976)), (107085/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193049731200961/144115188075855872), (4158610015429/144115188075855872)), (46885/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489342702997093/36028797018963968), (1556538375765/9007199254740992)), (281593/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486392547517939/9007199254740992), (242567151935/281474976710656)), (704975/9007199254740992), by norm_num⟩
  | 2 => ⟨((277778443948925/562949953421312), (3865706742051/1125899906842624)), (1412935/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207547340716055/2251799813685248), (23041116347295/2251799813685248)), (2126891/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081859074436497/1125899906842624), (22736521503439/1125899906842624)), (4283885/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081859074436497/1125899906842624), (22736521503439/1125899906842624)), (16341724404341887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1039081805070301/1125899906842624), (43694314139515/1125899906842624)), (2101413/562949953421312), by norm_num⟩
  | 2 => ⟨((957262539937915/1125899906842624), (80650094260541/1125899906842624)), (16167405/2251799813685248), by norm_num⟩
  | 3 => ⟨((1616213176916677/2251799813685248), (137140634986959/1125899906842624)), (29807897/2251799813685248), by norm_num⟩
  | 4 => ⟨((1126616497062735/2251799813685248), (393726831327689/2251799813685248)), (50050333/2251799813685248), by norm_num⟩
  | 5 => ⟨((989647398471907/4503599627370496), (393977422694657/2251799813685248)), (67584775/2251799813685248), by norm_num⟩
  | 6 => ⟨((39804730059791/2251799813685248), (1385198556485655/18014398509481984)), (426818945/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-257895241/4194304)), (1/8388608), by norm_num⟩, -10, term19ValuePoly, term19ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log20 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog20 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-43349291/16777216), (-524775757/8388608)), (1/16777216), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term20 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1309200954692225/18014398509481984), (11486363297819/562949953421312)), (3388757/562949953421312), by norm_num⟩
  | 1 => ⟨((-935081375/4294967296), (-131263997/2147483648)), (79/4294967296), by norm_num⟩
  | 2 => ⟨((1400626727/4294967296), (24576987/268435456)), (15/536870912), by norm_num⟩
  | 3 => ⟨((-699317115/2147483648), (-196336195/2147483648)), (61/2147483648), by norm_num⟩
  | 4 => ⟨((523741713/2147483648), (147042669/2147483648)), (93/4294967296), by norm_num⟩
  | 5 => ⟨((-627595981/4294967296), (-352400375/8589934592)), (57/4294967296), by norm_num⟩
  | 6 => ⟨((1253406357/17179869184), (351899059/17179869184)), (29/4294967296), by norm_num⟩
  | 7 => ⟨((-1072819965/34359738368), (-301198677/34359738368)), (101/34359738368), by norm_num⟩
  | 8 => ⟨((1606940697/137438953472), (451155299/137438953472)), (77/68719476736), by norm_num⟩
  | 9 => ⟨((-534884901/137438953472), (-300342331/274877906944)), (13/34359738368), by norm_num⟩
  | 10 => ⟨((1281897569/1099511627776), (179949043/549755813888)), (127/1099511627776), by norm_num⟩
  | 11 => ⟨((-698222167/2199023255552), (-12251799/137438953472)), (35/1099511627776), by norm_num⟩
  | 12 => ⟨((1394457787/17592186044416), (391499837/17592186044416)), (71/8796093022208), by norm_num⟩
  | 13 => ⟨((-321340169/17592186044416), (-11277199/2199023255552)), (133/70368744177664), by norm_num⟩
  | 14 => ⟨((1100170417/281474976710656), (308877431/281474976710656)), (29/70368744177664), by norm_num⟩
  | 15 => ⟨((-878884273/1125899906842624), (-30843803/140737488355328)), (95/1125899906842624), by norm_num⟩
  | 16 => ⟨((1316450991/9007199254740992), (2887493/70368744177664)), (9/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (356535107671/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777984351254695/633825300114114700748351602688), (210793089107/316912650057057350374175801344)), (46121/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118053725197429/2475880078570760549798248448), (237089390573/19807040628566084398385987584)), (103775/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944289910960469/1237940039285380274899124224), (503682241393/2475880078570760549798248448)), (110265/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221280799107941/19342813113834066795298816), (62941626617/19342813113834066795298816)), (27567/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548668490636777/9671406556917033397649408), (471903706745/9671406556917033397649408)), (25845/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629007353471499/302231454903657293676544), (412757320703/604462909807314587353088)), (90461/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886534972309231/75557863725914323419136), (335216876321/37778931862957161709568)), (73503/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162074650950763/590295810358705651712), (251282840821/2361183241434822606848)), (110261/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810076716851575/295147905179352825856), (345303094017/295147905179352825856)), (151619/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227732203213527/9223372036854775808), (862625786827/73786976294838206464)), (94769/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820839629174571/9223372036854775808), (969585873883/9223372036854775808)), (213251/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592090442549719/1152921504606846976), (484250945521/576460752303423488)), (106639/576460752303423488), by norm_num⟩
  | 5 => ⟨((596462431988729/72057594037927936), (105777663105/18014398509481984)), (23331/18014398509481984), by norm_num⟩
  | 4 => ⟨((744579364349151/18014398509481984), (1266900328875/36028797018963968)), (280031/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486168377689177/9007199254740992), (394844801369/2251799813685248)), (5471/140737488355328), by norm_num⟩
  | 2 => ⟨((2221796512780833/4503599627370496), (1573028144535/2251799813685248)), (175151/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103471854705001/1125899906842624), (4687456496503/2251799813685248)), (16433/35184372088832), by norm_num⟩
  | 0 => ⟨((2162680653001717/2251799813685248), (9249162539921/2251799813685248)), (2106701/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162680653001717/2251799813685248), (9249162539921/2251799813685248)), (8036426552779387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519262639537859/562949953421312), (17766219501385/2251799813685248)), (1015989/562949953421312), by norm_num⟩
  | 2 => ⟨((1915722417394603/2251799813685248), (32774970410181/2251799813685248)), (118145/35184372088832), by norm_num⟩
  | 3 => ⟨((814663488185115/1125899906842624), (27883360307003/1125899906842624)), (13085653/2251799813685248), by norm_num⟩
  | 4 => ⟨((588772690335241/1125899906842624), (40350932497591/1125899906842624)), (19584825/2251799813685248), by norm_num⟩
  | 5 => ⟨((306443833092349/1125899906842624), (42201845723153/1125899906842624)), (43773967/4503599627370496), by norm_num⟩
  | 6 => ⟨((1309200954692225/18014398509481984), (11486363297819/562949953421312)), (3388757/562949953421312), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-524775757/8388608)), (1/16777216), by norm_num⟩, -10, term20ValuePoly, term20ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log21 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog21 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22027651/8388608), (-1066645095/16777216)), (1/8388608), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term21 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((958264129708893/18014398509481984), (-27627232595009/562949953421312)), (36501363/2251799813685248), by norm_num⟩
  | 1 => ⟨((-173893967/1073741824), (641721569/4294967296)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((1058848169/4294967296), (-488433929/2147483648)), (41/536870912), by norm_num⟩
  | 3 => ⟨((-33580073/134217728), (991365371/4294967296)), (335/4294967296), by norm_num⟩
  | 4 => ⟨((408941143/2147483648), (-754558529/4294967296)), (257/4294967296), by norm_num⟩
  | 5 => ⟨((-996024389/8589934592), (918908149/8589934592)), (315/8589934592), by norm_num⟩
  | 6 => ⟨((126350775/2147483648), (-932545493/17179869184)), (161/8589934592), by norm_num⟩
  | 7 => ⟨((-879263473/34359738368), (811187337/34359738368)), (141/17179869184), by norm_num⟩
  | 8 => ⟨((669234343/68719476736), (-77177439/8589934592)), (27/8589934592), by norm_num⟩
  | 9 => ⟨((-905555099/274877906944), (835443359/274877906944)), (147/137438953472), by norm_num⟩
  | 10 => ⟨((1102793127/1099511627776), (-1017410421/1099511627776)), (45/137438953472), by norm_num⟩
  | 11 => ⟨((-305225311/1099511627776), (563187065/2199023255552)), (201/2199023255552), by norm_num⟩
  | 12 => ⟨((619510205/8796093022208), (-571545219/8796093022208)), (103/4398046511104), by norm_num⟩
  | 13 => ⟨((-580342375/35184372088832), (535409921/35184372088832)), (195/35184372088832), by norm_num⟩
  | 14 => ⟨((1009637361/281474976710656), (-931467153/281474976710656)), (171/140737488355328), by norm_num⟩
  | 15 => ⟨((-12807765/17592186044416), (378116353/562949953421312)), (279/1125899906842624), by norm_num⟩
  | 16 => ⟨((623896447/4503599627370496), (-143897965/1125899906842624)), (107/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-970639660821/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444479731309617/158456325028528675187087900672), (-1147656465793/633825300114114700748351602688)), (92313/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472196495445051/9903520314283042199192993792), (-1290821025377/39614081257132168796771975168)), (25965/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236062696873879/309485009821345068724781056), (-685565068947/1237940039285380274899124224)), (220719/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770168118739231/154742504910672534362390528), (-342679309581/38685626227668133590597632)), (110369/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387148769946127/2417851639229258349412352), (-321152219115/2417851639229258349412352)), (103481/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257950443624039/604462909807314587353088), (-140449303157/75557863725914323419136)), (22639/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886430490452033/75557863725914323419136), (-912509729997/37778931862957161709568)), (36793/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648259399537189/2361183241434822606848), (-1368046208385/4722366482869645213696)), (27599/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810022772760235/295147905179352825856), (-1879896925243/590295810358705651712)), (303643/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821722651063019/73786976294838206464), (-2348122580803/73786976294838206464)), (189817/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227585953224779/1152921504606846976), (-2639235789309/9223372036854775808)), (6675/144115188075855872), by norm_num⟩
  | 6 => ⟨((99496140230043/72057594037927936), (-1318118204897/576460752303423488)), (106835/288230376151711744), by norm_num⟩
  | 5 => ⟨((596395735453145/72057594037927936), (-1151668519059/72057594037927936)), (374081/144115188075855872), by norm_num⟩
  | 4 => ⟨((744479101568017/18014398509481984), (-431034638033/4503599627370496)), (140359/9007199254740992), by norm_num⟩
  | 3 => ⟨((185739620334159/1125899906842624), (-4298596717401/9007199254740992)), (351175/4503599627370496), by norm_num⟩
  | 2 => ⟨((555322856981023/1125899906842624), (-1070255593567/562949953421312)), (703185/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206180512514215/2251799813685248), (-6377772747643/1125899906842624)), (2113753/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080566191450471/1125899906842624), (-25163097264155/2251799813685248)), (4244429/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080566191450471/1125899906842624), (-25163097264155/2251799813685248)), (16191211709029387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2073834435271839/2251799813685248), (-48299839107503/2251799813685248)), (32195/8796093022208), by norm_num⟩
  | 2 => ⟨((1908898102014981/2251799813685248), (-88965163733005/2251799813685248)), (15534651/2251799813685248), by norm_num⟩
  | 3 => ⟨((1614698225579739/2251799813685248), (-37708820998047/562949953421312)), (27565603/2251799813685248), by norm_num⟩
  | 4 => ⟨((1147748152871377/2251799813685248), (-108159466013281/1125899906842624)), (43225865/2251799813685248), by norm_num⟩
  | 5 => ⟨((1128459052483195/4503599627370496), (-441033262647387/4503599627370496)), (104739295/4503599627370496), by norm_num⟩
  | 6 => ⟨((958264129708893/18014398509481984), (-27627232595009/562949953421312)), (36501363/2251799813685248), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-1066645095/16777216)), (1/8388608), by norm_num⟩, -10, term21ValuePoly, term21ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 16 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile016Terms2
