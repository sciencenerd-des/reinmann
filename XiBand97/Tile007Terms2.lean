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
namespace Reinmann.XiBand97.Tile007Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11351/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11351/640))
  have he : value ((69/80), (11351/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-412505271/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((760873003022203/18014398509481984), (365576666356297/4503599627370496)), (110849249/9007199254740992), by norm_num⟩
  | 1 => ⟨((-502964951/4294967296), (-966638319/4294967296)), (149/4294967296), by norm_num⟩
  | 2 => ⟨((697257475/4294967296), (1340045251/4294967296)), (209/4294967296), by norm_num⟩
  | 3 => ⟨((-644402737/4294967296), (-1238464783/4294967296)), (49/1073741824), by norm_num⟩
  | 4 => ⟨((111666485/1073741824), (858438373/4294967296)), (69/2147483648), by norm_num⟩
  | 5 => ⟨((-495368379/8589934592), (-952038621/8589934592)), (155/8589934592), by norm_num⟩
  | 6 => ⟨((228908797/8589934592), (879870515/17179869184)), (145/17179869184), by norm_num⟩
  | 7 => ⟨((-725337085/68719476736), (-1394010895/68719476736)), (233/68719476736), by norm_num⟩
  | 8 => ⟨((502765355/137438953472), (483127361/68719476736)), (41/34359738368), by norm_num⟩
  | 9 => ⟨((-154884617/137438953472), (-595339321/274877906944)), (51/137438953472), by norm_num⟩
  | 10 => ⟨((171772537/549755813888), (660252435/1099511627776)), (57/549755813888), by norm_num⟩
  | 11 => ⟨((-346366981/4398046511104), (-332837901/2199023255552)), (29/1099511627776), by norm_num⟩
  | 12 => ⟨((160055531/8796093022208), (307607537/8796093022208)), (217/35184372088832), by norm_num⟩
  | 13 => ⟨((-546176197/140737488355328), (-524842577/70368744177664)), (187/140737488355328), by norm_num⟩
  | 14 => ⟨((216331709/281474976710656), (415763603/281474976710656)), (75/281474976710656), by norm_num⟩
  | 15 => ⟨((-639785447/4503599627370496), (-1229590909/4503599627370496)), (7/140737488355328), by norm_num⟩
  | 16 => ⟨((443465479/18014398509481984), (53267967/1125899906842624)), (157/18014398509481984), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (710589091959/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889139711669869/316912650057057350374175801344), (1681011309211/633825300114114700748351602688)), (46183/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944595704386355/19807040628566084398385987584), (1890744499977/39614081257132168796771975168)), (51961/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236116521425841/309485009821345068724781056), (1004213015339/1237940039285380274899124224)), (55215/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770598524290099/154742504910672534362390528), (1003937501493/77371252455336267181195264)), (27611/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387249595573163/2417851639229258349412352), (58806173365/302231454903657293676544)), (25889/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157287891341659/75557863725914323419136), (822993905427/302231454903657293676544)), (90627/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887003227391389/75557863725914323419136), (1336816856333/37778931862957161709568)), (73647/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296948019851711/4722366482869645213696), (62633323145/147573952589676412928)), (3453/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1620635185146663/590295810358705651712), (2754308826855/590295810358705651712)), (75985/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911229446474739/36893488147419103232), (1720275753383/36893488147419103232)), (95011/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455378697163289/2305843009213693952), (1933706502387/4611686018427387904)), (6683/288230376151711744), by norm_num⟩
  | 6 => ⟨((1592764021818813/1152921504606846976), (1931703751139/576460752303423488)), (106979/576460752303423488), by norm_num⟩
  | 5 => ⟨((596756235767523/72057594037927936), (421997573913/18014398509481984)), (2927/2251799813685248), by norm_num⟩
  | 4 => ⟨((1490036599995655/36028797018963968), (5054981968295/36028797018963968)), (281221/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487259540975643/9007199254740992), (1575756530915/2251799813685248)), (175965/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223960388570693/4503599627370496), (3139766278537/1125899906842624)), (352535/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210143663724833/2251799813685248), (18721537978325/2251799813685248)), (265161/562949953421312), by norm_num⟩
  | 0 => ⟨((271112340271251/281474976710656), (4622159825661/281474976710656)), (2133505/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((271112340271251/281474976710656), (4622159825661/281474976710656)), (8138675698287200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044221231238405/1125899906842624), (71231884671915/2251799813685248)), (1044997/562949953421312), by norm_num⟩
  | 2 => ⟨((241835326080369/281474976710656), (66064350714913/1125899906842624)), (4008977/1125899906842624), by norm_num⟩
  | 3 => ⟨((1654471583043089/2251799813685248), (113521237192265/1125899906842624)), (14718537/2251799813685248), by norm_num⟩
  | 4 => ⟨((149087849505983/281474976710656), (41703898336131/281474976710656)), (24596445/2251799813685248), by norm_num⟩
  | 5 => ⟨((1164606358877807/4503599627370496), (353426487376391/2251799813685248)), (33344341/2251799813685248), by norm_num⟩
  | 6 => ⟨((760873003022203/18014398509481984), (365576666356297/4503599627370496)), (110849249/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-412505271/8388608)), (1/16777216), by norm_num⟩, -8, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-81995171/33554432), (-1686099967/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((782120095094039/9007199254740992), (6174437253337/4503599627370496)), (6152143/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1056629701/4294967296), (-4170775/1073741824)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((374207171/1073741824), (23633391/4294967296)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((-1413611667/4294967296), (-2789935/536870912)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((2002531719/8589934592), (7904481/2147483648)), (137/8589934592), by norm_num⟩
  | 5 => ⟨((-567359959/4294967296), (-17916065/8589934592)), (79/8589934592), by norm_num⟩
  | 6 => ⟨((535817269/8589934592), (16920011/17179869184)), (19/4294967296), by norm_num⟩
  | 7 => ⟨((-867476935/34359738368), (-27393143/68719476736)), (125/68719476736), by norm_num⟩
  | 8 => ⟨((614436807/68719476736), (19402655/137438953472)), (45/68719476736), by norm_num⟩
  | 9 => ⟨((-1547404943/549755813888), (-12215969/274877906944)), (115/549755813888), by norm_num⟩
  | 10 => ⟨((1753651333/2199023255552), (27688357/2199023255552)), (33/549755813888), by norm_num⟩
  | 11 => ⟨((-903357883/4398046511104), (-14263095/4398046511104)), (69/4398046511104), by norm_num⟩
  | 12 => ⟨((853135203/17592186044416), (26940261/35184372088832)), (33/8796093022208), by norm_num⟩
  | 13 => ⟨((-1487454795/140737488355328), (-23485387/140737488355328)), (117/140737488355328), by norm_num⟩
  | 14 => ⟨((602039539/281474976710656), (19011175/562949953421312)), (97/562949953421312), by norm_num⟩
  | 15 => ⟨((-1819420219/4503599627370496), (-28726781/4503599627370496)), (149/4503599627370496), by norm_num⟩
  | 16 => ⟨((1288701411/18014398509481984), (20347275/18014398509481984)), (107/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197599080584755/1267650600228229401496703205376), (10282596893/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778200375913203/633825300114114700748351602688), (24323015151/633825300114114700748351602688)), (92203/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118068911461905/2475880078570760549798248448), (13678804427/19807040628566084398385987584)), (103729/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888837929248573/2475880078570760549798248448), (29060217453/2475880078570760549798248448)), (27553/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110656527103349/9671406556917033397649408), (14526037025/77371252455336267181195264)), (27553/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774455166602527/4835703278458516698824704), (1701729393/604462909807314587353088)), (25831/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314556562136149/151115727451828646838272), (23815566003/604462909807314587353088)), (90409/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471719648752019/18889465931478580854784), (38684092169/75557863725914323419136)), (146915/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296854808833759/4722366482869645213696), (28998899581/4722366482869645213696)), (110187/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810253723664173/295147905179352825856), (39850475875/590295810358705651712)), (151507/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911149930415817/36893488147419103232), (24889301781/36893488147419103232)), (189385/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455334189091777/2305843009213693952), (55953544557/9223372036854775808)), (53265/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592587086043679/1152921504606846976), (27947187765/576460752303423488)), (213063/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298339720874025/36028797018963968), (48841097947/144115188075855872)), (186433/144115188075855872), by norm_num⟩
  | 4 => ⟨((186226084056631/4503599627370496), (4570556039/2251799813685248)), (139827/18014398509481984), by norm_num⟩
  | 3 => ⟨((371744727802033/2251799813685248), (45589640843/4503599627370496)), (174789/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111705952617021/2251799813685248), (181664937765/4503599627370496)), (699189/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104676330148667/1125899906842624), (270769945485/2251799813685248)), (1048877/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167442294693933/2251799813685248), (534669519665/2251799813685248)), (524545/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167442294693933/2251799813685248), (534669519665/2251799813685248)), (2000980379344749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2086244872393109/2251799813685248), (1029279177983/2251799813685248)), (505019/281474976710656), by norm_num⟩
  | 2 => ⟨((1932861252460911/2251799813685248), (953605375699/1125899906842624)), (7489925/2251799813685248), by norm_num⟩
  | 3 => ⟨((207386829032647/281474976710656), (1637078811025/1125899906842624)), (12870835/2251799813685248), by norm_num⟩
  | 4 => ⟨((1222392977369019/2251799813685248), (1206176788653/562949953421312)), (19003533/2251799813685248), by norm_num⟩
  | 5 => ⟨((1327135124748551/4503599627370496), (654774916915/281474976710656)), (41427257/4503599627370496), by norm_num⟩
  | 6 => ⟨((782120095094039/9007199254740992), (6174437253337/4503599627370496)), (6152143/1125899906842624), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81995171/33554432), (-1686099967/33554432)), (1/16777216), by norm_num⟩, -8, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-1720116043/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((807149089371605/18014398509481984), (-312866562995945/4503599627370496)), (95832179/9007199254740992), by norm_num⟩
  | 1 => ⟨((-556221231/4294967296), (862408331/4294967296)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((803843069/4294967296), (-623170171/2147483648)), (49/1073741824), by norm_num⟩
  | 3 => ⟨((-774468435/4294967296), (600397821/2147483648)), (191/4294967296), by norm_num⟩
  | 4 => ⟨((559625423/4294967296), (-867686453/4294967296)), (35/1073741824), by norm_num⟩
  | 5 => ⟨((-647010207/8589934592), (125396821/1073741824)), (41/2147483648), by norm_num⟩
  | 6 => ⟨((623366677/17179869184), (-966515813/17179869184)), (5/536870912), by norm_num⟩
  | 7 => ⟨((-257394491/17179869184), (399084287/17179869184)), (67/17179869184), by norm_num⟩
  | 8 => ⟨((92995721/17179869184), (-4505867/536870912)), (49/34359738368), by norm_num⟩
  | 9 => ⟨((-238926405/137438953472), (740899881/274877906944)), (127/274877906944), by norm_num⟩
  | 10 => ⟨((552468907/1099511627776), (-856590437/1099511627776)), (149/1099511627776), by norm_num⟩
  | 11 => ⟨((-290334641/2199023255552), (225078619/1099511627776)), (159/4398046511104), by norm_num⟩
  | 12 => ⟨((559450031/17592186044416), (-54213407/1099511627776)), (155/17592186044416), by norm_num⟩
  | 13 => ⟨((-497544175/70368744177664), (771430895/70368744177664)), (35/17592186044416), by norm_num⟩
  | 14 => ⟨((821764361/562949953421312), (-1274126899/562949953421312)), (117/281474976710656), by norm_num⟩
  | 15 => ⟨((-633387867/2251799813685248), (982053441/2251799813685248)), (91/1125899906842624), by norm_num⟩
  | 16 => ⟨((457681601/9007199254740992), (-709624883/9007199254740992)), (133/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-162495983795/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778123160482067/633825300114114700748351602688), (-384345564425/158456325028528675187087900672)), (1443/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889015664348065/39614081257132168796771975168), (-54036916255/1237940039285380274899124224)), (51953/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472186376928337/618970019642690137449562112), (-1836788050469/2475880078570760549798248448)), (110411/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770411933410527/154742504910672534362390528), (-918131395325/77371252455336267181195264)), (13803/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548823530674483/9671406556917033397649408), (-1720938479057/9671406556917033397649408)), (6471/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258150212861397/604462909807314587353088), (-11759871161/4722366482869645213696)), (5663/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((471688720174109/18889465931478580854784), (-305626008657/9444732965739290427392)), (73631/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296761886492079/4722366482869645213696), (-458210510581/1180591620717411303424)), (110469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620379457453445/590295810358705651712), (-2518673444083/590295810358705651712)), (75965/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455534885396791/18446744073709551616), (-3146116835551/73786976294838206464)), (189967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910577970898799/4611686018427387904), (-884081166729/2305843009213693952)), (213787/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592405703613929/1152921504606846976), (-883126884313/288230376151711744)), (213881/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149149942121025/18014398509481984), (-24114492923/1125899906842624)), (187251/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489568383699223/36028797018963968), (-4621417797571/36028797018963968)), (140543/18014398509481984), by norm_num⟩
  | 3 => ⟨((371669085111897/2251799813685248), (-5761813331225/9007199254740992)), (21983/562949953421312), by norm_num⟩
  | 2 => ⟨((2222800177575339/4503599627370496), (-2869716982729/1125899906842624)), (176141/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104209377215495/1125899906842624), (-17106817103265/2251799813685248)), (529817/1125899906842624), by norm_num⟩
  | 0 => ⟨((2165510126105711/2251799813685248), (-8442539778309/562949953421312)), (2130481/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2165510126105711/2251799813685248), (-8442539778309/562949953421312)), (8127140053755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2082020637059685/2251799813685248), (-64952151674825/2251799813685248)), (4161583/2251799813685248), by norm_num⟩
  | 2 => ⟨((480792200622829/562949953421312), (-120109895548041/2251799813685248)), (3967851/1125899906842624), by norm_num⟩
  | 3 => ⟨((102255755414985/140737488355328), (-25645219724311/281474976710656)), (7200841/1125899906842624), by norm_num⟩
  | 4 => ⟨((1170044492006603/2251799813685248), (-18633068888311/140737488355328)), (23551963/2251799813685248), by norm_num⟩
  | 5 => ⟨((1136977757888391/4503599627370496), (-309818227918127/2251799813685248)), (30711763/2251799813685248), by norm_num⟩
  | 6 => ⟨((807149089371605/18014398509481984), (-312866562995945/4503599627370496)), (95832179/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1720116043/33554432)), (1/16777216), by norm_num⟩, -8, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-876146245/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-535251103357519/18014398509481984), (-82293395549973/1125899906842624)), (125780983/9007199254740992), by norm_num⟩
  | 1 => ⟨((375751069/4294967296), (924331213/4294967296)), (89/2147483648), by norm_num⟩
  | 2 => ⟨((-553188047/4294967296), (-1360818427/4294967296)), (33/536870912), by norm_num⟩
  | 3 => ⟨((16966963/134217728), (1335615607/4294967296)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((-199832749/2147483648), (-61447479/268435456)), (97/2147483648), by norm_num⟩
  | 5 => ⟨((117679067/2147483648), (1157941455/8589934592)), (115/4294967296), by norm_num⟩
  | 6 => ⟨((-461998443/17179869184), (-1136495985/17179869184)), (57/4294967296), by norm_num⟩
  | 7 => ⟨((388664635/34359738368), (478049011/17179869184)), (97/17179869184), by norm_num⟩
  | 8 => ⟨((-572199651/137438953472), (-703793071/68719476736)), (9/4294967296), by norm_num⟩
  | 9 => ⟨((187200773/137438953472), (921011445/274877906944)), (95/137438953472), by norm_num⟩
  | 10 => ⟨((-220480501/549755813888), (-33898275/34359738368)), (113/549755813888), by norm_num⟩
  | 11 => ⟨((236069593/2199023255552), (1161441771/4398046511104)), (61/1099511627776), by norm_num⟩
  | 12 => ⟨((-7240547/274877906944), (-569965737/8796093022208)), (121/8796093022208), by norm_num⟩
  | 13 => ⟨((419827177/70368744177664), (32273641/2199023255552)), (221/70368744177664), by norm_num⟩
  | 14 => ⟨((-353187287/281474976710656), (-434412647/140737488355328)), (187/281474976710656), by norm_num⟩
  | 15 => ⟨((554633821/2251799813685248), (682187483/1125899906842624)), (37/281474976710656), by norm_num⟩
  | 16 => ⟨((-797405/17592186044416), (-251082427/2251799813685248)), (55/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (-2549084968705/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778047720260267/633825300114114700748351602688), (-3014394647059/633825300114114700748351602688)), (92497/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944465306683893/19807040628566084398385987584), (-3390441469779/39614081257132168796771975168)), (104079/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944327449402871/1237940039285380274899124224), (-3601410310695/2475880078570760549798248448)), (55303/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885160526145857/77371252455336267181195264), (-1800180097399/77371252455336267181195264)), (110631/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548738040638419/9671406556917033397649408), (-3374222283049/9671406556917033397649408)), (51871/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258075120359713/604462909807314587353088), (-2951329490083/604462909807314587353088)), (90801/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58957259831189/2361183241434822606848), (-4793820614921/75557863725914323419136)), (147601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648334744649835/2361183241434822606848), (-1796768856523/2361183241434822606848)), (110745/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620251644370139/590295810358705651712), (-4938145825131/590295810358705651712)), (19043/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227747328334147/9223372036854775808), (-6168232215649/73786976294838206464)), (23817/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820973336261645/9223372036854775808), (-6933146835959/9223372036854775808)), (214499/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99513820766737/72057594037927936), (-3462755237429/576460752303423488)), (214681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193035831697811/144115188075855872), (-6051239893543/144115188075855872)), (47013/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489318430563459/36028797018963968), (-566232444701/2251799813685248)), (35311/4503599627370496), by norm_num⟩
  | 3 => ⟨((743178121033071/4503599627370496), (-11294703920973/9007199254740992)), (353831/9007199254740992), by norm_num⟩
  | 2 => ⟨((277767143535063/562949953421312), (-22499777873899/4503599627370496)), (709829/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207367611549715/2251799813685248), (-2095394260821/140737488355328)), (1070177/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081592162103281/1125899906842624), (-33081735556341/1125899906842624)), (270273/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081592162103281/1125899906842624), (-33081735556341/1125899906842624)), (1031009675146007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2076112089170277/2251799813685248), (-127119455891431/2251799813685248)), (1070313/562949953421312), by norm_num⟩
  | 2 => ⟨((1906955504941283/2251799813685248), (-234402931860121/2251799813685248)), (8377823/2251799813685248), by norm_num⟩
  | 3 => ⟨((1590520854293783/2251799813685248), (-24813260406655/140737488355328)), (15933853/2251799813685248), by norm_num⟩
  | 4 => ⟨((526720428959239/1125899906842624), (-560845707863777/2251799813685248)), (878993/70368744177664), by norm_num⟩
  | 5 => ⟨((706270360509007/4503599627370496), (-524751605414687/2251799813685248)), (80657777/4503599627370496), by norm_num⟩
  | 6 => ⟨((-535251103357519/18014398509481984), (-82293395549973/1125899906842624)), (125780983/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-876146245/16777216)), (1/16777216), by norm_num⟩, -8, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-222852265/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1308741646417475/18014398509481984), (-184597847707189/9007199254740992)), (118945281/9007199254740992), by norm_num⟩
  | 1 => ⟨((116844165/536870912), (263693681/4294967296)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((-87508459/268435456), (-394977835/4294967296)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((699071773/2147483648), (394415949/4294967296)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-32722373/134217728), (-295391147/4294967296)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((627375801/4294967296), (353965117/8589934592)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((-1252966623/17179869184), (-353461575/17179869184)), (15/1073741824), by norm_num⟩
  | 7 => ⟨((536221793/17179869184), (302536071/34359738368)), (207/34359738368), by norm_num⟩
  | 8 => ⟨((-1606376931/137438953472), (-56644817/17179869184)), (39/17179869184), by norm_num⟩
  | 9 => ⟨((1069394493/274877906944), (301675923/274877906944)), (105/137438953472), by norm_num⟩
  | 10 => ⟨((-640723919/549755813888), (-45187015/137438953472)), (127/549755813888), by norm_num⟩
  | 11 => ⟨((1395954417/4398046511104), (196899199/2199023255552)), (279/4398046511104), by norm_num⟩
  | 12 => ⟨((-1393968567/17592186044416), (-196619095/8796093022208)), (281/17592186044416), by norm_num⟩
  | 13 => ⟨((1284909731/70368744177664), (362472719/70368744177664)), (261/70368744177664), by norm_num⟩
  | 14 => ⟨((-1099784443/281474976710656), (-310248921/281474976710656)), (225/281474976710656), by norm_num⟩
  | 15 => ⟨((878575933/1125899906842624), (247846055/1125899906842624)), (91/562949953421312), by norm_num⟩
  | 16 => ⟨((-1315989139/9007199254740992), (-371240213/9007199254740992)), (137/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-1867057972013/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888986996539525/316912650057057350374175801344), (-137981824579/19807040628566084398385987584)), (23159/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888847381234423/39614081257132168796771975168), (-4966209975905/39614081257132168796771975168)), (104243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888566076842735/2475880078570760549798248448), (-5275204812089/2475880078570760549798248448)), (55395/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885115897249387/77371252455336267181195264), (-1318409409909/38685626227668133590597632)), (110827/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774326949386211/4835703278458516698824704), (-4942370558645/9671406556917033397649408)), (103939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258001033973943/604462909807314587353088), (-4322909950775/604462909807314587353088)), (90985/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886511058414425/75557863725914323419136), (-3510804533067/37778931862957161709568)), (147923/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648288895249065/2361183241434822606848), (-5263478082613/4722366482869645213696)), (55503/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620124330657577/590295810358705651712), (-1808212488669/147573952589676412928)), (152737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113863602859141/4611686018427387904), (-4517208452083/36893488147419103232)), (47769/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820789709265321/9223372036854775808), (-5077293198997/4611686018427387904)), (215175/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199004294782819/144115188075855872), (-10143178122579/1152921504606846976)), (107721/576460752303423488), by norm_num⟩
  | 5 => ⟨((596434437046647/72057594037927936), (-2215614215623/36028797018963968)), (47203/36028797018963968), by norm_num⟩
  | 4 => ⟨((744530479252169/18014398509481984), (-6634031552709/18014398509481984)), (283821/36028797018963968), by norm_num⟩
  | 3 => ⟨((185752768230871/1125899906842624), (-4135074535447/2251799813685248)), (44479/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110716205919513/2251799813685248), (-16473243302203/2251799813685248)), (357419/2251799813685248), by norm_num⟩
  | 1 => ⟨((551554982477169/562949953421312), (-24542635206311/1125899906842624)), (540109/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080265665657433/1125899906842624), (-48418798731581/1125899906842624)), (1096207/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080265665657433/1125899906842624), (-48418798731581/1125899906842624)), (4181697849753951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((258599703501547/281474976710656), (-92912639079587/1125899906842624)), (2197837/1125899906842624), by norm_num⟩
  | 2 => ⟨((942666520768287/1125899906842624), (-341446777234857/2251799813685248)), (8802371/2251799813685248), by norm_num⟩
  | 3 => ⟨((1526731974543995/2251799813685248), (-571756767306523/2251799813685248)), (17409135/2251799813685248), by norm_num⟩
  | 4 => ⟨((444978436572141/1125899906842624), (-775308118424771/2251799813685248)), (32447711/2251799813685248), by norm_num⟩
  | 5 => ⟨((169571519103141/4503599627370496), (-1225669856802167/4503599627370496)), (95983733/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1308741646417475/18014398509481984), (-184597847707189/9007199254740992)), (118945281/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-222852265/4194304)), (1/16777216), by norm_num⟩, -8, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-88110603/33554432), (-1811854089/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1083088075261371/18014398509481984), (181447785401161/4503599627370496)), (119028911/9007199254740992), by norm_num⟩
  | 1 => ⟨((393090957/2147483648), (-263415267/2147483648)), (87/2147483648), by norm_num⟩
  | 2 => ⟨((-1196774239/4294967296), (801973691/4294967296)), (267/4294967296), by norm_num⟩
  | 3 => ⟨((1214535341/4294967296), (-50867227/268435456)), (273/4294967296), by norm_num⟩
  | 4 => ⟨((-115552503/536870912), (77433207/536870912)), (105/2147483648), by norm_num⟩
  | 5 => ⟨((562883501/4294967296), (-188597709/2147483648)), (129/4294967296), by norm_num⟩
  | 6 => ⟨((-1142474299/17179869184), (765586609/17179869184)), (33/2147483648), by norm_num⟩
  | 7 => ⟨((496898377/17179869184), (-41622243/2147483648)), (29/4294967296), by norm_num⟩
  | 8 => ⟨((-756409129/68719476736), (506879411/68719476736)), (89/34359738368), by norm_num⟩
  | 9 => ⟨((255878285/68719476736), (-342934609/137438953472)), (243/274877906944), by norm_num⟩
  | 10 => ⟨((-38951359/34359738368), (417628845/549755813888)), (149/549755813888), by norm_num⟩
  | 11 => ⟨((172492053/549755813888), (-462356505/2199023255552)), (167/2199023255552), by norm_num⟩
  | 12 => ⟨((-700207901/8796093022208), (469218251/8796093022208)), (171/8796093022208), by norm_num⟩
  | 13 => ⟨((655938051/35184372088832), (-109888115/8796093022208)), (81/17592186044416), by norm_num⟩
  | 14 => ⟨((-142644151/35184372088832), (382350665/140737488355328)), (71/70368744177664), by norm_num⟩
  | 15 => ⟨((926471079/1125899906842624), (-620840095/1125899906842624)), (233/1125899906842624), by norm_num⟩
  | 16 => ⟨((-705165497/4503599627370496), (29533775/281474976710656)), (179/4503599627370496), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (3323233374281/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888955676026579/316912650057057350374175801344), (3929295724733/633825300114114700748351602688)), (92587/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((14756070678759/309485009821345068724781056), (17263427259/154742504910672534362390528)), (52093/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888491526619905/2475880078570760549798248448), (2347196420455/1237940039285380274899124224)), (55363/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885078723317601/77371252455336267181195264), (1173244101997/38685626227668133590597632)), (110759/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193573051563121/1208925819614629174706176), (4398160839483/9671406556917033397649408)), (103871/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628970224086819/302231454903657293676544), (961721665031/151115727451828646838272)), (45461/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886413008657833/75557863725914323419136), (48815403741/590295810358705651712)), (147811/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296504604715593/4722366482869645213696), (1170953250975/1180591620717411303424)), (27729/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810012135385393/295147905179352825856), (6436237894799/590295810358705651712)), (152601/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821693425544785/73786976294838206464), (4019646578315/36893488147419103232)), (190889/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455162783690231/2305843009213693952), (2258988579363/2305843009213693952)), (53735/2305843009213693952), by norm_num⟩
  | 6 => ⟨((397974311847945/288230376151711744), (4512824586645/576460752303423488)), (107589/576460752303423488), by norm_num⟩
  | 5 => ⟨((596375272346883/72057594037927936), (3942930341923/72057594037927936)), (188549/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488886739703539/36028797018963968), (1475706712143/4503599627370496)), (283359/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485810081817945/9007199254740992), (14716638338129/9007199254740992)), (355139/9007199254740992), by norm_num⟩
  | 2 => ⟨((69407041348889/140737488355328), (29312236435815/4503599627370496)), (356551/2251799813685248), by norm_num⟩
  | 1 => ⟨((137853224031475/140737488355328), (43666615170371/2251799813685248)), (538369/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079780965961277/1125899906842624), (86131436933797/2251799813685248)), (1090971/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1079780965961277/1125899906842624), (86131436933797/2251799813685248)), (4161724094871139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2067807753194725/2251799813685248), (82603334103489/1125899906842624)), (4352051/2251799813685248), by norm_num⟩
  | 2 => ⟨((1886728844692061/2251799813685248), (303415629863453/2251799813685248)), (4315745/1125899906842624), by norm_num⟩
  | 3 => ⟨((1539961353523901/2251799813685248), (508449301145385/2251799813685248)), (16790313/2251799813685248), by norm_num⟩
  | 4 => ⟨((938342860528933/2251799813685248), (86929605068745/281474976710656)), (30547527/2251799813685248), by norm_num⟩
  | 5 => ⟨((352477979880481/4503599627370496), (579588105756959/2251799813685248)), (44327147/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1083088075261371/18014398509481984), (181447785401161/4503599627370496)), (119028911/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-1811854089/33554432)), (1/16777216), by norm_num⟩, -9, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile007Terms2
