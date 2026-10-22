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
namespace Reinmann.XiBand97.Tile047Terms2
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
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-20060163/8388608), (-5407667549/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((746416441463291/18014398509481984), (1469738414272483/18014398509481984)), (111364567/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1973634537/17179869184), (-3886203911/17179869184)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((1368019215/8589934592), (673427821/2147483648)), (413/17179869184), by norm_num⟩
  | 3 => ⟨((-158039777/1073741824), (-4979035685/17179869184)), (3/134217728), by norm_num⟩
  | 4 => ⟨((876358607/8589934592), (3451204547/17179869184)), (67/4294967296), by norm_num⟩
  | 5 => ⟨((-242978199/4294967296), (-1913754161/17179869184)), (299/34359738368), by norm_num⟩
  | 6 => ⟨((1796476305/68719476736), (3537368803/68719476736)), (139/34359738368), by norm_num⟩
  | 7 => ⟨((-2846222825/274877906944), (-700547775/34359738368)), (443/274877906944), by norm_num⟩
  | 8 => ⟨((1972851327/549755813888), (3884661721/549755813888)), (309/549755813888), by norm_num⟩
  | 9 => ⟨((-151941815/137438953472), (-4786919679/2199023255552)), (383/2199023255552), by norm_num⟩
  | 10 => ⟨((2696141841/8796093022208), (5308863807/8796093022208)), (427/8796093022208), by norm_num⟩
  | 11 => ⟨((-339786021/4398046511104), (-1338117811/8796093022208)), (433/35184372088832), by norm_num⟩
  | 12 => ⟨((1256115853/70368744177664), (4946733803/140737488355328)), (403/140737488355328), by norm_num⟩
  | 13 => ⟨((-535798869/140737488355328), (-2110039747/281474976710656)), (173/281474976710656), by norm_num⟩
  | 14 => ⟨((424442829/562949953421312), (835753201/562949953421312)), (69/562949953421312), by norm_num⟩
  | 15 => ⟨((-2510518189/18014398509481984), (-2471679893/9007199254740992)), (205/9007199254740992), by norm_num⟩
  | 16 => ⟨((1740158605/72057594037927936), (1713237949/36028797018963968)), (143/36028797018963968), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (717011616991/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889139697922245/316912650057057350374175801344), (1696204811805/633825300114114700748351602688)), (5773/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889191376314733/39614081257132168796771975168), (1907833606765/39614081257132168796771975168)), (51963/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888932134902707/2475880078570760549798248448), (2026578774445/2475880078570760549798248448)), (55217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770598485518771/154742504910672534362390528), (253252845257/19342813113834066795298816)), (6903/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548998343537285/9671406556917033397649408), (949402888551/4835703278458516698824704)), (51779/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157287886802133/75557863725914323419136), (1660864718619/604462909807314587353088)), (45315/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887003163871909/75557863725914323419136), (2697798767113/75557863725914323419136)), (36825/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162118496034235/590295810358705651712), (2022381454555/4722366482869645213696)), (27625/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405158776958859/147573952589676412928), (2779203015363/590295810358705651712)), (18997/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455614696684173/18446744073709551616), (3471648114735/73786976294838206464)), (95015/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821514656022279/9223372036854775808), (1951183828863/4611686018427387904)), (26733/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398190968198663/288230376151711744), (3898325895739/1152921504606846976)), (13373/144115188075855872), by norm_num⟩
  | 5 => ⟨((37297260085705/4503599627370496), (3406493433889/144115188075855872)), (93669/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490036340129271/36028797018963968), (5100669829307/36028797018963968)), (70309/18014398509481984), by norm_num⟩
  | 3 => ⟨((743629576107495/4503599627370496), (3179996860449/4503599627370496)), (21997/1125899906842624), by norm_num⟩
  | 2 => ⟨((277994927537033/562949953421312), (6336287262303/2251799813685248)), (176281/2251799813685248), by norm_num⟩
  | 1 => ⟨((552535434505395/562949953421312), (9445370395331/1125899906842624)), (530377/2251799813685248), by norm_num⟩
  | 0 => ⟨((2168892999036905/2251799813685248), (37311457924423/2251799813685248)), (266729/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168892999036905/2251799813685248), (37311457924423/2251799813685248)), (1017490389110374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((261052551596633/281474976710656), (71875447705719/2251799813685248)), (1045313/1125899906842624), by norm_num⟩
  | 2 => ⟨((967300404331865/1125899906842624), (66660522508955/1125899906842624)), (250709/140737488355328), by norm_num⟩
  | 3 => ⟨((1654190468086765/2251799813685248), (229081643879729/2251799813685248)), (3683785/1125899906842624), by norm_num⟩
  | 4 => ⟨((1191876688520597/2251799813685248), (336570479681603/2251799813685248)), (770225/140737488355328), by norm_num⟩
  | 5 => ⟨((1161107079679731/4503599627370496), (712586449894377/4503599627370496)), (2091213/281474976710656), by norm_num⟩
  | 6 => ⟨((746416441463291/18014398509481984), (1469738414272483/18014398509481984)), (111364567/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-5407667549/67108864)), (1/33554432), by norm_num⟩, -13, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-163990341/67108864), (-5525910041/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((1234867227145057/18014398509481984), (-960500055007257/18014398509481984)), (82845775/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1668282655/8589934592), (2595235417/17179869184)), (113/8589934592), by norm_num⟩
  | 2 => ⟨((590825085/2147483648), (-3676427807/17179869184)), (323/17179869184), by norm_num⟩
  | 3 => ⟨((-2231911353/8589934592), (1736017387/8589934592)), (307/17179869184), by norm_num⟩
  | 4 => ⟨((1580870257/8589934592), (-2459253813/17179869184)), (219/17179869184), by norm_num⟩
  | 5 => ⟨((-1791577083/17179869184), (21773721/268435456)), (125/17179869184), by norm_num⟩
  | 6 => ⟨((845986683/17179869184), (-2632089467/68719476736)), (119/34359738368), by norm_num⟩
  | 7 => ⟨((-2739269439/137438953472), (2130648857/137438953472)), (195/137438953472), by norm_num⟩
  | 8 => ⟨((970116841/137438953472), (-3018291387/549755813888)), (139/274877906944), by norm_num⟩
  | 9 => ⟨((-2443153759/1099511627776), (237540651/137438953472)), (177/1099511627776), by norm_num⟩
  | 10 => ⟨((2768790333/4398046511104), (-2153610695/4398046511104)), (101/2199023255552), by norm_num⟩
  | 11 => ⟨((-2852572261/17592186044416), (1109388829/8796093022208)), (105/8796093022208), by norm_num⟩
  | 12 => ⟨((673495483/17592186044416), (-2095423489/70368744177664)), (25/8796093022208), by norm_num⟩
  | 13 => ⟨((-587125043/70368744177664), (3653404179/562949953421312)), (351/562949953421312), by norm_num⟩
  | 14 => ⟨((1901086293/1125899906842624), (-2957392421/2251799813685248)), (287/2251799813685248), by norm_num⟩
  | 15 => ⟨((-1436315481/4503599627370496), (1117189823/4503599627370496)), (219/9007199254740992), by norm_num⟩
  | 16 => ⟨((4069388187/72057594037927936), (-3165237115/72057594037927936)), (313/72057594037927936), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644697451/10141204801825835211973625643008), (-107639241015/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778199820340889/633825300114114700748351602688), (-15913482979/9903520314283042199192993792)), (46151/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889101927624491/39614081257132168796771975168), (-71595516233/2475880078570760549798248448)), (51923/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472209297935015/618970019642690137449562112), (-1216820496581/2475880078570760549798248448)), (13793/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770503650342007/154742504910672534362390528), (-152059932525/19342813113834066795298816)), (6897/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193613693777637/1208925819614629174706176), (-142510909353/1208925819614629174706176)), (12933/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258225514845275/604462909807314587353088), (-498607147477/302231454903657293676544)), (22635/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943438655865279/37778931862957161709568), (-809897331351/37778931862957161709568)), (18393/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648426883411747/2361183241434822606848), (-1214252566703/4722366482869645213696)), (55187/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620505885454957/590295810358705651712), (-208579193257/73786976294838206464)), (75893/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822297715110807/73786976294838206464), (-2084347366565/73786976294838206464)), (23721/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821334076997189/9223372036854775808), (-2342906187613/9223372036854775808)), (53385/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398146018893415/288230376151711744), (-2340427953283/1152921504606846976)), (6675/72057594037927936), by norm_num⟩
  | 5 => ⟨((596677938898811/72057594037927936), (-2045089900363/144115188075855872)), (46743/72057594037927936), by norm_num⟩
  | 4 => ⟨((46556356975063/1125899906842624), (-191379647425/2251799813685248)), (70149/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486971058735125/9007199254740992), (-1908940732353/4503599627370496)), (175495/9007199254740992), by norm_num⟩
  | 2 => ⟨((555848087194947/1125899906842624), (-3803352914551/2251799813685248)), (351359/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104656885406475/1125899906842624), (-5668843010599/1125899906842624)), (16499/70368744177664), by norm_num⟩
  | 0 => ⟨((2167326737924395/2251799813685248), (-22387495732791/2251799813685248)), (264921/562949953421312), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167326737924395/2251799813685248), (-22387495732791/2251799813685248)), (1010593416454124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2085799972276453/2251799813685248), (-21547660587749/1125899906842624)), (2060935/2251799813685248), by norm_num⟩
  | 2 => ⟨((1931212664292851/2251799813685248), (-39918388467219/1125899906842624)), (3896897/2251799813685248), by norm_num⟩
  | 3 => ⟨((826718347951297/1125899906842624), (-136940942756167/2251799813685248)), (1740131/562949953421312), by norm_num⟩
  | 4 => ⟨((18839791432151/35184372088832), (-100552091064429/1125899906842624)), (11068451/2251799813685248), by norm_num⟩
  | 5 => ⟨((156916934547663/562949953421312), (-430732239629037/4503599627370496)), (27660825/4503599627370496), by norm_num⟩
  | 6 => ⟨((1234867227145057/18014398509481984), (-960500055007257/18014398509481984)), (82845775/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-163990341/67108864), (-5525910041/67108864)), (1/33554432), by norm_num⟩, -13, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-1409348007/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-31771768424277/562949953421312), (-1088110967259521/18014398509481984)), (136268519/18014398509481984), by norm_num⟩
  | 1 => ⟨((1401248507/8589934592), (374918605/2147483648)), (377/17179869184), by norm_num⟩
  | 2 => ⟨((-4050129111/17179869184), (-2167308295/8589934592)), (547/17179869184), by norm_num⟩
  | 3 => ⟨((1951063133/8589934592), (4176217791/17179869184)), (529/17179869184), by norm_num⟩
  | 4 => ⟨((-2819648889/17179869184), (-1508852745/8589934592)), (3/134217728), by norm_num⟩
  | 5 => ⟨((3259933407/34359738368), (3488916289/34359738368)), (223/17179869184), by norm_num⟩
  | 6 => ⟨((-785201621/17179869184), (-3361421703/68719476736)), (27/4294967296), by norm_num⟩
  | 7 => ⟨((648435597/34359738368), (2775930959/137438953472)), (359/137438953472), by norm_num⟩
  | 8 => ⟨((-3748439873/549755813888), (-4011736223/549755813888)), (521/549755813888), by norm_num⟩
  | 9 => ⟨((2407641055/1099511627776), (2576757573/1099511627776)), (337/1099511627776), by norm_num⟩
  | 10 => ⟨((-695897771/1099511627776), (-2979114927/4398046511104)), (49/549755813888), by norm_num⟩
  | 11 => ⟨((2925677475/17592186044416), (3131181691/17592186044416)), (207/8796093022208), by norm_num⟩
  | 12 => ⟨((-1409382591/35184372088832), (-1508379855/35184372088832)), (401/70368744177664), by norm_num⟩
  | 13 => ⟨((2506855161/281474976710656), (670735159/70368744177664)), (359/281474976710656), by norm_num⟩
  | 14 => ⟨((-517553097/281474976710656), (-4431254767/2251799813685248)), (149/562949953421312), by norm_num⟩
  | 15 => ⟨((99728057/281474976710656), (3415459635/9007199254740992)), (461/9007199254740992), by norm_num⟩
  | 16 => ⟨((-2306009275/36028797018963968), (-2467987017/36028797018963968)), (335/36028797018963968), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-3025026806991/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889058783549265/316912650057057350374175801344), (-1788745186775/316912650057057350374175801344)), (46277/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889009063056681/39614081257132168796771975168), (-1005948584743/9903520314283042199192993792)), (52073/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236092260456117/309485009821345068724781056), (-2137096537839/1237940039285380274899124224)), (13835/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885202024176915/77371252455336267181195264), (-4272968935009/154742504910672534362390528)), (55355/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548815649004339/9671406556917033397649408), (-4004608081483/9671406556917033397649408)), (51911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258142827392329/604462909807314587353088), (-1751366087273/302231454903657293676544)), (22719/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886741963315535/75557863725914323419136), (-5689503323609/75557863725914323419136)), (36933/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296751397857059/4722366482869645213696), (-1066249109117/1180591620717411303424)), (55425/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620363736283341/590295810358705651712), (-5860908720341/590295810358705651712)), (76251/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455529486027777/18446744073709551616), (-1830236651711/18446744073709551616)), (95377/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821128973627989/9223372036854775808), (-4114467082229/4611686018427387904)), (107385/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592375403813235/1152921504606846976), (-1027503433559/144115188075855872)), (107493/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193169286347233/144115188075855872), (-3591256650341/72057594037927936)), (94179/144115188075855872), by norm_num⟩
  | 4 => ⟨((744757777803887/18014398509481984), (-5376885861433/18014398509481984)), (17689/4503599627370496), by norm_num⟩
  | 3 => ⟨((743298659451733/4503599627370496), (-6703635013403/4503599627370496)), (177317/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222603394004549/4503599627370496), (-6677478792919/1125899906842624)), (177959/2251799813685248), by norm_num⟩
  | 1 => ⟨((138001718189047/140737488355328), (-39804041631401/2251799813685248)), (537099/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164347804734399/2251799813685248), (-78569141870663/2251799813685248)), (1087139/2251799813685248), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164347804734399/2251799813685248), (-78569141870663/2251799813685248)), (4147106179244231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1038775356799597/1125899906842624), (-37758895949399/562949953421312)), (1082851/1125899906842624), by norm_num⟩
  | 2 => ⟨((953327465858731/1125899906842624), (-139348126325685/1125899906842624)), (4286753/2251799813685248), by norm_num⟩
  | 3 => ⟨((394979763052095/562949953421312), (-117989525831621/562949953421312)), (8320511/2251799813685248), by norm_num⟩
  | 4 => ⟨((504796151598151/1125899906842624), (-662275211817625/2251799813685248)), (15163575/2251799813685248), by norm_num⟩
  | 5 => ⟨((257868465463111/2251799813685248), (-593860921725997/2251799813685248)), (45033291/4503599627370496), by norm_num⟩
  | 6 => ⟨((-31771768424277/562949953421312), (-1088110967259521/18014398509481984)), (136268519/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-1409348007/16777216)), (1/33554432), by norm_num⟩, -13, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-42607059/16777216), (-5742844941/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-8109190472093/140737488355328), (121371249479399/2251799813685248)), (2035411/281474976710656), by norm_num⟩
  | 1 => ⟨((2914674867/17179869184), (-2726518539/17179869184)), (23/1073741824), by norm_num⟩
  | 2 => ⟨((-4291041145/17179869184), (1003508433/4294967296)), (17/536870912), by norm_num⟩
  | 3 => ⟨((4211569603/17179869184), (-3939692461/17179869184)), (67/2147483648), by norm_num⟩
  | 4 => ⟨((-3100177425/17179869184), (725011503/4294967296)), (397/17179869184), by norm_num⟩
  | 5 => ⟨((3651313301/34359738368), (-3415603407/34359738368)), (235/17179869184), by norm_num⟩
  | 6 => ⟨((-447961217/8589934592), (3352345269/68719476736)), (463/68719476736), by norm_num⟩
  | 7 => ⟨((3014844499/137438953472), (-2820221737/137438953472)), (49/17179869184), by norm_num⟩
  | 8 => ⟨((-2219256415/274877906944), (2075992703/274877906944)), (145/137438953472), by norm_num⟩
  | 9 => ⟨((726051677/274877906944), (-2716726149/1099511627776)), (381/1099511627776), by norm_num⟩
  | 10 => ⟨((-1710251887/2199023255552), (3199693747/4398046511104)), (451/4398046511104), by norm_num⟩
  | 11 => ⟨((1831175389/8796093022208), (-428241045/2199023255552)), (485/17592186044416), by norm_num⟩
  | 12 => ⟨((-3594522795/70368744177664), (3362479001/70368744177664)), (239/35184372088832), by norm_num⟩
  | 13 => ⟨((3256570163/281474976710656), (-1523171421/140737488355328)), (435/281474976710656), by norm_num⟩
  | 14 => ⟨((-2739649179/1125899906842624), (1281395801/562949953421312)), (23/70368744177664), by norm_num⟩
  | 15 => ⟨((2151127955/4503599627370496), (-4024524527/9007199254740992)), (145/2251799813685248), by norm_num⟩
  | 16 => ⟨((-791733125/9007199254740992), (1481245861/18014398509481984)), (429/36028797018963968), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (97269924807/316912650057057350374175801344)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111127833013867/39614081257132168796771975168), (460102262981/79228162514264337593543950336)), (23141/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236115973827421/4951760157141521099596496896), (2069997955997/19807040628566084398385987584)), (26039/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888651724259581/2475880078570760549798248448), (4397604829189/2475880078570760549798248448)), (55347/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885158840324541/77371252455336267181195264), (4396321734817/154742504910672534362390528)), (27681/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548734670471927/9671406556917033397649408), (257511794625/604462909807314587353088)), (51919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629035981198205/302231454903657293676544), (3603802634279/604462909807314587353088)), (45445/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886626791296451/75557863725914323419136), (5853625507569/75557863725914323419136)), (36939/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648332502276975/2361183241434822606848), (4387985475595/4722366482869645213696)), (55435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620244922388069/590295810358705651712), (3014926010007/295147905179352825856)), (38133/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821969392289155/73786976294838206464), (7531875952249/73786976294838206464)), (95397/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820961805783971/9223372036854775808), (2116471624753/2305843009213693952)), (107411/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199026022206937/144115188075855872), (2114137807583/288230376151711744)), (53761/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193022898530913/144115188075855872), (7388989999623/144115188075855872)), (94207/144115188075855872), by norm_num⟩
  | 4 => ⟨((744647922854525/18014398509481984), (11062524965165/36028797018963968)), (141561/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486322460998749/9007199254740992), (6895765761533/4503599627370496)), (11087/562949953421312), by norm_num⟩
  | 2 => ⟨((277756628954675/562949953421312), (3434176301789/562949953421312)), (356105/4503599627370496), by norm_num⟩
  | 1 => ⟨((2207200383444951/2251799813685248), (40936758606217/2251799813685248)), (4199/17592186044416), by norm_num⟩
  | 0 => ⟨((2162687645562517/2251799813685248), (40392366648715/1125899906842624)), (544133/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2162687645562517/2251799813685248), (40392366648715/1125899906842624)), (2075702671531295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037101888620119/1125899906842624), (155175556539801/2251799813685248)), (542121/562949953421312), by norm_num⟩
  | 2 => ⟨((237490130681763/281474976710656), (142937095719647/1125899906842624)), (4293787/2251799813685248), by norm_num⟩
  | 3 => ⟨((1566736041182335/2251799813685248), (482403799278055/2251799813685248)), (8335857/2251799813685248), by norm_num⟩
  | 4 => ⟨((246685827008019/562949953421312), (335642366669927/1125899906842624)), (3792819/562949953421312), by norm_num⟩
  | 5 => ⟨((232276048497815/2251799813685248), (588316700606837/2251799813685248)), (44683193/4503599627370496), by norm_num⟩
  | 6 => ⟨((-8109190472093/140737488355328), (121371249479399/2251799813685248)), (2035411/281474976710656), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-5742844941/67108864)), (1/33554432), by norm_num⟩, -14, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-43349291/16777216), (-730360947/8388608)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((846571504903113/18014398509481984), (532077730615079/9007199254740992)), (41582985/9007199254740992), by norm_num⟩
  | 1 => ⟨((-604653735/4294967296), (-3040242061/17179869184)), (239/17179869184), by norm_num⟩
  | 2 => ⟨((452845177/2147483648), (4553875631/17179869184)), (361/17179869184), by norm_num⟩
  | 3 => ⟨((-904401941/4294967296), (-4547397399/17179869184)), (363/17179869184), by norm_num⟩
  | 4 => ⟨((2709346083/17179869184), (3405696287/17179869184)), (137/8589934592), by norm_num⟩
  | 5 => ⟨((-405823775/4294967296), (-255063857/2147483648)), (165/17179869184), by norm_num⟩
  | 6 => ⟨((101311615/2147483648), (2037608075/34359738368)), (83/17179869184), by norm_num⟩
  | 7 => ⟨((-2774879769/137438953472), (-1744036649/68719476736)), (143/68719476736), by norm_num⟩
  | 8 => ⟨((519549805/68719476736), (1306166719/137438953472)), (27/34359738368), by norm_num⟩
  | 9 => ⟨((-2766990433/1099511627776), (-1739078131/549755813888)), (289/1099511627776), by norm_num⟩
  | 10 => ⟨((414458127/549755813888), (2083924993/2199023255552)), (349/4398046511104), by norm_num⟩
  | 11 => ⟨((-1805971763/8796093022208), (-4540277351/17592186044416)), (191/8796093022208), by norm_num⟩
  | 12 => ⟨((225425329/4398046511104), (141681827/2199023255552)), (3/549755813888), by norm_num⟩
  | 13 => ⟨((-3324622441/281474976710656), (-4179109629/281474976710656)), (89/70368744177664), by norm_num⟩
  | 14 => ⟨((1422811249/562949953421312), (3576998169/1125899906842624)), (307/1125899906842624), by norm_num⟩
  | 15 => ⟨((-568314877/1125899906842624), (-2857527695/4503599627370496)), (247/4503599627370496), by norm_num⟩
  | 16 => ⟨((3405038437/36028797018963968), (4280193969/36028797018963968)), (93/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (292691853119/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111123963684293/39614081257132168796771975168), (692188999603/316912650057057350374175801344)), (5771/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944429251551417/19807040628566084398385987584), (778538720249/19807040628566084398385987584)), (6493/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888578584764159/2475880078570760549798248448), (1653958890069/2475880078570760549798248448)), (13799/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221280634863003/19342813113834066795298816), (826734371569/77371252455336267181195264)), (55201/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774333588630695/4835703278458516698824704), (48425198843/302231454903657293676544)), (25879/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629006738136939/302231454903657293676544), (1355385206037/604462909807314587353088)), (45295/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886532819878161/75557863725914323419136), (1100762876857/37778931862957161709568)), (36807/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296595459917493/4722366482869645213696), (1650291481535/4722366482869645213696)), (55221/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810075407100783/295147905179352825856), (2267765815941/590295810358705651712)), (9493/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821854027191593/73786976294838206464), (2832631358515/73786976294838206464)), (94955/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455208783992719/2305843009213693952), (3183858409283/9223372036854775808)), (53429/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592085394482809/1152921504606846976), (1590148666563/576460752303423488)), (106899/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192919824382447/144115188075855872), (1389379560115/72057594037927936)), (93585/144115188075855872), by norm_num⟩
  | 4 => ⟨((744574964217707/18014398509481984), (1040037370387/9007199254740992)), (17559/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486155215268275/9007199254740992), (2593117358631/4503599627370496)), (43939/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221763739261395/4503599627370496), (5165364322825/2251799813685248)), (352013/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103439279238403/1125899906842624), (1924018072683/281474976710656)), (264639/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162487170317129/2251799813685248), (15185454302043/1125899906842624)), (1063627/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162487170317129/2251799813685248), (15185454302043/1125899906842624)), (4057415017134856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1038153645204597/1125899906842624), (58332627801159/2251799813685248)), (2071573/2251799813685248), by norm_num⟩
  | 2 => ⟨((1912980560066027/2251799813685248), (53786513186559/1125899906842624)), (3927581/2251799813685248), by norm_num⟩
  | 3 => ⟨((405000773716353/562949953421312), (22846736529219/281474976710656)), (3524243/1125899906842624), by norm_num⟩
  | 4 => ⟨((1150636799925325/2251799813685248), (262984541769451/2251799813685248)), (5642975/1125899906842624), by norm_num⟩
  | 5 => ⟨((1114489990190663/4503599627370496), (268762515861657/2251799813685248)), (3542513/562949953421312), by norm_num⟩
  | 6 => ⟨((846571504903113/18014398509481984), (532077730615079/9007199254740992)), (41582985/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-730360947/8388608)), (1/33554432), by norm_num⟩, -14, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-88110603/33554432), (-2969024049/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((1131955229923299/18014398509481984), (-323469441158885/9007199254740992)), (62882323/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1643306301/8589934592), (1878375953/17179869184)), (23/2147483648), by norm_num⟩
  | 2 => ⟨((5003082905/17179869184), (-714844717/4294967296)), (283/17179869184), by norm_num⟩
  | 3 => ⟨((-5077332721/17179869184), (1450907187/8589934592)), (289/17179869184), by norm_num⟩
  | 4 => ⟨((966128337/4294967296), (-2208659743/17179869184)), (111/8589934592), by norm_num⟩
  | 5 => ⟨((-73534985/536870912), (1344862829/17179869184)), (17/2147483648), by norm_num⟩
  | 6 => ⟨((1194020863/17179869184), (-682410843/17179869184)), (279/68719476736), by norm_num⟩
  | 7 => ⟨((-1038635231/34359738368), (593604321/34359738368)), (61/34359738368), by norm_num⟩
  | 8 => ⟨((3162148265/274877906944), (-903620837/137438953472)), (47/68719476736), by norm_num⟩
  | 9 => ⟨((-2139384743/549755813888), (611354203/274877906944)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((2605361941/2199023255552), (-2978050541/4398046511104)), (157/2199023255552), by norm_num⟩
  | 11 => ⟨((-2884393777/8796093022208), (824249245/4398046511104)), (11/549755813888), by norm_num⟩
  | 12 => ⟨((731800131/8796093022208), (-1672963547/35184372088832)), (45/8796093022208), by norm_num⟩
  | 13 => ⟨((-342766449/17592186044416), (1567192325/140737488355328)), (85/70368744177664), by norm_num⟩
  | 14 => ⟨((2385280331/562949953421312), (-1363243485/562949953421312)), (149/562949953421312), by norm_num⟩
  | 15 => ⟨((-3873087727/4503599627370496), (1106780101/2251799813685248)), (61/1125899906842624), by norm_num⟩
  | 16 => ⟨((1473962811/9007199254740992), (-842404213/9007199254740992)), (187/18014398509481984), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197569404799409/1267650600228229401496703205376), (-169084718723/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777919288667235/633825300114114700748351602688), (-799683666561/633825300114114700748351602688)), (11535/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888786410553455/39614081257132168796771975168), (-224860124235/9903520314283042199192993792)), (51911/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888502057197029/2475880078570760549798248448), (-238849921041/618970019642690137449562112)), (27579/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770168630873877/154742504910672534362390528), (-955112003963/154742504910672534362390528)), (55161/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774297795842185/4835703278458516698824704), (-895111964535/9671406556917033397649408)), (51717/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314487730820315/151115727451828646838272), (-782917566017/604462909807314587353088)), (5657/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886431329355469/75557863725914323419136), (-1271668703581/75557863725914323419136)), (73547/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296519480218777/4722366482869645213696), (-953251018303/4722366482869645213696)), (55167/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810023283212853/295147905179352825856), (-654953682123/295147905179352825856)), (75863/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455431013373033/18446744073709551616), (-409041493475/18446744073709551616)), (47421/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820689376865625/9223372036854775808), (-459753297687/2305843009213693952)), (106717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795970105465183/576460752303423488), (-918461791735/576460752303423488)), (106741/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192793434787777/144115188075855872), (-100310030813/9007199254740992)), (93427/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488961632370329/36028797018963968), (-2402753357135/36028797018963968)), (140195/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485922091453357/9007199254740992), (-2995256526775/9007199254740992)), (175341/9007199254740992), by norm_num⟩
  | 2 => ⟨((555326049327599/1125899906842624), (-2983014192713/2251799813685248)), (350975/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103102947142205/1125899906842624), (-8888078144559/2251799813685248)), (527201/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080603873873835/1125899906842624), (-1095861021357/140737488355328)), (1057393/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080603873873835/1125899906842624), (-1095861021357/140737488355328)), (4033634194380950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2074123759681859/2251799813685248), (-525886740779/35184372088832)), (1023087/1125899906842624), by norm_num⟩
  | 2 => ⟨((954982003156545/1125899906842624), (-62002196952527/2251799813685248)), (3830613/2251799813685248), by norm_num⟩
  | 3 => ⟨((809156793343171/1125899906842624), (-26294958319997/562949953421312)), (6709159/2251799813685248), by norm_num⟩
  | 4 => ⟨((289532405553495/562949953421312), (-75590180000877/1125899906842624)), (5135089/1125899906842624), by norm_num⟩
  | 5 => ⟨((1170982173980693/4503599627370496), (-155508009327403/2251799813685248)), (23886399/4503599627370496), by norm_num⟩
  | 6 => ⟨((1131955229923299/18014398509481984), (-323469441158885/9007199254740992)), (62882323/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-88110603/33554432), (-2969024049/33554432)), (1/33554432), by norm_num⟩, -14, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨47,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile047Terms2
