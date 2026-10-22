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
namespace Reinmann.XiBand97.Tile025Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (29683/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (29683/1280))
  have he : value ((69/80), (29683/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-539353095/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((175634376367911/18014398509481984), (-1639030529402331/18014398509481984)), (257641895/9007199254740992), by norm_num⟩
  | 1 => ⟨((-58050381/2147483648), (1083459273/4294967296)), (171/2147483648), by norm_num⟩
  | 2 => ⟨((20118729/536870912), (-1501993481/4294967296)), (119/1073741824), by norm_num⟩
  | 3 => ⟨((-74374615/2147483648), (1388136729/4294967296)), (221/2147483648), by norm_num⟩
  | 4 => ⟨((206210219/8589934592), (-240545765/1073741824)), (615/8589934592), by norm_num⟩
  | 5 => ⟨((-57173613/4294967296), (133386895/1073741824)), (343/8589934592), by norm_num⟩
  | 6 => ⟨((26419819/4294967296), (-986205335/17179869184)), (319/17179869184), by norm_num⟩
  | 7 => ⟨((-167431525/68719476736), (1562481023/68719476736)), (507/68719476736), by norm_num⟩
  | 8 => ⟨((116054689/137438953472), (-270757329/34359738368)), (353/137438953472), by norm_num⟩
  | 9 => ⟨((-143009743/549755813888), (1334575497/549755813888)), (437/549755813888), by norm_num⟩
  | 10 => ⟨((1239085/17179869184), (-1480091589/2199023255552)), (487/2199023255552), by norm_num⟩
  | 11 => ⟨((-159905657/8796093022208), (1492249181/8796093022208)), (493/8796093022208), by norm_num⟩
  | 12 => ⟨((147784207/35184372088832), (-1379131083/35184372088832)), (229/17592186044416), by norm_num⟩
  | 13 => ⟨((-126075331/140737488355328), (588271275/70368744177664)), (49/17592186044416), by norm_num⟩
  | 14 => ⟨((99872869/562949953421312), (-1864039203/1125899906842624)), (623/1125899906842624), by norm_num⟩
  | 15 => ⟨((-9230213/281474976710656), (1378190419/4503599627370496)), (463/4503599627370496), by norm_num⟩
  | 16 => ⟨((51183169/9007199254740992), (-1910577607/36028797018963968)), (161/9007199254740992), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-119192727333/633825300114114700748351602688)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222284776364531/79228162514264337593543950336), (-563938638771/158456325028528675187087900672)), (46211/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472297494378493/9903520314283042199192993792), (-2537194473957/39614081257132168796771975168)), (103989/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888930561735715/2475880078570760549798248448), (-2695111394759/2475880078570760549798248448)), (110505/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770596814640705/154742504910672534362390528), (-2694371714543/154742504910672534362390528)), (221047/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774498336673595/4835703278458516698824704), (-2525187823971/9671406556917033397649408)), (25909/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258301529344499/604462909807314587353088), (-2208753970841/604462909807314587353088)), (90701/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887000426455493/75557863725914323419136), (-3587753226001/75557863725914323419136)), (73713/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162118218186445/590295810358705651712), (-1344763770743/2361183241434822606848)), (55301/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620631776055325/590295810358705651712), (-3696009507623/590295810358705651712)), (304261/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911227104712691/36893488147419103232), (-577109695439/9223372036854775808)), (190243/36893488147419103232), by norm_num⟩
  | 7 => ⟨((3557634648843/18014398509481984), (-5189680769947/9223372036854775808)), (53533/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592757450503629/1152921504606846976), (-2592151229495/576460752303423488)), (428537/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193505910439869/144115188075855872), (-1132555161711/36028797018963968)), (187639/72057594037927936), by norm_num⟩
  | 4 => ⟨((745012570519815/18014398509481984), (-6783259432313/36028797018963968)), (140883/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487242398376585/9007199254740992), (-1057248264493/1125899906842624)), (352747/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223917692108697/4503599627370496), (-8426427778033/2251799813685248)), (707115/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210058749363865/2251799813685248), (-25122008120155/2251799813685248)), (1064739/1125899906842624), by norm_num⟩
  | 0 => ⟨((2168646361123083/2251799813685248), (-49618006321905/2251799813685248)), (4291631/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168646361123083/2251799813685248), (-49618006321905/2251799813685248)), (16371273049361418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1043735119013129/1125899906842624), (-2986608428795/70368744177664)), (8455435/2251799813685248), by norm_num⟩
  | 2 => ⟨((1931076671377901/2251799813685248), (-88596951396595/1125899906842624)), (8197251/1125899906842624), by norm_num⟩
  | 3 => ⟨((821045327626473/1125899906842624), (-151956230706999/1125899906842624)), (30699041/2251799813685248), by norm_num⟩
  | 4 => ⟨((1156452238800269/2251799813685248), (-221623525266267/1125899906842624)), (26530081/1125899906842624), by norm_num⟩
  | 5 => ⟨((1013335045048403/4503599627370496), (-455274967885413/2251799813685248)), (150777711/4503599627370496), by norm_num⟩
  | 6 => ⟨((175634376367911/18014398509481984), (-1639030529402331/18014398509481984)), (257641895/9007199254740992), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-539353095/8388608)), (1/8388608), by norm_num⟩, -10, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1102292867/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-753528875312089/9007199254740992), (-419802850835245/18014398509481984)), (272894507/9007199254740992), by norm_num⟩
  | 1 => ⟨((1018003495/4294967296), (283572921/4294967296)), (371/4294967296), by norm_num⟩
  | 2 => ⟨((-1442110543/4294967296), (-100427823/1073741824)), (33/268435456), by norm_num⟩
  | 3 => ⟨((1361935611/4294967296), (379377931/4294967296)), (501/4294967296), by norm_num⟩
  | 4 => ⟨((-964663537/4294967296), (-134357327/2147483648)), (357/4294967296), by norm_num⟩
  | 5 => ⟨((546619521/4294967296), (304530377/8589934592)), (407/8589934592), by norm_num⟩
  | 6 => ⟨((-516229907/8589934592), (-287599843/17179869184)), (193/8589934592), by norm_num⟩
  | 7 => ⟨((1671530813/68719476736), (232809061/34359738368)), (627/68719476736), by norm_num⟩
  | 8 => ⟨((-1183950851/137438953472), (-329798869/137438953472)), (223/68719476736), by norm_num⟩
  | 9 => ⟨((1490837933/549755813888), (103821173/137438953472)), (141/137438953472), by norm_num⟩
  | 10 => ⟨((-844772385/1099511627776), (-117659013/549755813888)), (321/1099511627776), by norm_num⟩
  | 11 => ⟨((870334689/4398046511104), (15152413/274877906944)), (83/1099511627776), by norm_num⟩
  | 12 => ⟨((-1643895903/35184372088832), (-57240025/4398046511104)), (315/17592186044416), by norm_num⟩
  | 13 => ⟨((716539663/70368744177664), (49899447/17592186044416)), (551/140737488355328), by norm_num⟩
  | 14 => ⟨((-580031353/281474976710656), (-161572319/281474976710656)), (7/8796093022208), by norm_num⟩
  | 15 => ⟨((54778419/140737488355328), (244143387/2251799813685248)), (85/562949953421312), by norm_num⟩
  | 16 => ⟨((-1241591581/18014398509481984), (-345855151/18014398509481984)), (121/4503599627370496), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-3738393448125/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222273737354775/79228162514264337593543950336), (-4421499813341/633825300114114700748351602688)), (185271/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944545108434003/19807040628566084398385987584), (-1243276660727/9903520314283042199192993792)), (104243/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944412010659897/1237940039285380274899124224), (-41270359039/19342813113834066795298816)), (221581/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442622415502179/38685626227668133590597632), (-5281121320963/154742504910672534362390528)), (110827/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387223891944673/2417851639229258349412352), (-4949474135209/9671406556917033397649408)), (207879/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314553103140607/151115727451828646838272), (-4329213127329/604462909807314587353088)), (181971/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886854395244449/75557863725914323419136), (-3516007856273/37778931862957161709568)), (36981/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648417579450139/2361183241434822606848), (-329464149233/295147905179352825856)), (111007/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620477994072415/590295810358705651712), (-7244011458373/590295810358705651712)), (76369/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455564849438903/18446744073709551616), (-9048717115559/73786976294838206464)), (382155/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455321557552717/2305843009213693952), (-5085576103957/4611686018427387904)), (26897/576460752303423488), by norm_num⟩
  | 6 => ⟨((49766572390723/36028797018963968), (-5080170098847/576460752303423488)), (215443/576460752303423488), by norm_num⟩
  | 5 => ⟨((298325551085811/36028797018963968), (-4439071328359/72057594037927936)), (94407/36028797018963968), by norm_num⟩
  | 4 => ⟨((372427421761857/9007199254740992), (-830807825623/2251799813685248)), (17739/1125899906842624), by norm_num⟩
  | 3 => ⟨((1486830838667901/9007199254740992), (-16573699038105/9007199254740992)), (711673/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111521570203655/2251799813685248), (-16510108722093/2251799813685248)), (357425/1125899906842624), by norm_num⟩
  | 1 => ⟨((276077421039591/281474976710656), (-24606523513755/1125899906842624)), (540119/562949953421312), by norm_num⟩
  | 0 => ⟨((270657940460277/281474976710656), (-759070479951/17592186044416)), (2192457/1125899906842624), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270657940460277/281474976710656), (-759070479951/17592186044416)), (8363559727195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038930244701737/1125899906842624), (-93427139639849/1125899906842624)), (1101401/281474976710656), by norm_num⟩
  | 2 => ⟨((1901851872316355/2251799813685248), (-344841599001497/2251799813685248)), (17723489/2251799813685248), by norm_num⟩
  | 3 => ⟨((1553479485419425/2251799813685248), (-582500839308831/2251799813685248)), (35366597/2251799813685248), by norm_num⟩
  | 4 => ⟨((921037150469099/2251799813685248), (-401857704493243/1125899906842624)), (67095091/2251799813685248), by norm_num⟩
  | 5 => ⟨((179723768224991/4503599627370496), (-164368907391803/562949953421312)), (205564335/4503599627370496), by norm_num⟩
  | 6 => ⟨((-753528875312089/9007199254740992), (-419802850835245/18014398509481984)), (272894507/9007199254740992), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1102292867/16777216)), (1/8388608), by norm_num⟩, -10, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-562265489/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-368014075107773/9007199254740992), (1294573235562743/18014398509481984)), (67031289/2251799813685248), by norm_num⟩
  | 1 => ⟨((63401311/536870912), (-892114143/4294967296)), (371/4294967296), by norm_num⟩
  | 2 => ⟨((-733013435/4294967296), (644635381/2147483648)), (269/2147483648), by norm_num⟩
  | 3 => ⟨((353113555/2147483648), (-1242157267/4294967296)), (521/4294967296), by norm_num⟩
  | 4 => ⟨((-510314723/4294967296), (897574071/4294967296)), (189/2147483648), by norm_num⟩
  | 5 => ⟨((589999705/8589934592), (-518864549/4294967296)), (439/8589934592), by norm_num⟩
  | 6 => ⟨((-568439495/17179869184), (499903813/8589934592)), (425/17179869184), by norm_num⟩
  | 7 => ⟨((469428989/34359738368), (-206415409/8589934592)), (353/34359738368), by norm_num⟩
  | 8 => ⟨((-339206073/68719476736), (1193234537/137438953472)), (1/268435456), by norm_num⟩
  | 9 => ⟨((217873701/137438953472), (-766420313/274877906944)), (331/274877906944), by norm_num⟩
  | 10 => ⟨((-251894397/549755813888), (886095851/1099511627776)), (3/8589934592), by norm_num⟩
  | 11 => ⟨((66188041/549755813888), (-232831493/1099511627776)), (405/4398046511104), by norm_num⟩
  | 12 => ⟨((-510154785/17592186044416), (448646381/8796093022208)), (49/2199023255552), by norm_num⟩
  | 13 => ⟨((453703687/70368744177664), (-199500743/17592186044416)), (175/35184372088832), by norm_num⟩
  | 14 => ⟨((-374677807/281474976710656), (1318014431/562949953421312)), (581/562949953421312), by norm_num⟩
  | 15 => ⟨((577577681/2251799813685248), (-507940225/1125899906842624)), (225/1125899906842624), by norm_num⟩
  | 16 => ⟨((-208676777/4503599627370496), (734068041/9007199254740992)), (327/9007199254740992), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (2719552088121/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778118882636541/633825300114114700748351602688), (201014156979/39614081257132168796771975168)), (92517/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889010615652515/39614081257132168796771975168), (1808732138303/19807040628566084398385987584)), (208203/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888739829756513/2475880078570760549798248448), (3842577603857/2475880078570760549798248448)), (221263/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885202951443863/77371252455336267181195264), (960369368331/38685626227668133590597632)), (55329/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548817502744533/9671406556917033397649408), (3600216585301/9671406556917033397649408)), (207541/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258144564430341/604462909807314587353088), (3149021351583/604462909807314587353088)), (90827/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235843125180641/9444732965739290427392), (5114970214061/75557863725914323419136)), (147647/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296753864755917/4722366482869645213696), (239644542635/295147905179352825856)), (55391/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405091858466123/147573952589676412928), (5269069632565/590295810358705651712)), (9525/18446744073709551616), by norm_num⟩
  | 8 => ⟨((227765377973717/9223372036854775808), (3290837133565/36893488147419103232)), (190613/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455283829121433/2305843009213693952), (3698988298869/4611686018427387904)), (214595/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199047816283141/144115188075855872), (3694987222747/576460752303423488)), (107395/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193176401229159/144115188075855872), (3228617102535/72057594037927936)), (735/281474976710656), by norm_num⟩
  | 4 => ⟨((186190997580699/4503599627370496), (2416971722951/9007199254740992)), (282679/18014398509481984), by norm_num⟩
  | 3 => ⟨((743307952260607/4503599627370496), (12053471372963/9007199254740992)), (354117/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222649676604289/4503599627370496), (24012982789195/4503599627370496)), (1421091/4503599627370496), by norm_num⟩
  | 1 => ⟨((69003734790897/70368744177664), (17892639846997/1125899906842624)), (2143225/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164621167187961/2251799813685248), (70638007519315/2251799813685248)), (2166499/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164621167187961/2251799813685248), (70638007519315/2251799813685248)), (8264537815574264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039300882983845/1125899906842624), (67903250260089/1125899906842624)), (8602341/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910534795213287/2251799813685248), (31340222840363/281474976710656)), (4229749/562949953421312), by norm_num⟩
  | 3 => ⟨((1593073136247425/2251799813685248), (106362183462941/562949953421312)), (2029837/140737488355328), by norm_num⟩
  | 4 => ⟨((261665732670073/562949953421312), (300990765089593/1125899906842624)), (58225715/2251799813685248), by norm_num⟩
  | 5 => ⟨((651142719994787/4503599627370496), (2186000521545/8796093022208)), (85259359/2251799813685248), by norm_num⟩
  | 6 => ⟨((-368014075107773/9007199254740992), (1294573235562743/18014398509481984)), (67031289/2251799813685248), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-562265489/8388608)), (1/8388608), by norm_num⟩, -11, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-1145566425/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((477530728783045/9007199254740992), (1052632562393055/18014398509481984)), (335069719/18014398509481984), by norm_num⟩
  | 1 => ⟨((-335230849/2147483648), (-46184843/268435456)), (237/4294967296), by norm_num⟩
  | 2 => ⟨((987066779/4294967296), (33997113/134217728)), (351/4294967296), by norm_num⟩
  | 3 => ⟨((-484392983/2147483648), (-1067759197/4294967296)), (347/4294967296), by norm_num⟩
  | 4 => ⟨((356566395/2147483648), (392993975/2147483648)), (257/4294967296), by norm_num⟩
  | 5 => ⟨((-419955197/4294967296), (-925717423/8589934592)), (305/8589934592), by norm_num⟩
  | 6 => ⟨((103044371/2147483648), (908572821/17179869184)), (151/8589934592), by norm_num⟩
  | 7 => ⟨((-346751843/17179869184), (-382176747/17179869184)), (1/134217728), by norm_num⟩
  | 8 => ⟨((1020989643/137438953472), (1125296111/137438953472)), (379/137438953472), by norm_num⟩
  | 9 => ⟨((-41753357/17179869184), (-92037937/34359738368)), (125/137438953472), by norm_num⟩
  | 10 => ⟨((196704339/274877906944), (433600143/549755813888)), (297/1099511627776), by norm_num⟩
  | 11 => ⟨((-842449343/4398046511104), (-464257877/2199023255552)), (5/68719476736), by norm_num⟩
  | 12 => ⟨((413423447/8796093022208), (455659663/8796093022208)), (79/4398046511104), by norm_num⟩
  | 13 => ⟨((-749107761/70368744177664), (-825638199/70368744177664)), (9/2199023255552), by norm_num⟩
  | 14 => ⟨((630200597/281474976710656), (694583227/281474976710656)), (61/70368744177664), by norm_num⟩
  | 15 => ⟨((-247411627/562949953421312), (-1090750895/2251799813685248)), (385/2251799813685248), by norm_num⟩
  | 16 => ⟨((364244219/4503599627370496), (802912363/9007199254740992)), (285/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1086324123639/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778051706943237/633825300114114700748351602688), (1284621604799/633825300114114700748351602688)), (184653/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888935317892207/39614081257132168796771975168), (1444881861533/39614081257132168796771975168)), (207751/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944330094835893/1237940039285380274899124224), (1534789421993/2475880078570760549798248448)), (220755/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770326671651283/154742504910672534362390528), (767171189097/77371252455336267181195264)), (27597/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387185914385143/2417851639229258349412352), (718985586641/4835703278458516698824704)), (25875/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258080383595673/604462909807314587353088), (628875085199/302231454903657293676544)), (45287/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117915095002753/4722366482869645213696), (1021477282565/37778931862957161709568)), (294407/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296676963836531/4722366482869645213696), (382859517369/1180591620717411303424)), (220843/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620262847627117/590295810358705651712), (2104464127953/590295810358705651712)), (303719/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821994017271213/73786976294838206464), (2628686725215/73786976294838206464)), (379739/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820992553707441/9223372036854775808), (1477335676353/4611686018427387904)), (427331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592242723322291/1152921504606846976), (1475711611225/576460752303423488)), (427487/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193057387082819/144115188075855872), (2578845823949/144115188075855872)), (374227/144115188075855872), by norm_num⟩
  | 4 => ⟨((372339018088987/9007199254740992), (1930490678067/18014398509481984)), (280847/18014398509481984), by norm_num⟩
  | 3 => ⟨((743206272402307/4503599627370496), (300843741503/562949953421312)), (702737/9007199254740992), by norm_num⟩
  | 2 => ⟨((69446167084493/140737488355328), (9588923356191/4503599627370496)), (703667/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207646338728167/2251799813685248), (446517424211/70368744177664)), (66115/70368744177664), by norm_num⟩
  | 0 => ⟨((2164012196503193/2251799813685248), (7049994628129/562949953421312)), (2125099/1125899906842624), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2164012196503193/2251799813685248), (7049994628129/562949953421312)), (8106609348777389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079293869450923/2251799813685248), (54201174608271/2251799813685248)), (4137729/1125899906842624), by norm_num⟩
  | 2 => ⟨((1918698634731831/2251799813685248), (100097858961605/2251799813685248)), (15681367/2251799813685248), by norm_num⟩
  | 3 => ⟨((1630422405775309/2251799813685248), (170581438156257/2251799813685248)), (28117499/2251799813685248), by norm_num⟩
  | 4 => ⟨((1167590110911249/2251799813685248), (61755000841787/562949953421312)), (44977111/2251799813685248), by norm_num⟩
  | 5 => ⟨((1156628379769697/4503599627370496), (256166743931581/2251799813685248)), (56510421/2251799813685248), by norm_num⟩
  | 6 => ⟨((477530728783045/9007199254740992), (1052632562393055/18014398509481984)), (335069719/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-1145566425/16777216)), (1/8388608), by norm_num⟩, -11, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-1165522647/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1274782044380089/18014398509481984), (-236664793487579/9007199254740992)), (28976975/4503599627370496), by norm_num⟩
  | 1 => ⟨((-455249037/2147483648), (338070087/4294967296)), (85/4294967296), by norm_num⟩
  | 2 => ⟨((1363804233/4294967296), (-506383735/4294967296)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((-1361864119/4294967296), (252831683/2147483648)), (131/4294967296), by norm_num⟩
  | 4 => ⟨((1019945073/4294967296), (-23669251/268435456)), (25/1073741824), by norm_num⟩
  | 5 => ⟨((-1222192949/8589934592), (226901565/4294967296)), (61/4294967296), by norm_num⟩
  | 6 => ⟨((1220454287/17179869184), (-453157561/17179869184)), (31/4294967296), by norm_num⟩
  | 7 => ⟨((-1044615513/34359738368), (387868209/34359738368)), (27/8589934592), by norm_num⟩
  | 8 => ⟨((1564694203/137438953472), (-9077729/2147483648)), (41/34359738368), by norm_num⟩
  | 9 => ⟨((-520822769/137438953472), (386765451/274877906944)), (111/274877906944), by norm_num⟩
  | 10 => ⟨((624098231/549755813888), (-231729149/549755813888)), (135/1099511627776), by norm_num⟩
  | 11 => ⟨((-1359731791/4398046511104), (504871629/4398046511104)), (149/4398046511104), by norm_num⟩
  | 12 => ⟨((678898735/8796093022208), (-504153411/17592186044416)), (151/17592186044416), by norm_num⟩
  | 13 => ⟨((-312892131/17592186044416), (29044397/4398046511104)), (141/70368744177664), by norm_num⟩
  | 14 => ⟨((133905865/35184372088832), (-198878257/140737488355328)), (61/140737488355328), by norm_num⟩
  | 15 => ⟨((-106972299/140737488355328), (79438135/281474976710656)), (99/1125899906842624), by norm_num⟩
  | 16 => ⟨((640920737/4503599627370496), (-237975385/4503599627370496)), (75/4503599627370496), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (-463110972075/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222248035720675/79228162514264337593543950336), (-273803589893/316912650057057350374175801344)), (92255/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944429762943033/19807040628566084398385987584), (-153980199595/9903520314283042199192993792)), (51895/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888579735017535/2475880078570760549798248448), (-654243461205/2475880078570760549798248448)), (110281/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770246300565155/154742504910672534362390528), (-81756202735/19342813113834066795298816)), (55143/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387167099594857/2417851639229258349412352), (-306482823509/4835703278458516698824704)), (103397/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258014620495299/604462909807314587353088), (-268069579289/302231454903657293676544)), (45239/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886534821112839/75557863725914323419136), (-870840483513/75557863725914323419136)), (147035/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296597084840619/4722366482869645213696), (-163198278155/1180591620717411303424)), (27571/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101259578106099/36893488147419103232), (-897042860243/590295810358705651712)), (75827/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821857372932185/73786976294838206464), (-1120482703323/73786976294838206464)), (94793/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820839313551607/9223372036854775808), (-314853842267/2305843009213693952)), (3333/144115188075855872), by norm_num⟩
  | 6 => ⟨((1592090087950533/1152921504606846976), (-629003658745/576460752303423488)), (106673/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192924509973215/144115188075855872), (-549587228925/72057594037927936)), (46679/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489158110527111/36028797018963968), (-411400767977/9007199254740992)), (140075/18014398509481984), by norm_num⟩
  | 3 => ⟨((371541863274727/2251799813685248), (-512872027931/2251799813685248)), (175161/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110897105305627/2251799813685248), (-2043238162831/2251799813685248)), (701051/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206939132882533/2251799813685248), (-6088629777243/2251799813685248)), (526303/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162667061734293/2251799813685248), (-12013907157263/2251799813685248)), (2109387/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162667061734293/2251799813685248), (-12013907157263/2251799813685248)), (8046672829634856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1038499172422215/1125899906842624), (-1442295243889/140737488355328)), (1018573/562949953421312), by norm_num⟩
  | 2 => ⟨((119720610905495/140737488355328), (-1330333547471/70368744177664)), (7599539/2251799813685248), by norm_num⟩
  | 3 => ⟨((814335722122611/1125899906842624), (-72426857973961/2251799813685248)), (13216683/2251799813685248), by norm_num⟩
  | 4 => ⟨((1175648477921881/2251799813685248), (-52384565742345/1125899906842624)), (19968807/2251799813685248), by norm_num⟩
  | 5 => ⟨((38057689575543/140737488355328), (-218796838359433/4503599627370496)), (45418625/4503599627370496), by norm_num⟩
  | 6 => ⟨((1274782044380089/18014398509481984), (-236664793487579/9007199254740992)), (28976975/4503599627370496), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-1165522647/16777216)), (1/16777216), by norm_num⟩, -11, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-592252499/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((54587408796635/9007199254740992), (-649602439552369/9007199254740992)), (412183895/18014398509481984), by norm_num⟩
  | 1 => ⟨((-79246803/4294967296), (943054773/4294967296)), (601/8589934592), by norm_num⟩
  | 2 => ⟨((120634335/4294967296), (-358893927/1073741824)), (459/4294967296), by norm_num⟩
  | 3 => ⟨((-122424647/4294967296), (728440409/2147483648)), (117/1073741824), by norm_num⟩
  | 4 => ⟨((46590573/2147483648), (-1108876585/4294967296)), (179/2147483648), by norm_num⟩
  | 5 => ⟨((-28369209/2147483648), (675199929/4294967296)), (219/4294967296), by norm_num⟩
  | 6 => ⟨((28790231/4294967296), (-1370440889/17179869184)), (447/17179869184), by norm_num⟩
  | 7 => ⟨((-100174291/34359738368), (596048291/17179869184)), (391/34359738368), by norm_num⟩
  | 8 => ⟨((76245719/68719476736), (-453670599/34359738368)), (597/137438953472), by norm_num⟩
  | 9 => ⟨((-51584845/137438953472), (1227742505/274877906944)), (405/274877906944), by norm_num⟩
  | 10 => ⟨((62820487/549755813888), (-747577921/549755813888)), (495/1099511627776), by norm_num⟩
  | 11 => ⟨((-139097005/4398046511104), (206910705/549755813888)), (275/2199023255552), by norm_num⟩
  | 12 => ⟨((70580659/8796093022208), (-52495357/549755813888)), (35/1099511627776), by norm_num⟩
  | 13 => ⟨((-66118277/35184372088832), (393411181/17592186044416)), (263/35184372088832), by norm_num⟩
  | 14 => ⟨((115027759/281474976710656), (-10694189/2199023255552)), (459/281474976710656), by norm_num⟩
  | 15 => ⟨((-23346973/281474976710656), (138917113/140737488355328)), (375/1125899906842624), by norm_num⟩
  | 16 => ⟨((71080383/4503599627370496), (-845872535/4503599627370496)), (573/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-1936933063177/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111119801182303/39614081257132168796771975168), (-143135877523/39614081257132168796771975168)), (184851/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888783496727357/39614081257132168796771975168), (-2575859049251/39614081257132168796771975168)), (207987/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236062347530223/309485009821345068724781056), (-684029282491/618970019642690137449562112)), (55255/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770165150511391/154742504910672534362390528), (-341911591419/19342813113834066795298816)), (221057/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774296056449093/4835703278458516698824704), (-640865331629/2417851639229258349412352)), (103641/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314486915898191/151115727451828646838272), (-1121076702649/302231454903657293676544)), (45353/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235803203530625/9444732965739290427392), (-3641858931079/75557863725914323419136)), (294869/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296514851199179/4722366482869645213696), (-2729959640853/4722366482869645213696)), (110609/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101252476773331/36893488147419103232), (-234460297357/36893488147419103232)), (152141/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910857261280461/36893488147419103232), (-2342856892971/36893488147419103232)), (190257/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910338738261181/4611686018427387904), (-5266630284719/9223372036854775808)), (107075/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591926841335899/1152921504606846976), (-2630319560051/576460752303423488)), (428577/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192780088022595/144115188075855872), (-574540924959/18014398509481984)), (187659/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488938326802567/36028797018963968), (-6881047989721/36028797018963968)), (563603/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485887235413223/9007199254740992), (-4288915360307/4503599627370496)), (705601/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221217414279799/4503599627370496), (-4271352005743/1125899906842624)), (707251/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206033395412499/2251799813685248), (-12726561190443/1125899906842624)), (1065017/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160695559289035/2251799813685248), (-50210137977061/2251799813685248)), (536669/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160695559289035/2251799813685248), (-50210137977061/2251799813685248)), (2047229767919444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((259019708014101/281474976710656), (-96357430619709/2251799813685248)), (8430765/2251799813685248), by norm_num⟩
  | 2 => ⟨((1902723592242335/2251799813685248), (-44335155181063/562949953421312)), (16237893/2251799813685248), by norm_num⟩
  | 3 => ⟨((1593795039374829/2251799813685248), (-149849103310255/1125899906842624)), (29998991/2251799813685248), by norm_num⟩
  | 4 => ⟨((1088180040513481/2251799813685248), (-106061274212377/562949953421312)), (12612775/562949953421312), by norm_num⟩
  | 5 => ⟨((222966511558525/1125899906842624), (-820064099608941/4503599627370496)), (33885567/1125899906842624), by norm_num⟩
  | 6 => ⟨((54587408796635/9007199254740992), (-649602439552369/9007199254740992)), (412183895/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-592252499/8388608)), (1/8388608), by norm_num⟩, -11, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile025Terms2
