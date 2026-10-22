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
namespace Reinmann.XiBand97.Tile033Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32189/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32189/1280))
  have he : value ((69/80), (32189/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/8388608), (-584888211/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((675998557795647/9007199254740992), (-235766344861249/4503599627370496)), (5267705/281474976710656), by norm_num⟩
  | 1 => ⟨((-893719663/4294967296), (77925099/536870912)), (225/4294967296), by norm_num⟩
  | 2 => ⟨((1238958529/4294967296), (-864217003/4294967296)), (157/2147483648), by norm_num⟩
  | 3 => ⟨((-1145040815/4294967296), (798706105/4294967296)), (73/1073741824), by norm_num⟩
  | 4 => ⟨((793681813/4294967296), (-553620885/4294967296)), (51/1073741824), by norm_num⟩
  | 5 => ⟨((-440110649/4294967296), (613985209/8589934592)), (57/2147483648), by norm_num⟩
  | 6 => ⟨((813497215/17179869184), (-283721411/8589934592)), (213/17179869184), by norm_num⟩
  | 7 => ⟨((-322213315/17179869184), (449510163/34359738368)), (171/34359738368), by norm_num⟩
  | 8 => ⟨((893365003/137438953472), (-155788351/34359738368)), (239/137438953472), by norm_num⟩
  | 9 => ⟨((-1100859437/549755813888), (767888045/549755813888)), (297/549755813888), by norm_num⟩
  | 10 => ⟨((152611523/274877906944), (-851615093/2199023255552)), (83/549755813888), by norm_num⟩
  | 11 => ⟨((-1230920691/8796093022208), (107326291/1099511627776)), (337/8796093022208), by norm_num⟩
  | 12 => ⟨((1137612275/35184372088832), (-793524437/35184372088832)), (157/17592186044416), by norm_num⟩
  | 13 => ⟨((-970501835/140737488355328), (84619881/17592186044416)), (135/70368744177664), by norm_num⟩
  | 14 => ⟨((384400349/281474976710656), (-536265435/562949953421312)), (215/562949953421312), by norm_num⟩
  | 15 => ⟨((-142104543/562949953421312), (792983199/4503599627370496)), (5/70368744177664), by norm_num⟩
  | 16 => ⟨((787994907/18014398509481984), (-549654069/18014398509481984)), (7/562949953421312), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197607594575137/1267650600228229401496703205376), (-793381314541/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222285058204621/79228162514264337593543950336), (-58652170491/39614081257132168796771975168)), (184585/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889192639198409/39614081257132168796771975168), (-1055520169737/39614081257132168796771975168)), (103835/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944466777605901/1237940039285380274899124224), (-140152088285/309485009821345068724781056)), (220663/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442649998511245/38685626227668133590597632), (-560454591355/77371252455336267181195264)), (220679/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774499925721317/4835703278458516698824704), (-525262865925/4835703278458516698824704)), (206903/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258304507418973/604462909807314587353088), (-918883519929/604462909807314587353088)), (181057/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887005635307227/75557863725914323419136), (-373143455061/18889465931478580854784)), (36781/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296949975080163/4722366482869645213696), (-559447616081/2361183241434822606848)), (220713/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620638115885229/590295810358705651712), (-1537611876183/590295810358705651712)), (303525/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911231459649251/36893488147419103232), (-1920712158009/73786976294838206464)), (23717/4611686018427387904), by norm_num⟩
  | 7 => ⟨((113844988529335/576460752303423488), (-269876433535/1152921504606846976)), (426997/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592769671079539/1152921504606846976), (-539194139391/288230376151711744)), (53389/144115188075855872), by norm_num⟩
  | 5 => ⟨((596759056008265/72057594037927936), (-1884668270941/144115188075855872)), (93463/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490046451116235/36028797018963968), (-2821987606709/36028797018963968)), (561035/36028797018963968), by norm_num⟩
  | 3 => ⟨((743637139145275/4503599627370496), (-1759362879267/4503599627370496)), (175437/2251799813685248), by norm_num⟩
  | 2 => ⟨((69499909200867/140737488355328), (-7011243730123/4503599627370496)), (1404859/4503599627370496), by norm_num⟩
  | 1 => ⟨((276277083068455/281474976710656), (-2612896284151/562949953421312)), (2110721/2251799813685248), by norm_num⟩
  | 0 => ⟨((271139459993477/281474976710656), (-10321738810289/1125899906842624)), (529409/281474976710656), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((271139459993477/281474976710656), (-10321738810289/1125899906842624)), (2019535065771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2089278385776085/2251799813685248), (-39770934097525/2251799813685248)), (514823/140737488355328), by norm_num⟩
  | 2 => ⟨((1937784353454989/2251799813685248), (-36900506202679/1125899906842624)), (15576285/2251799813685248), by norm_num⟩
  | 3 => ⟨((1665139853141057/2251799813685248), (-127018792913205/2251799813685248)), (27829319/2251799813685248), by norm_num⟩
  | 4 => ⟨((1224157200836681/2251799813685248), (-93926668299837/1125899906842624)), (44297505/2251799813685248), by norm_num⟩
  | 5 => ⟨((324911647872887/1125899906842624), (-408494597614051/4503599627370496)), (13888567/562949953421312), by norm_num⟩
  | 6 => ⟨((675998557795647/9007199254740992), (-235766344861249/4503599627370496)), (5267705/281474976710656), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/8388608), (-584888211/8388608)), (1/8388608), by norm_num⟩, -11, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-40997585/16777216), (-1195354415/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-834768149599391/18014398509481984), (-1323109834329767/18014398509481984)), (565615217/18014398509481984), by norm_num⟩
  | 1 => ⟨((281939061/2147483648), (223437097/1073741824)), (3/33554432), by norm_num⟩
  | 2 => ⟨((-399396755/2147483648), (-633044965/2147483648)), (273/2147483648), by norm_num⟩
  | 3 => ⟨((47149009/268435456), (597850481/2147483648)), (259/2147483648), by norm_num⟩
  | 4 => ⟨((-267166403/2147483648), (-211729745/1073741824)), (369/4294967296), by norm_num⟩
  | 5 => ⟨((302775767/4294967296), (479900431/4294967296)), (105/2147483648), by norm_num⟩
  | 6 => ⟨((-285942781/8589934592), (-906440203/17179869184)), (399/17179869184), by norm_num⟩
  | 7 => ⟨((462935373/34359738368), (733753851/34359738368)), (81/8589934592), by norm_num⟩
  | 8 => ⟨((-327898669/68719476736), (-1039440601/137438953472)), (461/137438953472), by norm_num⟩
  | 9 => ⟨((825783897/549755813888), (1308869769/549755813888)), (583/549755813888), by norm_num⟩
  | 10 => ⟨((-467924391/1099511627776), (-741661459/1099511627776)), (83/274877906944), by norm_num⟩
  | 11 => ⟨((482083501/4398046511104), (95512961/549755813888)), (43/549755813888), by norm_num⟩
  | 12 => ⟨((-455281803/17592186044416), (-360811461/8796093022208)), (327/17592186044416), by norm_num⟩
  | 13 => ⟨((99223883/17592186044416), (1258161041/140737488355328)), (573/140737488355328), by norm_num⟩
  | 14 => ⟨((-642565553/562949953421312), (-509234093/281474976710656)), (233/281474976710656), by norm_num⟩
  | 15 => ⟨((485473413/2251799813685248), (192369177/562949953421312)), (177/1125899906842624), by norm_num⟩
  | 16 => ⟨((-171931219/4503599627370496), (-1090045839/18014398509481984)), (63/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792644716861/10141204801825835211973625643008), (-2779300294201/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222274323155411/79228162514264337593543950336), (-1643577101039/316912650057057350374175801344)), (185047/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889095748423509/39614081257132168796771975168), (-924313709347/9903520314283042199192993792)), (52055/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888830242325797/2475880078570760549798248448), (-15341223249/9671406556917033397649408)), (110641/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((55328008417201/4835703278458516698824704), (-3926250834803/154742504910672534362390528)), (27667/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193612771541795/1208925819614629174706176), (-3679689273755/9671406556917033397649408)), (25945/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314554650343537/151115727451828646838272), (-804639399823/151115727451828646838272)), (181673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886865219748677/75557863725914323419136), (-5227962165983/75557863725914323419136)), (147663/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296843948265733/4722366482869645213696), (-1959526358149/2361183241434822606848)), (110795/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101280698026423/36893488147419103232), (-5385580727057/590295810358705651712)), (38105/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822277496736951/73786976294838206464), (-1681825835087/18446744073709551616)), (11915/2305843009213693952), by norm_num⟩
  | 7 => ⟨((910654415163477/4611686018427387904), (-7561795648599/9223372036854775808)), (214629/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592555709193563/1152921504606846976), (-944222017939/144115188075855872)), (53707/144115188075855872), by norm_num⟩
  | 5 => ⟨((74582972282503/9007199254740992), (-6600540781817/144115188075855872)), (376397/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489753962301811/36028797018963968), (-4941402987035/18014398509481984)), (565491/36028797018963968), by norm_num⟩
  | 3 => ⟨((46465533427845/281474976710656), (-6161023346415/4503599627370496)), (708435/9007199254740992), by norm_num⟩
  | 2 => ⟨((138950505162067/281474976710656), (-24549904217395/4503599627370496)), (1421591/4503599627370496), by norm_num⟩
  | 1 => ⟨((552236837775677/562949953421312), (-9147514709849/562949953421312)), (2144225/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083118997917759/1125899906842624), (-72244975418979/2251799813685248)), (4335995/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1083118997917759/1125899906842624), (-72244975418979/2251799813685248)), (16540508278853606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((130100589138765/140737488355328), (-34749938651223/562949953421312)), (4310353/1125899906842624), by norm_num⟩
  | 2 => ⟨((1915701762355553/2251799813685248), (-16061774101175/140737488355328)), (17002595/2251799813685248), by norm_num⟩
  | 3 => ⟨((100027492176669/140737488355328), (-109315468507197/562949953421312)), (32810529/2251799813685248), by norm_num⟩
  | 4 => ⟨((1052584617891549/2251799813685248), (-621557329105403/2251799813685248)), (29690949/1125899906842624), by norm_num⟩
  | 5 => ⟨((320455157723945/2251799813685248), (-145270836194667/562949953421312)), (176594257/4503599627370496), by norm_num⟩
  | 6 => ⟨((-834768149599391/18014398509481984), (-1323109834329767/18014398509481984)), (565615217/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40997585/16777216), (-1195354415/16777216)), (1/8388608), by norm_num⟩, -11, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2614043/1048576), (-1219469987/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1353958416524977/18014398509481984), (38752716964541/1125899906842624)), (267038179/9007199254740992), by norm_num⟩
  | 1 => ⟨((116629695/536870912), (-53410415/536870912)), (185/2147483648), by norm_num⟩
  | 2 => ⟨((-1348412707/4294967296), (617503821/4294967296)), (537/4294967296), by norm_num⟩
  | 3 => ⟨((649569001/2147483648), (-594938535/4294967296)), (519/4294967296), by norm_num⟩
  | 4 => ⟨((-234686987/1073741824), (429898385/4294967296)), (377/4294967296), by norm_num⟩
  | 5 => ⟨((1085332223/8589934592), (-124256615/2147483648)), (219/4294967296), by norm_num⟩
  | 6 => ⟨((-522835601/8589934592), (119715937/4294967296)), (53/2147483648), by norm_num⟩
  | 7 => ⟨((863536717/34359738368), (-395455501/34359738368)), (11/1073741824), by norm_num⟩
  | 8 => ⟨((-623985535/68719476736), (285753353/68719476736)), (511/137438953472), by norm_num⟩
  | 9 => ⟨((200394463/68719476736), (-367081521/274877906944)), (165/137438953472), by norm_num⟩
  | 10 => ⟨((-463371597/549755813888), (424400825/1099511627776)), (3/8589934592), by norm_num⟩
  | 11 => ⟨((974048129/4398046511104), (-223032029/2199023255552)), (405/4398046511104), by norm_num⟩
  | 12 => ⟨((-469226867/8796093022208), (107440913/4398046511104)), (49/2199023255552), by norm_num⟩
  | 13 => ⟨((834609283/70368744177664), (-191104111/35184372088832)), (175/35184372088832), by norm_num⟩
  | 14 => ⟨((-1378474915/562949953421312), (157817693/140737488355328)), (145/140737488355328), by norm_num⟩
  | 15 => ⟨((265620331/562949953421312), (-486561923/2251799813685248)), (449/2251799813685248), by norm_num⟩
  | 16 => ⟨((-767741503/9007199254740992), (175793105/4503599627370496)), (163/4503599627370496), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98795526689373/633825300114114700748351602688), (3532875969473/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889057535123309/316912650057057350374175801344), (4178088518721/633825300114114700748351602688)), (92611/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472251529070867/9903520314283042199192993792), (4699312511273/39614081257132168796771975168)), (208429/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944367384806801/1237940039285380274899124224), (2495873823283/1237940039285380274899124224)), (221517/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770400528540839/154742504910672534362390528), (2495158512095/77371252455336267181195264)), (110793/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774406065354357/4835703278458516698824704), (4676902528183/9671406556917033397649408)), (103905/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629069765300705/302231454903657293676544), (4090770428131/604462909807314587353088)), (181907/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117921012321991/4722366482869645213696), (6644654133963/75557863725914323419136)), (36967/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296746715866221/4722366482869645213696), (4980999611133/4722366482869645213696)), (221923/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620356718573357/590295810358705651712), (6844828194063/590295810358705651712)), (305339/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227763537915905/9223372036854775808), (133593259571/1152921504606846976)), (381967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910558467744159/4611686018427387904), (9610377586247/9223372036854775808)), (430117/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592361878544547/1152921504606846976), (2399990744923/288230376151711744)), (430623/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18643059110977/2251799813685248), (2097065122355/36028797018963968)), (94341/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489491974419811/36028797018963968), (784937487121/2251799813685248)), (283593/18014398509481984), by norm_num⟩
  | 3 => ⟨((743281022973909/4503599627370496), (7828934018175/4503599627370496)), (177745/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111257778415415/2251799813685248), (7798325208243/1125899906842624)), (356991/1125899906842624), by norm_num⟩
  | 1 => ⟨((1103926424834665/1125899906842624), (11621149565869/562949953421312)), (269625/281474976710656), by norm_num⟩
  | 0 => ⟨((1081914513655323/1125899906842624), (45876099747939/1125899906842624)), (1093615/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1081914513655323/1125899906842624), (45876099747939/1125899906842624)), (4171810152293968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1037778217431963/1125899906842624), (88167727602685/1125899906842624)), (4381807/1125899906842624), by norm_num⟩
  | 2 => ⟨((949649319524363/1125899906842624), (162534070089999/1125899906842624)), (8763973/1125899906842624), by norm_num⟩
  | 3 => ⟨((1555052097993341/2251799813685248), (274181333744559/1125899906842624)), (34628817/2251799813685248), by norm_num⟩
  | 4 => ⟨((940352423651851/2251799813685248), (378689309483783/1125899906842624)), (64693821/2251799813685248), by norm_num⟩
  | 5 => ⟨((275904018031075/4503599627370496), (1265126350290733/4503599627370496)), (195102087/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1353958416524977/18014398509481984), (38752716964541/1125899906842624)), (267038179/9007199254740992), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2614043/1048576), (-1219469987/16777216)), (1/8388608), by norm_num⟩, -12, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-42607059/16777216), (-621140681/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((307834302619763/18014398509481984), (1387593507216395/18014398509481984)), (214024995/18014398509481984), by norm_num⟩
  | 1 => ⟨((-108051219/2147483648), (-30440721/134217728)), (19/536870912), by norm_num⟩
  | 2 => ⟨((318150221/4294967296), (1434093527/4294967296)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((-312257971/4294967296), (-1407533627/4294967296)), (7/134217728), by norm_num⟩
  | 4 => ⟨((229856135/4294967296), (1036099219/4294967296)), (167/4294967296), by norm_num⟩
  | 5 => ⟨((-270718945/8589934592), (-1220292371/8589934592)), (199/8589934592), by norm_num⟩
  | 6 => ⟨((132852569/8589934592), (1197692141/17179869184)), (197/17179869184), by norm_num⟩
  | 7 => ⟨((-27941163/4294967296), (-1007580407/34359738368)), (167/34359738368), by norm_num⟩
  | 8 => ⟨((164542099/68719476736), (185422439/17179869184)), (31/17179869184), by norm_num⟩
  | 9 => ⟨((-107663149/137438953472), (-485302273/137438953472)), (41/68719476736), by norm_num⟩
  | 10 => ⟨((126803029/549755813888), (1143154343/1099511627776)), (195/1099511627776), by norm_num⟩
  | 11 => ⟨((-271537295/4398046511104), (-611990583/2199023255552)), (211/4398046511104), by norm_num⟩
  | 12 => ⟨((66627083/4398046511104), (600656309/8796093022208)), (209/17592186044416), by norm_num⟩
  | 13 => ⟨((-241451545/70368744177664), (-272091669/17592186044416)), (191/70368744177664), by norm_num⟩
  | 14 => ⟨((101562763/140737488355328), (915608361/281474976710656)), (81/140737488355328), by norm_num⟩
  | 15 => ⟨((-318981715/2251799813685248), (-359460393/562949953421312)), (257/2251799813685248), by norm_num⟩
  | 16 => ⟨((234805549/9007199254740992), (1058409193/9007199254740992)), (191/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841205905/5070602400912917605986812821504), (1761761927623/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778050264749663/633825300114114700748351602688), (2083353748195/633825300114114700748351602688)), (46203/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888933616017505/39614081257132168796771975168), (1171628121345/19807040628566084398385987584)), (51985/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118041142230227/154742504910672534362390528), (1244532398309/1237940039285380274899124224)), (110483/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770324638829207/154742504910672534362390528), (1244169758763/77371252455336267181195264)), (27625/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548741625607071/9671406556917033397649408), (2332047959795/9671406556917033397649408)), (25903/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258078479601669/604462909807314587353088), (2039771932011/604462909807314587353088)), (90679/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886638189940821/75557863725914323419136), (103537069563/2361183241434822606848)), (147387/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296674259894953/4722366482869645213696), (2483627549167/4722366482869645213696)), (110571/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405064698701333/147573952589676412928), (853234537095/147573952589676412928)), (152083/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910994224829681/36893488147419103232), (4263100210831/73786976294838206464)), (190177/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820985601712631/9223372036854775808), (4791766531949/9223372036854775808)), (107025/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592234912656521/1152921504606846976), (4786495192337/1152921504606846976)), (214177/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149131198663767/18014398509481984), (4182260134001/144115188075855872)), (187547/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489342455215411/36028797018963968), (6261561606559/36028797018963968)), (70401/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486392176897833/9007199254740992), (3903145895767/4503599627370496)), (352505/9007199254740992), by norm_num⟩
  | 2 => ⟨((277778328589391/562949953421312), (1943845243659/562949953421312)), (353255/2251799813685248), by norm_num⟩
  | 1 => ⟨((551886376486931/562949953421312), (11586072072865/1125899906842624)), (531765/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163712699225417/2251799813685248), (45731615030981/2251799813685248)), (535549/562949953421312), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163712699225417/2251799813685248), (45731615030981/2251799813685248)), (2042957308055686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2078142664252879/2251799813685248), (87885322307299/2251799813685248)), (4203805/2251799813685248), by norm_num⟩
  | 2 => ⟨((957223878630619/1125899906842624), (162215341469019/2251799813685248)), (4043681/1125899906842624), by norm_num⟩
  | 3 => ⟨((807975108657527/1125899906842624), (137913146089343/1125899906842624)), (14916715/2251799813685248), by norm_num⟩
  | 4 => ⟨((281465402250217/562949953421312), (395880267933671/2251799813685248)), (6265897/562949953421312), by norm_num⟩
  | 5 => ⟨((986626936667879/4503599627370496), (197933400970517/1125899906842624)), (67750805/4503599627370496), by norm_num⟩
  | 6 => ⟨((307834302619763/18014398509481984), (1387593507216395/18014398509481984)), (214024995/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42607059/16777216), (-621140681/8388608)), (1/16777216), by norm_num⟩, -12, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-43349291/16777216), (-315980599/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((678579107705619/9007199254740992), (21259904929295/4503599627370496)), (44874917/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1938668569/8589934592), (-121477095/8589934592)), (65/4294967296), by norm_num⟩
  | 2 => ⟨((181491625/536870912), (45489107/2147483648)), (99/4294967296), by norm_num⟩
  | 3 => ⟨((-362466879/1073741824), (-90848791/4294967296)), (101/4294967296), by norm_num⟩
  | 4 => ⟨((33932929/134217728), (4252479/268435456)), (77/4294967296), by norm_num⟩
  | 5 => ⟨((-1301170823/8589934592), (-81531447/8589934592)), (47/4294967296), by norm_num⟩
  | 6 => ⟨((1299319809/17179869184), (40707731/8589934592)), (3/536870912), by norm_num⟩
  | 7 => ⟨((-1112118367/34359738368), (-2177669/1073741824)), (21/8589934592), by norm_num⟩
  | 8 => ⟨((832902221/68719476736), (104379413/137438953472)), (1/1073741824), by norm_num⟩
  | 9 => ⟨((-1108956473/274877906944), (-17371821/68719476736)), (87/274877906944), by norm_num⟩
  | 10 => ⟨((1328854679/1099511627776), (10408265/137438953472)), (53/549755813888), by norm_num⟩
  | 11 => ⟨((-180949675/549755813888), (-90706547/4398046511104)), (59/2199023255552), by norm_num⟩
  | 12 => ⟨((361384521/4398046511104), (45288755/8796093022208)), (15/2199023255552), by norm_num⟩
  | 13 => ⟨((-333111161/17592186044416), (-20872767/17592186044416)), (113/70368744177664), by norm_num⟩
  | 14 => ⟨((285117673/70368744177664), (4466373/17592186044416)), (99/281474976710656), by norm_num⟩
  | 15 => ⟨((-911078629/1125899906842624), (-114176493/2251799813685248)), (161/2251799813685248), by norm_num⟩
  | 16 => ⟨((682336913/4503599627370496), (85510551/9007199254740992)), (123/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580610054254037/10141204801825835211973625643008), (81515156109/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777984441572471/633825300114114700748351602688), (48193939939/316912650057057350374175801344)), (46105/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888859709727537/39614081257132168796771975168), (54206105521/19807040628566084398385987584)), (103737/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118036246360713/154742504910672534362390528), (57578816181/1237940039285380274899124224)), (55111/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885123260077163/77371252455336267181195264), (57561757423/77371252455336267181195264)), (55111/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774334308935499/4835703278458516698824704), (26973014903/2417851639229258349412352)), (51667/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258014826164999/604462909807314587353088), (94369332707/604462909807314587353088)), (90419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943267590413821/37778931862957161709568), (38320572093/18889465931478580854784)), (36733/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296597376914803/4722366482869645213696), (7181397365/295147905179352825856)), (13775/590295810358705651712), by norm_num⟩
  | 9 => ⟨((101259605466841/36893488147419103232), (78947174305/295147905179352825856)), (18941/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821857974317465/73786976294838206464), (197223457621/73786976294838206464)), (94707/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820840064457493/9223372036854775808), (55419478549/2305843009213693952)), (213095/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592090931585679/1152921504606846976), (110715046055/576460752303423488)), (106551/576460752303423488), by norm_num⟩
  | 5 => ⟨((18639458628015/2251799813685248), (96736452453/72057594037927936)), (23309/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489159581232699/36028797018963968), (144826720001/18014398509481984)), (279723/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486169652813539/9007199254740992), (90274010605/2251799813685248)), (174841/4503599627370496), by norm_num⟩
  | 2 => ⟨((555449921939597/1125899906842624), (719288184489/4503599627370496)), (699451/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103475010506241/1125899906842624), (1071701744963/2251799813685248)), (1049403/2251799813685248), by norm_num⟩
  | 0 => ⟨((1081349698537157/1125899906842624), (1057328002561/1125899906842624)), (1049887/1125899906842624), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1081349698537157/1125899906842624), (1057328002561/1125899906842624)), (4005001072410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2077122567427905/2251799813685248), (4061964335819/2251799813685248)), (4037323/2251799813685248), by norm_num⟩
  | 2 => ⟨((1915988106199873/2251799813685248), (7493736999835/2251799813685248)), (1865711/562949953421312), by norm_num⟩
  | 3 => ⟨((815115589915017/1125899906842624), (12752386669023/2251799813685248)), (12749487/2251799813685248), by norm_num⟩
  | 4 => ⟨((1180163112268437/2251799813685248), (18464641695717/2251799813685248)), (9302425/1125899906842624), by norm_num⟩
  | 5 => ⟨((1236738736812779/4503599627370496), (19354552636609/2251799813685248)), (39613273/4503599627370496), by norm_num⟩
  | 6 => ⟨((678579107705619/9007199254740992), (21259904929295/4503599627370496)), (44874917/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43349291/16777216), (-315980599/4194304)), (1/16777216), by norm_num⟩, -12, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-22027651/8388608), (-321126835/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((257705984583747/9007199254740992), (-598791065548949/9007199254740992)), (364033923/18014398509481984), by norm_num⟩
  | 1 => ⟨((-187061227/2147483648), (217322449/1073741824)), (133/2147483648), by norm_num⟩
  | 2 => ⟨((569512103/4294967296), (-1323286145/4294967296)), (407/4294967296), by norm_num⟩
  | 3 => ⟨((-577964125/4294967296), (1342924787/4294967296)), (415/4294967296), by norm_num⟩
  | 4 => ⟨((439906187/4294967296), (-511070581/2147483648)), (159/2147483648), by norm_num⟩
  | 5 => ⟨((-535721703/8589934592), (1244772681/8589934592)), (389/8589934592), by norm_num⟩
  | 6 => ⟨((67959031/2147483648), (-1263246119/17179869184)), (397/17179869184), by norm_num⟩
  | 7 => ⟨((-236460337/17179869184), (549425879/17179869184)), (347/34359738368), by norm_num⟩
  | 8 => ⟨((359954401/68719476736), (-209092427/17179869184)), (133/34359738368), by norm_num⟩
  | 9 => ⟨((-487061889/274877906944), (565854743/137438953472)), (181/137438953472), by norm_num⟩
  | 10 => ⟨((148287085/274877906944), (-1378205969/1099511627776)), (443/1099511627776), by norm_num⟩
  | 11 => ⟨((-328336987/2199023255552), (95363159/274877906944)), (247/2199023255552), by norm_num⟩
  | 12 => ⟨((333209775/8796093022208), (-387113703/4398046511104)), (63/2199023255552), by norm_num⟩
  | 13 => ⟨((-312142965/35184372088832), (725277757/35184372088832)), (237/35184372088832), by norm_num⟩
  | 14 => ⟨((271521789/140737488355328), (-630892687/140737488355328)), (415/281474976710656), by norm_num⟩
  | 15 => ⟨((-440882229/1125899906842624), (256102259/281474976710656)), (339/1125899906842624), by norm_num⟩
  | 16 => ⟨((5243265/70368744177664), (-389854537/2251799813685248)), (65/1125899906842624), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580555238356451/10141204801825835211973625643008), (-1516734987475/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888958953446953/316912650057057350374175801344), (-448335975113/158456325028528675187087900672)), (184753/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888784780330231/39614081257132168796771975168), (-2017053667631/39614081257132168796771975168)), (207871/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888500223811125/2475880078570760549798248448), (-2142545594729/2475880078570760549798248448)), (220889/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885083341843691/77371252455336267181195264), (-2141900222407/154742504910672534362390528)), (220919/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774296822690561/4835703278458516698824704), (-1003673003863/4835703278458516698824704)), (103571/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257949099559505/604462909807314587353088), (-219467824441/75557863725914323419136)), (90641/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471607034928897/18889465931478580854784), (-2851797655427/75557863725914323419136)), (294641/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648258445195317/2361183241434822606848), (-534431325435/1180591620717411303424)), (221033/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620042684750005/590295810358705651712), (-1468774332265/295147905179352825856)), (76001/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821718721165103/73786976294838206464), (-917300601755/18446744073709551616)), (380131/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455170679728135/2305843009213693952), (-4124097521257/9223372036854775808)), (427821/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795966365484783/576460752303423488), (-4119408439821/1152921504606846976)), (428039/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192785967600883/144115188075855872), (-3599213901091/144115188075855872)), (374779/144115188075855872), by norm_num⟩
  | 4 => ⟨((46529643546177/1125899906842624), (-2694150347351/18014398509481984)), (140665/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485902590346145/9007199254740992), (-3358501679119/4503599627370496)), (352093/4503599627370496), by norm_num⟩
  | 2 => ⟨((69414238882991/140737488355328), (-3344759987007/1125899906842624)), (1410963/4503599627370496), by norm_num⟩
  | 1 => ⟨((1103054692490889/1125899906842624), (-9965834669029/1125899906842624)), (2122947/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160921187855381/2251799813685248), (-39318923748233/2251799813685248)), (4272053/2251799813685248), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160921187855381/2251799813685248), (-39318923748233/2251799813685248)), (16296588906295012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((518255927323973/562949953421312), (-37732082086007/1125899906842624)), (8348471/2251799813685248), by norm_num⟩
  | 2 => ⟨((476478019176687/562949953421312), (-34736436289769/562949953421312)), (3982723/562949953421312), by norm_num⟩
  | 3 => ⟨((50143152464083/70368744177664), (-235205964665487/2251799813685248)), (28933665/2251799813685248), by norm_num⟩
  | 4 => ⟨((279704920442705/562949953421312), (-335204747065155/2251799813685248)), (11819829/562949953421312), by norm_num⟩
  | 5 => ⟨((1011986279542349/4503599627370496), (-83274202742235/562949953421312)), (15264519/562949953421312), by norm_num⟩
  | 6 => ⟨((257705984583747/9007199254740992), (-598791065548949/9007199254740992)), (364033923/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22027651/8388608), (-321126835/4194304)), (1/8388608), by norm_num⟩, -12, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile033Terms2
