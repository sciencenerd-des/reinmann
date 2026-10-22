/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile060Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨60,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (79593/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (79593/2560))
  have he : value ((69/80), (79593/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2567700857/1073741824), (-92559336189/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-313257790641653/18014398509481984), (1618375142699129/18014398509481984)), (8757397/18014398509481984), by norm_num⟩
  | 1 => ⟨((13252792625/274877906944), (-68467539505/274877906944)), (93/68719476736), by norm_num⟩
  | 2 => ⟨((-18372271685/274877906944), (94916163935/274877906944)), (259/137438953472), by norm_num⟩
  | 3 => ⟨((16979584425/274877906944), (-87721161895/274877906944)), (481/274877906944), by norm_num⟩
  | 4 => ⟨((-11769351071/274877906944), (60803676043/274877906944)), (335/274877906944), by norm_num⟩
  | 5 => ⟨((13052628019/549755813888), (-67433434587/549755813888)), (373/549755813888), by norm_num⟩
  | 6 => ⟨((-12063189747/1099511627776), (31160863373/549755813888)), (173/549755813888), by norm_num⟩
  | 7 => ⟨((9556075385/2199023255552), (-49369290493/2199023255552)), (551/4398046511104), by norm_num⟩
  | 8 => ⟨((-13247533421/8796093022208), (68440369023/8796093022208)), (3/68719476736), by norm_num⟩
  | 9 => ⟨((16324427449/35184372088832), (-84336442355/35184372088832)), (475/35184372088832), by norm_num⟩
  | 10 => ⟨((-18104369377/140737488355328), (93532107579/140737488355328)), (529/140737488355328), by norm_num⟩
  | 11 => ⟨((9126540065/281474976710656), (-94300387869/562949953421312)), (535/562949953421312), by norm_num⟩
  | 12 => ⟨((-8434714019/1125899906842624), (87152063969/2251799813685248)), (31/140737488355328), by norm_num⟩
  | 13 => ⟨((7195690143/4503599627370496), (-18587448437/2251799813685248)), (425/9007199254740992), by norm_num⟩
  | 14 => ⟨((-2850098477/9007199254740992), (14724385689/9007199254740992)), (169/18014398509481984), by norm_num⟩
  | 15 => ⟨((4214480477/72057594037927936), (-87092620167/288230376151711744)), (251/144115188075855872), by norm_num⟩
  | 16 => ⟨((-11685021041/1152921504606846976), (15092001029/288230376151711744)), (175/576460752303423488), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (143449702279/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222284623525941/79228162514264337593543950336), (2714824357033/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472297133528255/9903520314283042199192993792), (1526769079321/19807040628566084398385987584)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888928938410437/2475880078570760549798248448), (3243592460645/2475880078570760549798248448)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((885297545244235/77371252455336267181195264), (1621350969499/77371252455336267181195264)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548994949904439/9671406556917033397649408), (3039087172651/9671406556917033397649408)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258299914370527/604462909807314587353088), (332281962553/75557863725914323419136)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886997601757731/75557863725914323419136), (2158946618817/37778931862957161709568)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296943451836557/4722366482869645213696), (3236869865687/4722366482869645213696)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620628338042455/590295810358705651712), (4448178485573/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911224743084211/36893488147419103232), (2778224481121/36893488147419103232)), (93/1152921504606846976), by norm_num⟩
  | 7 => ⟨((455375760537037/2305843009213693952), (1561454811829/2305843009213693952)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592750823445563/1152921504606846976), (6239342371073/1152921504606846976)), (6705/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193499293694173/144115188075855872), (5452145533597/144115188075855872)), (367/9007199254740992), by norm_num⟩
  | 4 => ⟨((1490013584906243/36028797018963968), (8163678815687/36028797018963968)), (2205/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487225110440539/9007199254740992), (10179196226543/9007199254740992)), (11045/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223874633833301/4503599627370496), (10141176299439/2251799813685248)), (11075/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209973116060593/2251799813685248), (15117006484739/1125899906842624)), (33377/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084195933644573/1125899906842624), (29856728708419/1125899906842624)), (33683/1125899906842624), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084195933644573/1125899906842624), (29856728708419/1125899906842624)), (128490452293014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521622477781429/562949953421312), (115003273953097/2251799813685248)), (133315/2251799813685248), by norm_num⟩
  | 2 => ⟨((1927442381792529/2251799813685248), (6660038377725/70368744177664)), (130337/1125899906842624), by norm_num⟩
  | 3 => ⟨((407408937393845/562949953421312), (364844943123669/2251799813685248)), (495595/2251799813685248), by norm_num⟩
  | 4 => ⟨((280064953869363/562949953421312), (528079235776359/2251799813685248)), (877925/2251799813685248), by norm_num⟩
  | 5 => ⟨((866963722958963/4503599627370496), (525433871726031/2251799813685248)), (2570599/4503599627370496), by norm_num⟩
  | 6 => ⟨((-313257790641653/18014398509481984), (1618375142699129/18014398509481984)), (8757397/18014398509481984), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-92559336189/1073741824)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-655961365/268435456), (-94583211821/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((388159444021095/4503599627370496), (-191763767137355/18014398509481984)), (3407585/18014398509481984), by norm_num⟩
  | 1 => ⟨((-8390339023/34359738368), (518138565/17179869184)), (149/274877906944), by norm_num⟩
  | 2 => ⟨((23771620481/68719476736), (-11743976771/274877906944)), (213/274877906944), by norm_num⟩
  | 3 => ⟨((-89800096475/274877906944), (2772765975/68719476736)), (203/274877906944), by norm_num⟩
  | 4 => ⟨((63605707907/274877906944), (-981979695/34359738368)), (73/137438953472), by norm_num⟩
  | 5 => ⟨((-2252606755/17179869184), (8902905521/549755813888)), (21/68719476736), by norm_num⟩
  | 6 => ⟨((34037949425/549755813888), (-4203971787/549755813888)), (161/1099511627776), by norm_num⟩
  | 7 => ⟨((-110213454303/4398046511104), (13612284531/4398046511104)), (263/4398046511104), by norm_num⟩
  | 8 => ⟨((19516139339/2199023255552), (-602601659/549755813888)), (47/2199023255552), by norm_num⟩
  | 9 => ⟨((-98299353599/35184372088832), (6070396663/17592186044416)), (239/35184372088832), by norm_num⟩
  | 10 => ⟨((111401216131/140737488355328), (-13758983063/140737488355328)), (273/140737488355328), by norm_num⟩
  | 11 => ⟨((-114772149849/562949953421312), (14175321605/562949953421312)), (283/562949953421312), by norm_num⟩
  | 12 => ⟨((54195664413/1125899906842624), (-1673404597/281474976710656)), (135/1125899906842624), by norm_num⟩
  | 13 => ⟨((-94491002833/9007199254740992), (11670430115/9007199254740992)), (237/9007199254740992), by norm_num⟩
  | 14 => ⟨((76489477177/36028797018963968), (-1180886369/4503599627370496)), (97/18014398509481984), by norm_num⟩
  | 15 => ⟨((-28894800989/72057594037927936), (14274999545/288230376151711744)), (37/36028797018963968), by norm_num⟩
  | 16 => ⟨((81865135735/1152921504606846976), (-10111029799/1152921504606846976)), (53/288230376151711744), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-160072797845/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889100178518903/316912650057057350374175801344), (-94661230231/316912650057057350374175801344)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889102561110121/39614081257132168796771975168), (-212942751265/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944418952094881/1237940039285380274899124224), (-226195303935/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885252203518633/77371252455336267181195264), (-226131918001/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774455153299321/4835703278458516698824704), (-211931350695/9671406556917033397649408)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629113111805883/302231454903657293676544), (-92686318853/302231454903657293676544)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886878551397275/75557863725914323419136), (-150552209899/37778931862957161709568)), (4593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296854773420533/4722366482869645213696), (-225718022961/4722366482869645213696)), (3445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810253697122435/295147905179352825856), (-310183169733/590295810358705651712)), (4737/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56946868371923/2305843009213693952), (-96865122777/18446744073709551616)), (5921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455334166323701/2305843009213693952), (-435524224155/9223372036854775808)), (3331/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398146745928121/288230376151711744), (-435063667311/1152921504606846976)), (3331/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193358781322363/144115188075855872), (-190081619869/72057594037927936)), (2915/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489808494005165/36028797018963968), (-569211562241/36028797018963968)), (8745/36028797018963968), by norm_num⟩
  | 3 => ⟨((743489322125723/4503599627370496), (-177427467079/2251799813685248)), (2733/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223411240351487/4503599627370496), (-88376293477/281474976710656)), (21869/4503599627370496), by norm_num⟩
  | 1 => ⟨((552337834516201/562949953421312), (-1053792397323/1125899906842624)), (32815/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167438365597351/2251799813685248), (-1040422899991/562949953421312)), (65679/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2167438365597351/2251799813685248), (-1040422899991/562949953421312)), (250545510298918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((521557436015823/562949953421312), (-8011555898287/2251799813685248)), (126681/2251799813685248), by norm_num⟩
  | 2 => ⟨((1932805187004439/2251799813685248), (-14844966332845/2251799813685248)), (235635/2251799813685248), by norm_num⟩
  | 3 => ⟨((1658902134720571/2251799813685248), (-25483995295365/2251799813685248)), (407617/2251799813685248), by norm_num⟩
  | 4 => ⟨((1221825688874857/2251799813685248), (-37548146100521/2251799813685248)), (304905/1125899906842624), by norm_num⟩
  | 5 => ⟨((165584007696277/562949953421312), (-81494436932493/4503599627370496)), (1364205/4503599627370496), by norm_num⟩
  | 6 => ⟨((388159444021095/4503599627370496), (-191763767137355/18014398509481984)), (3407585/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-94583211821/1073741824)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-83649375/33554432), (-24122843131/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-240717625082613/9007199254740992), (-352302917620801/4503599627370496)), (2037855/4503599627370496), by norm_num⟩
  | 1 => ⟨((5308253671/68719476736), (31075634867/137438953472)), (361/274877906944), by norm_num⟩
  | 2 => ⟨((-30685652989/274877906944), (-89820137379/274877906944)), (131/68719476736), by norm_num⟩
  | 3 => ⟨((7391078731/68719476736), (86537862791/274877906944)), (507/274877906944), by norm_num⟩
  | 4 => ⟨((-21362965225/274877906944), (-31265824325/137438953472)), (23/17179869184), by norm_num⟩
  | 5 => ⟨((24698764541/549755813888), (72295884493/549755813888)), (107/137438953472), by norm_num⟩
  | 6 => ⟨((-5949050957/274877906944), (-69653994251/1099511627776)), (207/549755813888), by norm_num⟩
  | 7 => ⟨((19651392997/2199023255552), (57521696517/2199023255552)), (43/274877906944), by norm_num⟩
  | 8 => ⟨((-28399915661/8796093022208), (-20782385885/2199023255552)), (499/8796093022208), by norm_num⟩
  | 9 => ⟨((18241403145/17592186044416), (53394507755/17592186044416)), (161/8796093022208), by norm_num⟩
  | 10 => ⟨((-10544887295/35184372088832), (-61731990897/70368744177664)), (187/35184372088832), by norm_num⟩
  | 11 => ⟨((22166286857/281474976710656), (32441527827/140737488355328)), (395/281474976710656), by norm_num⟩
  | 12 => ⟨((-5339067459/281474976710656), (-62512050543/1125899906842624)), (191/562949953421312), by norm_num⟩
  | 13 => ⟨((18993095135/4503599627370496), (3474674335/281474976710656)), (171/2251799813685248), by norm_num⟩
  | 14 => ⟨((-3921221841/4503599627370496), (-91822633745/36028797018963968)), (567/36028797018963968), by norm_num⟩
  | 15 => ⟨((6044687395/36028797018963968), (35386872975/72057594037927936)), (439/144115188075855872), by norm_num⟩
  | 16 => ⟨((-4367848433/144115188075855872), (-12785152281/144115188075855872)), (637/1152921504606846976), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-309370134589/1267650600228229401496703205376)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889059917597197/316912650057057350374175801344), (-2926965607837/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472252934963841/9903520314283042199192993792), (-3292118627543/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888741094073315/2475880078570760549798248448), (-3496986031879/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885203622853923/77371252455336267181195264), (-1747992552039/77371252455336267181195264)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548818844984293/9671406556917033397649408), (-409552859641/1208925819614629174706176)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629072911082081/302231454903657293676544), (-2865807228237/604462909807314587353088)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943373600624383/37778931862957161709568), (-4654944799311/75557863725914323419136)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648377825472013/2361183241434822606848), (-1744733214633/2361183241434822606848)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620370111132373/590295810358705651712), (-4795186781331/590295810358705651712)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822126701763787/73786976294838206464), (-187179428305/2305843009213693952)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910569954527793/4611686018427387904), (-3366315577121/4611686018427387904)), (3351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592387690181077/1152921504606846976), (-3362676037711/576460752303423488)), (6709/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193181552751395/144115188075855872), (-2938251346819/72057594037927936)), (1469/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489536976956083/36028797018963968), (-2199603689511/9007199254740992)), (4413/18014398509481984), by norm_num⟩
  | 3 => ⟨((185828670169517/1125899906842624), (-5484736474771/4503599627370496)), (5527/4503599627370496), by norm_num⟩
  | 2 => ⟨((138917699206757/281474976710656), (-10926751084969/2251799813685248)), (11087/2251799813685248), by norm_num⟩
  | 1 => ⟨((276023267726189/281474976710656), (-32567317619043/2251799813685248)), (2089/140737488355328), by norm_num⟩
  | 0 => ⟨((541204774146519/562949953421312), (-64286926891485/2251799813685248)), (33755/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((541204774146519/562949953421312), (-64286926891485/2251799813685248)), (128765110496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((519840716248177/562949953421312), (-123607406084431/2251799813685248)), (33415/562949953421312), by norm_num⟩
  | 2 => ⟨((956672770662639/1125899906842624), (-114141873752711/1125899906842624)), (65381/562949953421312), by norm_num⟩
  | 3 => ⟨((1602619233380321/2251799813685248), (-193971812144211/1125899906842624)), (497459/2251799813685248), by norm_num⟩
  | 4 => ⟨((67109877421159/140737488355328), (-276101769781387/1125899906842624)), (109937/281474976710656), by norm_num⟩
  | 5 => ⟨((376599896445557/2251799813685248), (-131657571428391/562949953421312)), (2540239/4503599627370496), by norm_num⟩
  | 6 => ⟨((-240717625082613/9007199254740992), (-352302917620801/4503599627370496)), (2037855/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-24122843131/268435456)), (1/536870912), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2726851779/1073741824), (-98296337707/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-1286306417162251/18014398509481984), (604643274184899/18014398509481984)), (3990757/9007199254740992), by norm_num⟩
  | 1 => ⟨((28895956069/137438953472), (-27165759659/274877906944)), (45/34359738368), by norm_num⟩
  | 2 => ⟨((-42541189695/137438953472), (39993960819/274877906944)), (133/68719476736), by norm_num⟩
  | 3 => ⟨((20876656193/68719476736), (-2453328691/17179869184)), (131/68719476736), by norm_num⟩
  | 4 => ⟨((-30735020125/137438953472), (14447353253/137438953472)), (97/68719476736), by norm_num⟩
  | 5 => ⟨((72397913025/549755813888), (-34031480051/549755813888)), (459/549755813888), by norm_num⟩
  | 6 => ⟨((-71057079041/1099511627776), (8350301365/274877906944)), (453/1099511627776), by norm_num⟩
  | 7 => ⟨((29889033325/1099511627776), (-28099374659/2199023255552)), (383/2199023255552), by norm_num⟩
  | 8 => ⟨((-22001608693/2199023255552), (20684223509/4398046511104)), (283/4398046511104), by norm_num⟩
  | 9 => ⟨((14396087609/4398046511104), (-6767048217/4398046511104)), (93/4398046511104), by norm_num⟩
  | 10 => ⟨((-33910721203/35184372088832), (31880256871/70368744177664)), (55/8796093022208), by norm_num⟩
  | 11 => ⟨((72616763143/281474976710656), (-17067176545/140737488355328)), (473/281474976710656), by norm_num⟩
  | 12 => ⟨((-17817968995/281474976710656), (4187771657/140737488355328)), (233/562949953421312), by norm_num⟩
  | 13 => ⟨((64570981463/4503599627370496), (-30352339945/4503599627370496)), (53/562949953421312), by norm_num⟩
  | 14 => ⟨((-27160759249/9007199254740992), (6383615203/4503599627370496)), (179/9007199254740992), by norm_num⟩
  | 15 => ⟨((42652372393/72057594037927936), (-20049243127/72057594037927936)), (565/144115188075855872), by norm_num⟩
  | 16 => ⟨((-31396826957/288230376151711744), (29516886483/576460752303423488)), (417/576460752303423488), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (3519892842237/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778043303189595/633825300114114700748351602688), (4162413678663/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944462700480183/19807040628566084398385987584), (4681664634915/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888649036785563/2475880078570760549798248448), (1243244491829/618970019642690137449562112)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770314826320279/154742504910672534362390528), (2485763105135/77371252455336267181195264)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548731817394083/9671406556917033397649408), (4659263706641/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629034644482287/302231454903657293676544), (4075314050635/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886622115446911/75557863725914323419136), (6619495557089/75557863725914323419136)), (2311/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296661207915195/4722366482869645213696), (1240523503299/1180591620717411303424)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620239231783373/590295810358705651712), (6818773514615/590295810358705651712)), (1193/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821961574777743/73786976294838206464), (1064663901569/9223372036854775808)), (5969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910476022246167/4611686018427387904), (2393378961749/2305843009213693952)), (6721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592197210762131/1152921504606846976), (9562948955267/1152921504606846976)), (6729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37281623431853/4503599627370496), (2088925618533/36028797018963968)), (5897/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489276726323633/36028797018963968), (12509822723033/36028797018963968)), (8863/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486293863518373/9007199254740992), (60921112683/35184372088832)), (5555/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110990911490443/2251799813685248), (7766852950159/1125899906842624)), (2789/562949953421312), by norm_num⟩
  | 1 => ⟨((551764704769853/562949953421312), (11572850770145/562949953421312)), (16851/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081133600964215/1125899906842624), (45674315699125/1125899906842624)), (8543/281474976710656), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081133600964215/1125899906842624), (45674315699125/1125899906842624)), (32588959813976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((129536794626269/140737488355328), (87716567171319/1125899906842624)), (136799/2251799813685248), by norm_num⟩
  | 2 => ⟨((473493155002009/562949953421312), (161471162797859/1125899906842624)), (68285/562949953421312), by norm_num⟩
  | 3 => ⟨((1546691903299783/2251799813685248), (543248932523009/2251799813685248)), (268909/1125899906842624), by norm_num⟩
  | 4 => ⟨((931315665051765/2251799813685248), (746281903305135/2251799813685248)), (998321/2251799813685248), by norm_num⟩
  | 5 => ⟨((275701407277463/4503599627370496), (154326335509207/562949953421312)), (2975009/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1286306417162251/18014398509481984), (604643274184899/18014398509481984)), (3990757/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-98296337707/1073741824)), (1/536870912), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1387177309/536870912), (-100008698881/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((151949787071559/4503599627370496), (608212622071385/9007199254740992)), (5776987/18014398509481984), by norm_num⟩
  | 1 => ⟨((-13891628451/137438953472), (-27802157305/137438953472)), (133/137438953472), by norm_num⟩
  | 2 => ⟨((41615599683/274877906944), (83287819913/274877906944)), (25/17179869184), by norm_num⟩
  | 3 => ⟨((-41556398351/274877906944), (-83169336703/274877906944)), (201/137438953472), by norm_num⟩
  | 4 => ⟨((972592529/8589934592), (62288266533/274877906944)), (303/274877906944), by norm_num⟩
  | 5 => ⟨((-4661802925/68719476736), (-74639588127/549755813888)), (365/549755813888), by norm_num⟩
  | 6 => ⟨((9310342317/274877906944), (74533407679/1099511627776)), (183/549755813888), by norm_num⟩
  | 7 => ⟨((-31875763379/2199023255552), (-63794895669/2199023255552)), (315/2199023255552), by norm_num⟩
  | 8 => ⟨((23872813275/4398046511104), (47778106961/4398046511104)), (237/4398046511104), by norm_num⟩
  | 9 => ⟨((-1986571033/1099511627776), (-63613518663/17592186044416)), (159/8796093022208), by norm_num⟩
  | 10 => ⟨((38087903727/70368744177664), (76227628357/70368744177664)), (383/70368744177664), by norm_num⟩
  | 11 => ⟨((-2593208237/17592186044416), (-83039115057/281474976710656)), (105/70368744177664), by norm_num⟩
  | 12 => ⟨((41432307241/1125899906842624), (5182561603/70368744177664)), (421/1125899906842624), by norm_num⟩
  | 13 => ⟨((-38190799991/4503599627370496), (-4777097555/281474976710656)), (195/2251799813685248), by norm_num⟩
  | 14 => ⟨((32688403453/18014398509481984), (16355320365/4503599627370496)), (21/1125899906842624), by norm_num⟩
  | 15 => ⟨((-26113521385/72057594037927936), (-52262571799/72057594037927936)), (135/36028797018963968), by norm_num⟩
  | 16 => ⟨((39114559395/576460752303423488), (78282336519/576460752303423488)), (407/576460752303423488), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (360634770583/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777982886506333/633825300114114700748351602688), (1705735355557/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((29513404294649/618970019642690137449562112), (1918523153329/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((59018058694381/77371252455336267181195264), (2037893710001/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885122164248607/77371252455336267181195264), (2037289700245/154742504910672534362390528)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((48395825849613/302231454903657293676544), (954658785829/4835703278458516698824704)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314503193358367/151115727451828646838272), (835005810373/302231454903657293676544)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886531590614705/75557863725914323419136), (2712567100569/75557863725914323419136)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296594461803701/4722366482869645213696), (127085895865/295147905179352825856)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620149318190085/590295810358705651712), (698545728331/147573952589676412928)), (2375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821851972058257/73786976294838206464), (436271288961/9223372036854775808)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820832569875549/9223372036854775808), (3922926922945/9223372036854775808)), (1671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592082511500965/1152921504606846976), (1959269055367/576460752303423488)), (209/36028797018963968), by norm_num⟩
  | 5 => ⟨((149114618279841/18014398509481984), (1711894831019/72057594037927936)), (5855/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489144902552403/36028797018963968), (2562918837843/18014398509481984)), (4395/18014398509481984), by norm_num⟩
  | 3 => ⟨((743073849068345/4503599627370496), (3195050051193/4503599627370496)), (1375/1125899906842624), by norm_num⟩
  | 2 => ⟨((277718127769567/562949953421312), (12728748708325/4503599627370496)), (11019/2251799813685248), by norm_num⟩
  | 1 => ⟨((137927584414189/140737488355328), (18964981278025/2251799813685248)), (33153/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162376672850373/2251799813685248), (9355076846729/562949953421312)), (16673/562949953421312), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162376672850373/2251799813685248), (9355076846729/562949953421312)), (63602449657249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1037941420785619/1125899906842624), (35934277679831/1125899906842624)), (130305/2251799813685248), by norm_num⟩
  | 2 => ⟨((1911415240609845/2251799813685248), (132507960976755/2251799813685248)), (248569/2251799813685248), by norm_num⟩
  | 3 => ⟨((807343050704595/1125899906842624), (112477909703081/1125899906842624)), (451245/2251799813685248), by norm_num⟩
  | 4 => ⟨((567680588181421/1125899906842624), (322615743032491/2251799813685248)), (92163/281474976710656), by norm_num⟩
  | 5 => ⟨((1052459526764347/4503599627370496), (650653556850751/4503599627370496)), (1909535/4503599627370496), by norm_num⟩
  | 6 => ⟨((151949787071559/4503599627370496), (608212622071385/9007199254740992)), (5776987/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-100008698881/1073741824)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2819539303/1073741824), (-101637496247/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((1195979266637551/18014398509481984), (-32445033543211/1125899906842624)), (1812283/9007199254740992), by norm_num⟩
  | 1 => ⟨((-27780042361/137438953472), (6029030311/68719476736)), (85/137438953472), by norm_num⟩
  | 2 => ⟨((84576962289/274877906944), (-36711036119/274877906944)), (261/274877906944), by norm_num⟩
  | 3 => ⟨((-85832153135/274877906944), (18627928863/137438953472)), (267/274877906944), by norm_num⟩
  | 4 => ⟨((65329479025/274877906944), (-55383933/536870912)), (205/274877906944), by norm_num⟩
  | 5 => ⟨((-79558825895/549755813888), (17266444975/274877906944)), (63/137438953472), by norm_num⟩
  | 6 => ⟨((80739543519/1099511627776), (-17522693049/549755813888)), (129/549755813888), by norm_num⟩
  | 7 => ⟨((-70232386245/2199023255552), (15242352045/1099511627776)), (227/2199023255552), by norm_num⟩
  | 8 => ⟨((53456018945/4398046511104), (-11601420701/2199023255552)), (175/4398046511104), by norm_num⟩
  | 9 => ⟨((-72332466271/17592186044416), (31396253897/17592186044416)), (239/17592186044416), by norm_num⟩
  | 10 => ⟨((88087126615/70368744177664), (-9558659945/17592186044416)), (293/70368744177664), by norm_num⟩
  | 11 => ⟨((-48760587901/140737488355328), (10582383519/70368744177664)), (41/35184372088832), by norm_num⟩
  | 12 => ⟨((49484234647/562949953421312), (-21478869379/562949953421312)), (21/70368744177664), by norm_num⟩
  | 13 => ⟨((-92711300121/4503599627370496), (40241784469/4503599627370496)), (317/4503599627370496), by norm_num⟩
  | 14 => ⟨((40323090493/9007199254740992), (-35004861643/18014398509481984)), (139/9007199254740992), by norm_num⟩
  | 15 => ⟨((-32737214337/36028797018963968), (28419489787/72057594037927936)), (57/18014398509481984), by norm_num⟩
  | 16 => ⟨((49834591799/288230376151711744), (-21630943581/288230376151711744)), (175/288230376151711744), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (-533439107175/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111119963641397/39614081257132168796771975168), (-630723084159/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888786563451225/39614081257132168796771975168), (-354701458475/19807040628566084398385987584)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888502229150473/2475880078570760549798248448), (-376769408575/1237940039285380274899124224)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770168813501775/154742504910672534362390528), (-11770498857/2417851639229258349412352)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548595774230517/9671406556917033397649408), (-705988956401/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((628975547165683/302231454903657293676544), (-154374867451/151115727451828646838272)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886431628519267/75557863725914323419136), (-125373155255/9444732965739290427392)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324129930781575/1180591620717411303424), (-375922094435/2361183241434822606848)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620046930501603/590295810358705651712), (-1033144732307/590295810358705651712)), (4741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821724553632771/73786976294838206464), (-1290470125227/73786976294838206464)), (5927/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910345000673027/4611686018427387904), (-725229511797/4611686018427387904)), (1667/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795970456257623/576460752303423488), (-1448811016365/1152921504606846976)), (3335/576460752303423488), by norm_num⟩
  | 5 => ⟨((149099266897399/18014398509481984), (-632929070039/72057594037927936)), (5837/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488962855373397/36028797018963968), (-947545237339/18014398509481984)), (4379/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485923920603693/9007199254740992), (-2362407872951/9007199254740992)), (1369/1125899906842624), by norm_num⟩
  | 2 => ⟨((2221308751492965/4503599627370496), (-588188278163/562949953421312)), (10959/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206214946767249/2251799813685248), (-7010181463243/2251799813685248)), (32913/2251799813685248), by norm_num⟩
  | 0 => ⟨((1080617313609605/1125899906842624), (-6914611239305/1125899906842624)), (8247/281474976710656), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1080617313609605/1125899906842624), (-6914611239305/1125899906842624)), (31459809423351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2074226953084677/2251799813685248), (-6636512337075/562949953421312)), (127457/2251799813685248), by norm_num⟩
  | 2 => ⟨((1910344220664469/2251799813685248), (-48905351818149/2251799813685248)), (118909/1125899906842624), by norm_num⟩
  | 3 => ⟨((1619603699149899/2251799813685248), (-82979006959295/2251799813685248)), (413843/2251799813685248), by norm_num⟩
  | 4 => ⟨((145229973974819/281474976710656), (-119365057059059/2251799813685248)), (625813/2251799813685248), by norm_num⟩
  | 5 => ⟨((296568033455411/1125899906842624), (-246350625306347/4503599627370496)), (1424275/4503599627370496), by norm_num⟩
  | 6 => ⟨((1195979266637551/18014398509481984), (-32445033543211/1125899906842624)), (1812283/9007199254740992), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-101637496247/1073741824)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨60,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile060Terms2
