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
namespace Reinmann.XiBand97.Tile062Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨62,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (80309/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (80309/2560))
  have he : value ((69/80), (80309/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-2567700857/1073741824), (-93391978315/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((227308886209951/4503599627370496), (343744024484797/4503599627370496)), (411309/1125899906842624), by norm_num⟩
  | 1 => ⟨((-19233216991/137438953472), (-58170215187/274877906944)), (281/274877906944), by norm_num⟩
  | 2 => ⟨((26662900261/137438953472), (80641041299/274877906944)), (49/34359738368), by norm_num⟩
  | 3 => ⟨((-49283504377/274877906944), (-37264073609/137438953472)), (91/68719476736), by norm_num⟩
  | 4 => ⟨((34160722107/274877906944), (12914743779/68719476736)), (127/137438953472), by norm_num⟩
  | 5 => ⟨((-37885453143/549755813888), (-57291636723/549755813888)), (71/137438953472), by norm_num⟩
  | 6 => ⟨((17506796687/549755813888), (52948715285/1099511627776)), (265/1099511627776), by norm_num⟩
  | 7 => ⟨((-27736655461/2199023255552), (-2621518051/137438953472)), (211/2199023255552), by norm_num⟩
  | 8 => ⟨((19225584531/4398046511104), (58147131067/8796093022208)), (295/8796093022208), by norm_num⟩
  | 9 => ⟨((-47381901199/35184372088832), (-71652479923/35184372088832)), (365/35184372088832), by norm_num⟩
  | 10 => ⟨((52548209961/140737488355328), (39732571551/70368744177664)), (407/140737488355328), by norm_num⟩
  | 11 => ⟨((-13244961301/140737488355328), (-80117876209/562949953421312)), (413/562949953421312), by norm_num⟩
  | 12 => ⟨((48963773773/2251799813685248), (74044640009/2251799813685248)), (3/17592186044416), by norm_num⟩
  | 13 => ⟨((-20885601071/4503599627370496), (-63167795025/9007199254740992)), (329/9007199254740992), by norm_num⟩
  | 14 => ⟨((16544909139/18014398509481984), (12509879721/9007199254740992)), (131/18014398509481984), by norm_num⟩
  | 15 => ⟨((-48930377055/288230376151711744), (-36997068193/144115188075855872)), (389/288230376151711744), by norm_num⟩
  | 16 => ⟨((33915952899/1152921504606846976), (25644413507/576460752303423488)), (17/72057594037927936), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395215189152397/2535301200456458802993406410752), (642537039493/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444569924871693/158456325028528675187087900672), (1520023375265/633825300114114700748351602688)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944595867381043/19807040628566084398385987584), (854835499345/19807040628566084398385987584)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888932538031621/2475880078570760549798248448), (1816082392949/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770598913685741/154742504910672534362390528), (56737005481/4835703278458516698824704)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548998771527261/9671406556917033397649408), (1701580990891/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258303495469791/604462909807314587353088), (5813884371/2361183241434822606848)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887003865338799/75557863725914323419136), (2417584519701/75557863725914323419136)), (4603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648474268932083/2361183241434822606848), (906160684863/2361183241434822606848)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810317980803145/295147905179352825856), (2490533793327/590295810358705651712)), (4749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822459959674075/73786976294838206464), (3111056536375/73786976294838206464)), (5937/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821516120699551/9223372036854775808), (437129838173/1152921504606846976)), (6681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796382759252263/576460752303423488), (3493417312493/1152921504606846976)), (6685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193513965891349/144115188075855872), (3052670861193/144115188075855872)), (1463/36028797018963968), by norm_num⟩
  | 4 => ⟨((186254901235951/4503599627370496), (4570879652449/36028797018963968)), (549/2251799813685248), by norm_num⟩
  | 3 => ⟨((1487263445373283/9007199254740992), (2849702380779/4503599627370496)), (10991/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111985056561345/2251799813685248), (5678166087341/2251799813685248)), (22017/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105081501942939/1125899906842624), (16928678733837/2251799813685248)), (16555/1125899906842624), by norm_num⟩
  | 0 => ⟨((2168956200557199/2251799813685248), (16718157695029/1125899906842624)), (66565/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2168956200557199/2251799813685248), (16718157695029/1125899906842624)), (253925332076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044331957078239/1125899906842624), (64412389723369/2251799813685248)), (65105/1125899906842624), by norm_num⟩
  | 2 => ⟨((241938024633769/281474976710656), (59745912235247/1125899906842624)), (249003/2251799813685248), by norm_num⟩
  | 3 => ⟨((414323930804193/562949953421312), (205415176227151/2251799813685248)), (227241/1125899906842624), by norm_num⟩
  | 4 => ⟨((1201009833614895/2251799813685248), (151182929750727/1125899906842624)), (751905/2251799813685248), by norm_num⟩
  | 5 => ⟨((1199928607540479/4503599627370496), (161268496605989/1125899906842624)), (2007987/4503599627370496), by norm_num⟩
  | 6 => ⟨((227308886209951/4503599627370496), (343744024484797/4503599627370496)), (411309/1125899906842624), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/1073741824), (-93391978315/1073741824)), (1/536870912), by norm_num⟩, -14, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-655961365/268435456), (-47717030129/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((476802652251059/9007199254740992), (-310049827581833/4503599627370496)), (1505207/4503599627370496), by norm_num⟩
  | 1 => ⟨((-41225696925/274877906944), (209435775/1073741824)), (131/137438953472), by norm_num⟩
  | 2 => ⟨((58400597323/274877906944), (-37976078877/137438953472)), (187/137438953472), by norm_num⟩
  | 3 => ⟨((-55153783879/274877906944), (71729555619/274877906944)), (89/68719476736), by norm_num⟩
  | 4 => ⟨((39065609115/274877906944), (-50806283535/274877906944)), (127/137438953472), by norm_num⟩
  | 5 => ⟨((-44272482015/549755813888), (57578016189/549755813888)), (145/274877906944), by norm_num⟩
  | 6 => ⟨((10452782235/274877906944), (-54376934597/1099511627776)), (69/274877906944), by norm_num⟩
  | 7 => ⟨((-4230708873/274877906944), (11004389765/549755813888)), (113/1099511627776), by norm_num⟩
  | 8 => ⟨((47946003335/8796093022208), (-31177783925/4398046511104)), (161/4398046511104), by norm_num⟩
  | 9 => ⟨((-7546736469/4398046511104), (4907406303/2199023255552)), (51/4398046511104), by norm_num⟩
  | 10 => ⟨((34210423149/70368744177664), (-44491932871/70368744177664)), (233/70368744177664), by norm_num⟩
  | 11 => ⟨((-35245609953/281474976710656), (1432444749/8796093022208)), (121/140737488355328), by norm_num⟩
  | 12 => ⟨((33286110813/1125899906842624), (-2705614385/70368744177664)), (231/1125899906842624), by norm_num⟩
  | 13 => ⟨((-29017431793/4503599627370496), (75476507367/9007199254740992)), (405/9007199254740992), by norm_num⟩
  | 14 => ⟨((23489307133/18014398509481984), (-30548721119/18014398509481984)), (165/18014398509481984), by norm_num⟩
  | 15 => ⟨((-35493449819/144115188075855872), (46160556969/144115188075855872)), (63/36028797018963968), by norm_num⟩
  | 16 => ⟨((50280257827/1152921504606846976), (-32695676493/576460752303423488)), (45/144115188075855872), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396322346299/5070602400912917605986812821504), (-1192280971301/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222274913816183/79228162514264337593543950336), (-705071598943/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236137665734193/4951760157141521099596496896), (-793037430445/19807040628566084398385987584)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888836514981961/2475880078570760549798248448), (-421196143143/618970019642690137449562112)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770502931555799/154742504910672534362390528), (-421078078407/38685626227668133590597632)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774454415868789/4835703278458516698824704), (-789270598807/4835703278458516698824704)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258224841588375/604462909807314587353088), (-1380722152609/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943438067086667/37778931862957161709568), (-2242733808959/75557863725914323419136)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296852810659995/4722366482869645213696), (-1681228555765/4722366482869645213696)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620504452261883/590295810358705651712), (-2310354637693/590295810358705651712)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911147873089259/36893488147419103232), (-2885942756589/73786976294838206464)), (371/4611686018427387904), by norm_num⟩
  | 7 => ⟨((227666452298925/1152921504606846976), (-3243937129919/9223372036854775808)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592581313157269/1152921504606846976), (-810126236457/288230376151711744)), (3341/576460752303423488), by norm_num⟩
  | 5 => ⟨((298338279942211/36028797018963968), (-2831585297441/144115188075855872)), (2925/72057594037927936), by norm_num⟩
  | 4 => ⟨((744899303253411/18014398509481984), (-4239676563575/36028797018963968)), (8781/36028797018963968), by norm_num⟩
  | 3 => ⟨((371740963340239/2251799813685248), (-5286144519657/9007199254740992)), (10987/9007199254740992), by norm_num⟩
  | 2 => ⟨((555843600999843/1125899906842624), (-2633010055785/1125899906842624)), (22005/4503599627370496), by norm_num⟩
  | 1 => ⟨((552319521621195/562949953421312), (-3924450994269/562949953421312)), (16543/1125899906842624), by norm_num⟩
  | 0 => ⟨((135451294126589/140737488355328), (-15498384713839/1125899906842624)), (66493/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((135451294126589/140737488355328), (-15498384713839/1125899906842624)), (253650673873137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085391765454141/2251799813685248), (-29832510028331/1125899906842624)), (129823/2251799813685248), by norm_num⟩
  | 2 => ⟨((964850177710547/1125899906842624), (-6906971745203/140737488355328)), (247339/2251799813685248), by norm_num⟩
  | 3 => ⟨((1648250717906265/2251799813685248), (-23675969330131/281474976710656)), (448197/2251799813685248), by norm_num⟩
  | 4 => ⟨((297634709274281/562949953421312), (-69320431076241/562949953421312)), (365767/1125899906842624), by norm_num⟩
  | 5 => ⟨((37206281611275/140737488355328), (-586401436923575/4503599627370496)), (1907383/4503599627370496), by norm_num⟩
  | 6 => ⟨((476802652251059/9007199254740992), (-310049827581833/4503599627370496)), (1505207/4503599627370496), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-655961365/268435456), (-47717030129/536870912)), (1/536870912), by norm_num⟩, -14, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-83649375/33554432), (-12169923291/134217728)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1351624867362367/18014398509481984), (-78139263723429/2251799813685248)), (8349579/18014398509481984), by norm_num⟩
  | 1 => ⟨((59611485961/274877906944), (27569765753/274877906944)), (185/137438953472), by norm_num⟩
  | 2 => ⟨((-43074838867/137438953472), (-4980429519/34359738368)), (537/274877906944), by norm_num⟩
  | 3 => ⟨((83001531825/274877906944), (38387447531/274877906944)), (65/34359738368), by norm_num⟩
  | 4 => ⟨((-59976320863/274877906944), (-13869249275/137438953472)), (189/137438953472), by norm_num⟩
  | 5 => ⟨((34670772793/274877906944), (16034914563/274877906944)), (439/549755813888), by norm_num⟩
  | 6 => ⟨((-16701903751/274877906944), (-15448954731/549755813888)), (425/1099511627776), by norm_num⟩
  | 7 => ⟨((55171098177/2199023255552), (25516127111/2199023255552)), (353/2199023255552), by norm_num⟩
  | 8 => ⟨((-19933123003/2199023255552), (-18437773293/4398046511104)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((51212565133/17592186044416), (23685341869/17592186044416)), (165/8796093022208), by norm_num⟩
  | 10 => ⟨((-14802335191/17592186044416), (-13691888643/35184372088832)), (383/70368744177664), by norm_num⟩
  | 11 => ⟨((3889477417/17592186044416), (28781562361/281474976710656)), (101/70368744177664), by norm_num⟩
  | 12 => ⟨((-29978761811/562949953421312), (-27729804999/1125899906842624)), (391/1125899906842624), by norm_num⟩
  | 13 => ⟨((1666341663/140737488355328), (1541335485/281474976710656)), (175/2251799813685248), by norm_num⟩
  | 14 => ⟨((-88070342981/36028797018963968), (-10182931555/9007199254740992)), (145/9007199254740992), by norm_num⟩
  | 15 => ⟨((33940804275/72057594037927936), (31394621631/144115188075855872)), (449/144115188075855872), by norm_num⟩
  | 16 => ⟨((-49050771059/576460752303423488), (-2835691491/72057594037927936)), (163/288230376151711744), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580728427068789/10141204801825835211973625643008), (-3527993443229/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889057548069101/316912650057057350374175801344), (-521539286525/79228162514264337593543950336)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944503073419039/19807040628566084398385987584), (-2346409004035/19807040628566084398385987584)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((29511481312079/38685626227668133590597632), (-4984849002601/2475880078570760549798248448)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885200282515187/77371252455336267181195264), (-77865943241/2417851639229258349412352)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193601520897391/1208925819614629174706176), (-4670439023991/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258139564772541/604462909807314587353088), (-2042558486817/302231454903657293676544)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943368128456195/37778931862957161709568), (-6635471230095/75557863725914323419136)), (2311/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296746764385863/4722366482869645213696), (-4974115898263/4722366482869645213696)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405089197822839/147573952589676412928), (-854421090013/73786976294838206464)), (1193/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911054201608189/36893488147419103232), (-8538152717925/73786976294838206464)), (5969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821117060205025/9223372036854775808), (-9597096322125/9223372036854775808)), (6721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398090504663737/288230376151711744), (-2396674059881/288230376151711744)), (6729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298288980742897/36028797018963968), (-8376668434323/144115188075855872)), (5897/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489492218654853/36028797018963968), (-6270822201977/18014398509481984)), (8863/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486562411241773/9007199254740992), (-15636231027549/9007199254740992)), (11109/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111258233200845/2251799813685248), (-7787549641231/1125899906842624)), (11157/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103927328965485/1125899906842624), (-11605093611571/562949953421312)), (4213/281474976710656), by norm_num⟩
  | 0 => ⟨((540958599554295/562949953421312), (-45812735688343/1125899906842624)), (34175/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((540958599554295/562949953421312), (-45812735688343/1125899906842624)), (130367283347701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1037788538638763/1125899906842624), (-88046168896899/1125899906842624)), (136923/2251799813685248), by norm_num⟩
  | 2 => ⟨((237421842868581/281474976710656), (-81155797595271/562949953421312)), (273831/2251799813685248), by norm_num⟩
  | 3 => ⟨((1555308858777437/2251799813685248), (-273817008527129/1125899906842624)), (270451/1125899906842624), by norm_num⟩
  | 4 => ⟨((941061730566779/2251799813685248), (-378248560514099/1125899906842624)), (1010291/2251799813685248), by norm_num⟩
  | 5 => ⟨((278274547061653/4503599627370496), (-316151766936371/1125899906842624)), (380813/562949953421312), by norm_num⟩
  | 6 => ⟨((-1351624867362367/18014398509481984), (-78139263723429/2251799813685248)), (8349579/18014398509481984), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83649375/33554432), (-12169923291/134217728)), (1/536870912), by norm_num⟩, -14, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-2726851779/1073741824), (-99180588555/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-430694177235979/18014398509481984), (677251838968487/9007199254740992)), (3877585/9007199254740992), by norm_num⟩
  | 1 => ⟨((4837618727/68719476736), (-60855917767/274877906944)), (175/137438953472), by norm_num⟩
  | 2 => ⟨((-7122036573/68719476736), (89593268193/274877906944)), (259/137438953472), by norm_num⟩
  | 3 => ⟨((27960536129/274877906944), (-21983492595/68719476736)), (255/137438953472), by norm_num⟩
  | 4 => ⟨((-10291011557/137438953472), (64729052495/274877906944)), (377/274877906944), by norm_num⟩
  | 5 => ⟨((24241004451/549755813888), (-76236298101/549755813888)), (223/274877906944), by norm_num⟩
  | 6 => ⟨((-371750825/17179869184), (74824375919/1099511627776)), (439/1099511627776), by norm_num⟩
  | 7 => ⟨((20015499331/2199023255552), (-31473687007/1099511627776)), (371/2199023255552), by norm_num⟩
  | 8 => ⟨((-29467208209/8796093022208), (46336175421/4398046511104)), (137/2199023255552), by norm_num⟩
  | 9 => ⟨((19280976991/17592186044416), (-15159337895/4398046511104)), (45/2199023255552), by norm_num⟩
  | 10 => ⟨((-5677166021/17592186044416), (35708596317/35184372088832)), (213/35184372088832), by norm_num⟩
  | 11 => ⟨((24314282071/281474976710656), (-76466751191/281474976710656)), (229/140737488355328), by norm_num⟩
  | 12 => ⟨((-11931986647/562949953421312), (75050560939/1125899906842624)), (113/281474976710656), by norm_num⟩
  | 13 => ⟨((21620311743/4503599627370496), (-67994399089/4503599627370496)), (411/4503599627370496), by norm_num⟩
  | 14 => ⟨((-4547120617/4503599627370496), (57201531155/18014398509481984)), (347/18014398509481984), by norm_num⟩
  | 15 => ⟨((14281300467/72057594037927936), (-44913711467/72057594037927936)), (547/144115188075855872), by norm_num⟩
  | 16 => ⟨((-5256302221/144115188075855872), (66122841371/576460752303423488)), (405/576460752303423488), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790333841204085/5070602400912917605986812821504), (2447162479225/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889024051011773/316912650057057350374175801344), (2893867238005/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888931063871533/39614081257132168796771975168), (813719730811/9903520314283042199192993792)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888655405456645/2475880078570760549798248448), (1728706260327/1237940039285380274899124224)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770321590399209/154742504910672534362390528), (432050561905/19342813113834066795298816)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548738578510763/9671406556917033397649408), (3239308528219/9671406556917033397649408)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314518906091313/151115727451828646838272), (2833324659557/604462909807314587353088)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886633196108333/75557863725914323419136), (4602146568905/75557863725914323419136)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81041887816173/295147905179352825856), (1724927744231/2361183241434822606848)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810126358595083/295147905179352825856), (2370350930391/295147905179352825856)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821980100471237/73786976294838206464), (740200730251/9223372036854775808)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820975176516433/9223372036854775808), (1663984404533/2305843009213693952)), (3351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592223199816743/1152921504606846976), (6648607926275/1152921504606846976)), (1677/288230376151711744), by norm_num⟩
  | 5 => ⟨((298259473957089/36028797018963968), (5809294964753/144115188075855872)), (1469/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489322035110899/36028797018963968), (4348745409575/18014398509481984)), (8825/36028797018963968), by norm_num⟩
  | 3 => ⟨((743180816775859/4503599627370496), (5421561665405/4503599627370496)), (11053/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222150573440383/4503599627370496), (1350014153621/281474976710656)), (11085/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103697150846707/1125899906842624), (32185989378055/2251799813685248)), (33417/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163263597178157/2251799813685248), (7939846225639/281474976710656)), (2109/70368744177664), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2163263597178157/2251799813685248), (7939846225639/281474976710656)), (8045196801638581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2076416708244821/2251799813685248), (122042680367807/2251799813685248)), (133477/2251799813685248), by norm_num⟩
  | 2 => ⟨((477019749306129/562949953421312), (225074590640425/2251799813685248)), (32579/281474976710656), by norm_num⟩
  | 3 => ⟨((1594327731301241/2251799813685248), (95359298060127/562949953421312)), (61725/281474976710656), by norm_num⟩
  | 4 => ⟨((532104712108037/1125899906842624), (16879161772141/70368744177664)), (866537/2251799813685248), by norm_num⟩
  | 5 => ⟨((746778505708327/4503599627370496), (1021076231539845/4503599627370496)), (2469531/4503599627370496), by norm_num⟩
  | 6 => ⟨((-430694177235979/18014398509481984), (677251838968487/9007199254740992)), (3877585/9007199254740992), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2726851779/1073741824), (-99180588555/1073741824)), (1/536870912), by norm_num⟩, -15, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-1387177309/536870912), (-50454176865/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1310717279873163/18014398509481984), (362119305598579/18014398509481984)), (1688549/9007199254740992), by norm_num⟩
  | 1 => ⟨((-59914521131/274877906944), (-16552924967/274877906944)), (39/68719476736), by norm_num⟩
  | 2 => ⟨((89743932303/274877906944), (24794065773/274877906944)), (59/68719476736), by norm_num⟩
  | 3 => ⟨((-89616264785/274877906944), (-24758794343/274877906944)), (119/137438953472), by norm_num⟩
  | 4 => ⟨((67116584163/274877906944), (18542679817/274877906944)), (45/68719476736), by norm_num⟩
  | 5 => ⟨((-80425326907/549755813888), (-11109780873/274877906944)), (109/274877906944), by norm_num⟩
  | 6 => ⟨((80310915809/1099511627776), (11093976371/549755813888)), (55/274877906944), by norm_num⟩
  | 7 => ⟨((-4296250043/137438953472), (-9495595159/1099511627776)), (95/1099511627776), by norm_num⟩
  | 8 => ⟨((102963319273/8796093022208), (14223130437/4398046511104)), (287/8796093022208), by norm_num⟩
  | 9 => ⟨((-8568070515/2199023255552), (-18937195947/17592186044416)), (193/17592186044416), by norm_num⟩
  | 10 => ⟨((20534116291/17592186044416), (5673076907/17592186044416)), (117/35184372088832), by norm_num⟩
  | 11 => ⟨((-89475948919/281474976710656), (-24720028481/281474976710656)), (257/281474976710656), by norm_num⟩
  | 12 => ⟨((22337165657/281474976710656), (24684862375/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | 13 => ⟨((-82358360687/4503599627370496), (-22753611965/4503599627370496)), (241/4503599627370496), by norm_num⟩
  | 14 => ⟨((8811557111/2251799813685248), (1217209459/1125899906842624)), (13/1125899906842624), by norm_num⟩
  | 15 => ⟨((-28156870419/36028797018963968), (-15558116949/72057594037927936)), (21/9007199254740992), by norm_num⟩
  | 16 => ⟨((84350445437/576460752303423488), (11651988265/288230376151711744)), (127/288230376151711744), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395152513565329/2535301200456458802993406410752), (2743135393/79228162514264337593543950336)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888992177067729/316912650057057350374175801344), (415184638341/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((118053725409843/2475880078570760549798248448), (466978654071/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888579825742533/2475880078570760549798248448), (248017060821/1237940039285380274899124224)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885123198460863/77371252455336267181195264), (247943579621/77371252455336267181195264)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774334247346265/4835703278458516698824704), (232369062827/4835703278458516698824704)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629007355371375/302231454903657293676544), (406489842937/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886534978953919/75557863725914323419136), (165063402423/18889465931478580854784)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648298606500237/2361183241434822606848), (494934517051/4722366482869645213696)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620153441787157/590295810358705651712), (85014967409/73786976294838206464)), (4739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821857636811793/73786976294838206464), (424763661171/36893488147419103232)), (1481/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910419821518301/4611686018427387904), (477431642267/4611686018427387904)), (6665/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99505653632569/72057594037927936), (29806117587/36028797018963968)), (3333/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192924879520255/144115188075855872), (833371936755/144115188075855872)), (5833/144115188075855872), by norm_num⟩
  | 4 => ⟨((744579377917613/18014398509481984), (1247663203649/36028797018963968)), (547/2251799813685248), by norm_num⟩
  | 3 => ⟨((371542104567767/2251799813685248), (1555397283155/9007199254740992)), (10943/9007199254740992), by norm_num⟩
  | 2 => ⟨((138862288363191/281474976710656), (774571336703/1125899906842624)), (10947/2251799813685248), by norm_num⟩
  | 1 => ⟨((551735977554499/562949953421312), (4616280418613/2251799813685248)), (16433/1125899906842624), by norm_num⟩
  | 0 => ⟨((2162681249261631/2251799813685248), (4554360123299/1125899906842624)), (65831/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2162681249261631/2251799813685248), (4554360123299/1125899906842624)), (251125344283293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64907901513635/70368744177664), (17496456267885/2251799813685248)), (126985/2251799813685248), by norm_num⟩
  | 2 => ⟨((239466358365775/281474976710656), (8069337271433/562949953421312)), (59059/562949953421312), by norm_num⟩
  | 3 => ⟨((1629355729106855/2251799813685248), (54920258515247/2251799813685248)), (408731/2251799813685248), by norm_num⟩
  | 4 => ⟨((1177628597827307/2251799813685248), (19869581059561/562949953421312)), (611437/2251799813685248), by norm_num⟩
  | 5 => ⟨((1226123478656573/4503599627370496), (166259801535679/4503599627370496)), (1365383/4503599627370496), by norm_num⟩
  | 6 => ⟨((1310717279873163/18014398509481984), (362119305598579/18014398509481984)), (1688549/9007199254740992), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1387177309/536870912), (-50454176865/536870912)), (1/536870912), by norm_num⟩, -15, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-2819539303/1073741824), (-6409487711/67108864)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((99360117389895/4503599627370496), (-620865043910097/9007199254740992)), (1481895/4503599627370496), by norm_num⟩
  | 1 => ⟨((-18463385425/274877906944), (901335505/4294967296)), (277/274877906944), by norm_num⟩
  | 2 => ⟨((28106095601/274877906944), (-87812357405/274877906944)), (53/34359738368), by norm_num⟩
  | 3 => ⟨((-14261606449/137438953472), (89115564143/274877906944)), (27/17179869184), by norm_num⟩
  | 4 => ⟨((1356868151/17179869184), (-33914291823/137438953472)), (165/137438953472), by norm_num⟩
  | 5 => ⟨((-26438499397/549755813888), (20650564483/137438953472)), (101/137438953472), by norm_num⟩
  | 6 => ⟨((26830868211/1099511627776), (-2619629455/34359738368)), (103/274877906944), by norm_num⟩
  | 7 => ⟨((-23339194369/2199023255552), (36459522991/1099511627776)), (45/274877906944), by norm_num⟩
  | 8 => ⟨((8882087617/2199023255552), (-13875229477/1099511627776)), (69/1099511627776), by norm_num⟩
  | 9 => ⟨((-24037080039/17592186044416), (75099462171/17592186044416)), (375/17592186044416), by norm_num⟩
  | 10 => ⟨((29272571807/70368744177664), (-91456799057/70368744177664)), (459/70368744177664), by norm_num⟩
  | 11 => ⟨((-32407636973/281474976710656), (101251737023/281474976710656)), (511/281474976710656), by norm_num⟩
  | 12 => ⟨((32888592639/1125899906842624), (-102754395075/1125899906842624)), (521/1125899906842624), by norm_num⟩
  | 13 => ⟨((-1925578043/281474976710656), (6016116565/281474976710656)), (491/4503599627370496), by norm_num⟩
  | 14 => ⟨((26799842549/18014398509481984), (-83731208549/18014398509481984)), (429/18014398509481984), by norm_num⟩
  | 15 => ⟨((-2719757399/9007199254740992), (33989539089/36028797018963968)), (351/72057594037927936), by norm_num⟩
  | 16 => ⟨((16560724853/288230376151711744), (-103481914405/576460752303423488)), (537/576460752303423488), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395138809596695/2535301200456458802993406410752), (-821316148329/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888958804366939/316912650057057350374175801344), (-1942201264121/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888784428556989/39614081257132168796771975168), (-2184479799741/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944249914098073/1237940039285380274899124224), (-290048522359/309485009821345068724781056)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885083131756355/77371252455336267181195264), (-1159844591647/77371252455336267181195264)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193574153174211/1208925819614629174706176), (-2173966201905/9671406556917033397649408)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628974353010231/302231454903657293676544), (-7427649723/2361183241434822606848)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886427451421021/75557863725914323419136), (-3088511509951/75557863725914323419136)), (2303/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296516331525445/4722366482869645213696), (-2315167362311/4722366482869645213696)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1620041847107397/590295810358705651712), (-3181379916875/590295810358705651712)), (297/36893488147419103232), by norm_num⟩
  | 8 => ⟨((910858785235811/36893488147419103232), (-1986882121227/36893488147419103232)), (2971/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910340641071813/4611686018427387904), (-558302171821/1152921504606846976)), (209/288230376151711744), by norm_num⟩
  | 6 => ⟨((1591931116801463/1152921504606846976), (-2230669186533/576460752303423488)), (1673/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192784356177715/144115188075855872), (-3897964405847/144115188075855872)), (5859/144115188075855872), by norm_num⟩
  | 4 => ⟨((744472889828965/18014398509481984), (-5835551260451/36028797018963968)), (8797/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485898381941075/9007199254740992), (-1818634409593/2251799813685248)), (11011/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221245166288557/4503599627370496), (-14489532347297/4503599627370496)), (1379/281474976710656), by norm_num⟩
  | 1 => ⟨((2206088557782843/2251799813685248), (-10793002327003/1125899906842624)), (16603/1125899906842624), by norm_num⟩
  | 0 => ⟨((2160859346932599/2251799813685248), (-21291101778363/1125899906842624)), (16713/562949953421312), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2160859346932599/2251799813685248), (-21291101778363/1125899906842624)), (63755037547874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2072786330649659/2251799813685248), (-40862492309185/1125899906842624)), (65417/1125899906842624), by norm_num⟩
  | 2 => ⟨((1905037993762273/2251799813685248), (-150456030735945/2251799813685248)), (62591/562949953421312), by norm_num⟩
  | 3 => ⟨((50050696094497/70368744177664), (-254573655438363/2251799813685248)), (457077/2251799813685248), by norm_num⟩
  | 4 => ⟨((1110394516694367/2251799813685248), (-181068865316699/1125899906842624)), (376777/1125899906842624), by norm_num⟩
  | 5 => ⟨((244655905924731/1125899906842624), (-714301063424235/4503599627370496)), (61597/140737488355328), by norm_num⟩
  | 6 => ⟨((99360117389895/4503599627370496), (-620865043910097/9007199254740992)), (1481895/4503599627370496), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2819539303/1073741824), (-6409487711/67108864)), (1/536870912), by norm_num⟩, -15, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨62,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand97.Tile062Terms2
