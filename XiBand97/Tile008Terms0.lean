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
namespace Reinmann.XiBand97.Tile008Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (11709/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (11709/640))
  have he : value ((69/80), (11709/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/33554432), (-1702061217/134217728)), (1/67108864), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((615155069939773/1125899906842624), (-142079865362761/2251799813685248)), (20809189/2251799813685248), by norm_num⟩
  | 1 => ⟨((-406640055/1073741824), (366875/8388608)), (15/2147483648), by norm_num⟩
  | 2 => ⟨((1127445631/8589934592), (-65100383/4294967296)), (23/8589934592), by norm_num⟩
  | 3 => ⟨((-520990507/17179869184), (60165529/17179869184)), (23/34359738368), by norm_num⟩
  | 4 => ⟨((361123101/68719476736), (-166814267/274877906944)), (17/137438953472), by norm_num⟩
  | 5 => ⟨((-400498335/549755813888), (92501471/1099511627776)), (5/274877906944), by norm_num⟩
  | 6 => ⟨((1480556223/17592186044416), (-10686189/1099511627776)), (39/17592186044416), by norm_num⟩
  | 7 => ⟨((-36651549/4398046511104), (135444147/140737488355328)), (33/140737488355328), by norm_num⟩
  | 8 => ⟨((1625914743/2251799813685248), (-187765457/2251799813685248)), (3/140737488355328), by norm_num⟩
  | 9 => ⟨((-250444049/4503599627370496), (57844043/9007199254740992)), (1/562949953421312), by norm_num⟩
  | 10 => ⟨((1111005353/288230376151711744), (-128302193/288230376151711744)), (37/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1120131241/4611686018427387904), (64678039/2305843009213693952)), (39/4611686018427387904), by norm_num⟩
  | 12 => ⟨((517610541/36893488147419103232), (-119550401/73786976294838206464)), (37/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-220787869/295147905179352825856), (12748619/147573952589676412928)), (65/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((1399209041/37778931862957161709568), (-80792405/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((-1034514989/604462909807314587353088), (119468859/604462909807314587353088)), (21/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((179267787/2417851639229258349412352), (-82809503/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-149766033973/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890524203545891/316912650057057350374175801344), (-177672290259/633825300114114700748351602688)), (23055/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946153094491387/19807040628566084398385987584), (-99935274053/19807040628566084398385987584)), (25937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946120615564249/1237940039285380274899124224), (-212349497145/2475880078570760549798248448)), (13779/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773907140519177/154742504910672534362390528), (-106167459095/77371252455336267181195264)), (27559/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776049869426843/4835703278458516698824704), (-199048497063/9671406556917033397649408)), (25837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78813521664675/37778931862957161709568), (-87075973883/302231454903657293676544)), (1413/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1891411320075567/75557863725914323419136), (-141483940017/37778931862957161709568)), (18369/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650126658370159/2361183241434822606848), (-212200507673/4722366482869645213696)), (13777/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625178713110215/590295810358705651712), (-145867212751/295147905179352825856)), (37/576460752303423488), by norm_num⟩
  | 8 => ⟨((914068210232817/36893488147419103232), (-364606134033/73786976294838206464)), (23681/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827899419486287/9223372036854775808), (-205048404545/4611686018427387904)), (53283/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399786354804835/288230376151711744), (-409990471217/1152921504606846976)), (26643/576460752303423488), by norm_num⟩
  | 5 => ⟨((149886569769493/18014398509481984), (-358622068979/144115188075855872)), (46629/144115188075855872), by norm_num⟩
  | 4 => ⟨((93649966342985/2251799813685248), (-537694008691/36028797018963968)), (17487/9007199254740992), by norm_num⟩
  | 3 => ⟨((187212550820007/1125899906842624), (-671699301687/9007199254740992)), (87445/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122402009938805/2251799813685248), (-671072401077/2251799813685248)), (174921/4503599627370496), by norm_num⟩
  | 1 => ⟨((280164247511043/281474976710656), (-1005042795193/1125899906842624)), (262461/2251799813685248), by norm_num⟩
  | 0 => ⟨((1115429773932053/1125899906842624), (-2003831027797/1125899906842624)), (525239/2251799813685248), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115429773932053/1125899906842624), (-2003831027797/1125899906842624)), (2003627785689543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((552526720036949/562949953421312), (-3970393419077/1125899906842624)), (260645/562949953421312), by norm_num⟩
  | 2 => ⟨((271144738083263/281474976710656), (-1948440034293/281474976710656)), (2053907/2251799813685248), by norm_num⟩
  | 3 => ⟨((1044720542206421/1125899906842624), (-30030904711641/2251799813685248)), (996373/562949953421312), by norm_num⟩
  | 4 => ⟨((1938388201059077/2251799813685248), (-55731247267401/2251799813685248)), (7502567/2251799813685248), by norm_num⟩
  | 5 => ⟨((833609369551139/1125899906842624), (-95948841879189/2251799813685248)), (3322013/562949953421312), by norm_num⟩
  | 6 => ⟨((615155069939773/1125899906842624), (-142079865362761/2251799813685248)), (20809189/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1702061217/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/16777216), (-674425801/33554432)), (1/33554432), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((137679463762885/1125899906842624), (-828432877509923/2251799813685248)), (123122523/4503599627370496), by norm_num⟩
  | 1 => ⟨((-144249297/1073741824), (433982153/1073741824)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((316948101/4294967296), (-953556253/4294967296)), (37/2147483648), by norm_num⟩
  | 3 => ⟨((-116067693/4294967296), (174598103/2147483648)), (111/17179869184), by norm_num⟩
  | 4 => ⟨((63756697/8589934592), (-1534524973/68719476736)), (125/68719476736), by norm_num⟩
  | 5 => ⟨((-448280901/274877906944), (674339197/137438953472)), (113/274877906944), by norm_num⟩
  | 6 => ⟨((82081151/274877906944), (-987783105/1099511627776)), (85/1099511627776), by norm_num⟩
  | 7 => ⟨((-412230223/8796093022208), (1240217895/8796093022208)), (109/8796093022208), by norm_num⟩
  | 8 => ⟨((452881189/70368744177664), (-340629655/17592186044416)), (61/35184372088832), by norm_num⟩
  | 9 => ⟨((-110564631/140737488355328), (1330559733/562949953421312)), (121/562949953421312), by norm_num⟩
  | 10 => ⟨((388696519/4503599627370496), (-1169415419/4503599627370496)), (109/4503599627370496), by norm_num⟩
  | 11 => ⟨((-310564925/36028797018963968), (934352109/36028797018963968)), (89/36028797018963968), by norm_num⟩
  | 12 => ⟨((454920591/576460752303423488), (-1368654279/576460752303423488)), (133/576460752303423488), by norm_num⟩
  | 13 => ⟨((-307557755/4611686018427387904), (231326217/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 14 => ⟨((193078131/36893488147419103232), (-1161772913/73786976294838206464)), (59/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-28282401/73786976294838206464), (1361427199/1180591620717411303424)), (141/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((497142293/18889465931478580854784), (-1495680651/18889465931478580854784)), (79/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-101758330901/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890253084529337/316912650057057350374175801344), (-965197558845/316912650057057350374175801344)), (46195/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891696095703871/39614081257132168796771975168), (-1085753970463/19807040628566084398385987584)), (6497/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472898228094373/618970019642690137449562112), (-2307003776961/2475880078570760549798248448)), (55231/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221657339417301/19342813113834066795298816), (-288344056317/19342813113834066795298816)), (55239/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387872931802127/2417851639229258349412352), (-2162313404447/9671406556917033397649408)), (12949/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260484223455895/604462909807314587353088), (-1891757229399/604462909807314587353088)), (45329/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945273204079259/37778931862957161709568), (-768401228231/18889465931478580854784)), (73675/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299604447623845/4722366482869645213696), (-1152382856081/2361183241434822606848)), (55271/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812143108677065/295147905179352825856), (-3168341222413/590295810358705651712)), (76019/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827020350029271/73786976294838206464), (-3959359209085/73786976294838206464)), (47529/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826643221028691/9223372036854775808), (-4452811756077/9223372036854775808)), (53493/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597888447569345/1152921504606846976), (-4450977877687/1152921504606846976)), (26761/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197991839259317/144115188075855872), (-3892542962267/144115188075855872)), (93729/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496746648581775/36028797018963968), (-5834690164185/36028797018963968)), (140723/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495631361341691/9007199254740992), (-3643073827151/4503599627370496)), (176133/9007199254740992), by norm_num⟩
  | 2 => ⟨((280082108467957/562949953421312), (-227354061255/70368744177664)), (44119/562949953421312), by norm_num⟩
  | 1 => ⟨((1117535343500373/1125899906842624), (-2721491955887/281474976710656)), (265571/1125899906842624), by norm_num⟩
  | 0 => ⟨((554570809360019/562949953421312), (-5415982534475/281474976710656)), (267291/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554570809360019/562949953421312), (-5415982534475/281474976710656)), (1019634248973655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((136526990214035/140737488355328), (-42682953244701/1125899906842624)), (33557/35184372088832), by norm_num⟩
  | 2 => ⟨((1057921559372335/1125899906842624), (-10351497685593/140737488355328)), (2164815/1125899906842624), by norm_num⟩
  | 3 => ⟨((987956562343729/1125899906842624), (-19453012664495/140737488355328)), (4386673/1125899906842624), by norm_num⟩
  | 4 => ⟨((1690806265073587/2251799813685248), (-273114601430443/1125899906842624)), (556945/70368744177664), by norm_num⟩
  | 5 => ⟨((1137072429082255/2251799813685248), (-51268309506821/140737488355328)), (35410771/2251799813685248), by norm_num⟩
  | 6 => ⟨((137679463762885/1125899906842624), (-828432877509923/2251799813685248)), (123122523/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-674425801/33554432)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-20060163/16777216), (-1702061217/67108864)), (1/33554432), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((82904591644447/281474976710656), (-77627814855541/1125899906842624)), (6400997/562949953421312), by norm_num⟩
  | 1 => ⟨((-876847595/2147483648), (205259327/2147483648)), (9/536870912), by norm_num⟩
  | 2 => ⟨((1215568877/4294967296), (-35568731/536870912)), (13/1073741824), by norm_num⟩
  | 3 => ⟨((-1123424187/8589934592), (65744975/2147483648)), (25/4294967296), by norm_num⟩
  | 4 => ⟨((194674577/4294967296), (-356023/33554432)), (9/4294967296), by norm_num⟩
  | 5 => ⟨((-863604059/68719476736), (404318353/137438953472)), (83/137438953472), by norm_num⟩
  | 6 => ⟨((798139625/274877906944), (-186834751/274877906944)), (79/549755813888), by norm_num⟩
  | 7 => ⟨((-632260835/1099511627776), (296009099/2199023255552)), (65/2199023255552), by norm_num⟩
  | 8 => ⟨((438249815/4398046511104), (-12823617/549755813888)), (47/8796093022208), by norm_num⟩
  | 9 => ⟨((-270019221/17592186044416), (31604103/8796093022208)), (59/70368744177664), by norm_num⟩
  | 10 => ⟨((1197843595/562949953421312), (-280400575/562949953421312)), (17/140737488355328), by norm_num⟩
  | 11 => ⟨((-1207682779/4503599627370496), (4417247/70368744177664)), (35/2251799813685248), by norm_num⟩
  | 12 => ⟨((279033971/9007199254740992), (-261273797/36028797018963968)), (67/36028797018963968), by norm_num⟩
  | 13 => ⟨((-952180235/288230376151711744), (222893779/288230376151711744)), (59/288230376151711744), by norm_num⟩
  | 14 => ⟨((754286909/2305843009213693952), (-176569365/2305843009213693952)), (3/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1115374601/36893488147419103232), (261095589/36893488147419103232)), (73/36893488147419103232), by norm_num⟩
  | 16 => ⟨((96639845/36893488147419103232), (-361955343/590295810358705651712)), (103/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-299532067945/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780124951873385/633825300114114700748351602688), (-22187176897/39614081257132168796771975168)), (23059/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891267382305469/39614081257132168796771975168), (-199663337717/19807040628566084398385987584)), (12971/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891137596317371/2475880078570760549798248448), (-106058206507/618970019642690137449562112)), (6891/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110800225946087/9671406556917033397649408), (-424174599759/154742504910672534362390528)), (27565/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551065300061657/9671406556917033397649408), (-99400458261/2417851639229258349412352)), (25843/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630055664463989/302231454903657293676544), (-173919881131/302231454903657293676544)), (45227/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889940884208339/75557863725914323419136), (-282561843651/37778931862957161709568)), (73495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649575340235721/2361183241434822606848), (-423741356615/4722366482869645213696)), (13781/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623662897948319/590295810358705651712), (-291239813011/295147905179352825856)), (9475/73786976294838206464), by norm_num⟩
  | 8 => ⟨((913121057977605/36893488147419103232), (-727852511145/73786976294838206464)), (23689/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825768965325171/9223372036854775808), (-102311820367/1152921504606846976)), (6663/576460752303423488), by norm_num⟩
  | 6 => ⟨((1597015762782869/1152921504606846976), (-818070386157/1152921504606846976)), (106619/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197230005813267/144115188075855872), (-178833670551/36028797018963968)), (11663/18014398509481984), by norm_num⟩
  | 4 => ⟨((747803713025109/18014398509481984), (-1072048944433/36028797018963968)), (34995/9007199254740992), by norm_num⟩
  | 3 => ⟨((186776687236723/1125899906842624), (-1338394939297/9007199254740992)), (175017/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237839600430929/4503599627370496), (-1335898867665/2251799813685248)), (21885/281474976710656), by norm_num⟩
  | 1 => ⟨((2230890814141231/2251799813685248), (-3995239246531/2251799813685248)), (525561/2251799813685248), by norm_num⟩
  | 0 => ⟨((552526720036949/562949953421312), (-7940786838153/2251799813685248)), (131551/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552526720036949/562949953421312), (-7940786838153/2251799813685248)), (501827241063976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((271144738083263/281474976710656), (-7793760137171/1125899906842624)), (518317/562949953421312), by norm_num⟩
  | 2 => ⟨((1044720542206421/1125899906842624), (-30030904711637/2251799813685248)), (4023061/2251799813685248), by norm_num⟩
  | 3 => ⟨((1938388201059077/2251799813685248), (-55731247267393/2251799813685248)), (3786645/1125899906842624), by norm_num⟩
  | 4 => ⟨((1667218739102279/2251799813685248), (-95948841879175/2251799813685248)), (13413311/2251799813685248), by norm_num⟩
  | 5 => ⟨((307577534969887/562949953421312), (-35519966340685/562949953421312)), (10502673/1125899906842624), by norm_num⟩
  | 6 => ⟨((82904591644447/281474976710656), (-77627814855541/1125899906842624)), (6400997/562949953421312), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1702061217/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/2097152), (-247003985/8388608)), (1/33554432), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437596779095325/4503599627370496), (517563649496693/2251799813685248)), (97875291/4503599627370496), by norm_num⟩
  | 1 => ⟨((335829185/2147483648), (-12412467/33554432)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-540496223/4294967296), (1278534079/4294967296)), (125/4294967296), by norm_num⟩
  | 3 => ⟨((579930075/8589934592), (-685907073/4294967296)), (17/1073741824), by norm_num⟩
  | 4 => ⟨((-466680725/17179869184), (68995303/1073741824)), (111/17179869184), by norm_num⟩
  | 5 => ⟨((300437461/34359738368), (-1421358803/68719476736)), (73/34359738368), by norm_num⟩
  | 6 => ⟨((-10073655/4294967296), (381264791/68719476736)), (5/8589934592), by norm_num⟩
  | 7 => ⟨((592929729/1099511627776), (-1402564593/1099511627776)), (149/1099511627776), by norm_num⟩
  | 8 => ⟨((-477141793/4398046511104), (1128670315/4398046511104)), (61/2199023255552), by norm_num⟩
  | 9 => ⟨((341302263/17592186044416), (-403672177/8796093022208)), (89/17592186044416), by norm_num⟩
  | 10 => ⟨((-439443841/140737488355328), (519748245/70368744177664)), (117/140737488355328), by norm_num⟩
  | 11 => ⟨((128592287/281474976710656), (-608365477/562949953421312)), (139/1125899906842624), by norm_num⟩
  | 12 => ⟨((-551896805/9007199254740992), (1305501951/9007199254740992)), (151/9007199254740992), by norm_num⟩
  | 13 => ⟨((34163217/4503599627370496), (-1292999591/72057594037927936)), (151/72057594037927936), by norm_num⟩
  | 14 => ⟨((-502706987/576460752303423488), (594572161/288230376151711744)), (141/576460752303423488), by norm_num⟩
  | 15 => ⟨((431507031/4611686018427387904), (-510361055/2305843009213693952)), (123/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-10851309/1152921504606846976), (821394431/36893488147419103232)), (101/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (2567130986765/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779823002069485/633825300114114700748351602688), (760377003041/158456325028528675187087900672)), (23125/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472731860596443/9903520314283042199192993792), (3421266155565/39614081257132168796771975168)), (52041/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945388048853441/1237940039285380274899124224), (3634579331703/2475880078570760549798248448)), (55305/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443110441300657/38685626227668133590597632), (3633998890125/154742504910672534362390528)), (55317/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550725692638083/9671406556917033397649408), (3406257284087/9671406556917033397649408)), (51873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314953449879103/151115727451828646838272), (2979858497359/604462909807314587353088)), (45403/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472364175027213/18889465931478580854784), (1210278497167/18889465931478580854784)), (73803/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298786931353413/4722366482869645213696), (3629824035367/4722366482869645213696)), (55375/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405790437684221/147573952589676412928), (4989364628967/590295810358705651712)), (76175/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912807097514547/36893488147419103232), (6234241001109/73786976294838206464)), (11909/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912530255985629/4611686018427387904), (876266575897/1152921504606846976)), (53627/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596304759824659/1152921504606846976), (3502948900195/576460752303423488)), (107345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196605014434917/144115188075855872), (95709337153/2251799813685248)), (47015/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494664222681209/36028797018963968), (4589286639291/18014398509481984)), (141251/36028797018963968), by norm_num⟩
  | 3 => ⟨((373256128876649/2251799813685248), (2864139438343/2251799813685248)), (176925/9007199254740992), by norm_num⟩
  | 2 => ⟨((558857950603105/1125899906842624), (11431582651155/2251799813685248)), (177467/2251799813685248), by norm_num⟩
  | 1 => ⟨((556801221985531/562949953421312), (8542491253585/562949953421312)), (133779/562949953421312), by norm_num⟩
  | 0 => ⟨((1101220115133833/1125899906842624), (16960339256203/562949953421312)), (33785/70368744177664), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101220115133833/1125899906842624), (16960339256203/562949953421312)), (128879547387576081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((134507419596267/140737488355328), (66354270516999/1125899906842624)), (1089995/1125899906842624), by norm_num⟩
  | 2 => ⟨((64032160133993/70368744177664), (63416946051363/562949953421312)), (1105983/562949953421312), by norm_num⟩
  | 3 => ⟨((917970812127817/1125899906842624), (230825437754997/1125899906842624)), (2261963/562949953421312), by norm_num⟩
  | 4 => ⟨((1402238377330565/2251799813685248), (752788105826999/2251799813685248)), (4615925/562949953421312), by norm_num⟩
  | 5 => ⟨((621539501903381/2251799813685248), (937550812086663/2251799813685248)), (35340409/2251799813685248), by norm_num⟩
  | 6 => ⟨((-437596779095325/4503599627370496), (517563649496693/2251799813685248)), (97875291/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-247003985/8388608)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-51854769/33554432), (-1099941105/33554432)), (1/33554432), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((196352495887449/4503599627370496), (-940005697380505/4503599627370496)), (71504271/4503599627370496), by norm_num⟩
  | 1 => ⟨((-335518307/4294967296), (1606239423/4294967296)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((75146013/1073741824), (-359749337/1073741824)), (57/2147483648), by norm_num⟩
  | 3 => ⟨((-89762387/2147483648), (1718891417/8589934592)), (69/4294967296), by norm_num⟩
  | 4 => ⟨((160832607/8589934592), (-1539919987/17179869184)), (63/8589934592), by norm_num⟩
  | 5 => ⟨((-230538677/34359738368), (137958311/4294967296)), (23/8589934592), by norm_num⟩
  | 6 => ⟨((275379905/137438953472), (-1318336587/137438953472)), (7/8589934592), by norm_num⟩
  | 7 => ⟨((-281951173/549755813888), (1349795465/549755813888)), (29/137438953472), by norm_num⟩
  | 8 => ⟨((126297171/1099511627776), (-1209254403/2199023255552)), (105/2199023255552), by norm_num⟩
  | 9 => ⟨((-201150357/8796093022208), (962974679/8796093022208)), (85/8796093022208), by norm_num⟩
  | 10 => ⟨((144165223/35184372088832), (-43135475/2199023255552)), (31/17592186044416), by norm_num⟩
  | 11 => ⟨((-23482673/35184372088832), (449677939/140737488355328)), (83/281474976710656), by norm_num⟩
  | 12 => ⟨((224401609/2251799813685248), (-537143137/1125899906842624)), (101/2251799813685248), by norm_num⟩
  | 13 => ⟨((-123714987/9007199254740992), (592265417/9007199254740992)), (113/18014398509481984), by norm_num⟩
  | 14 => ⟨((253334285/144115188075855872), (-1212796765/144115188075855872)), (117/144115188075855872), by norm_num⟩
  | 15 => ⟨((-121043761/576460752303423488), (579477357/576460752303423488)), (113/1152921504606846976), by norm_num⟩
  | 16 => ⟨((216881305/9223372036854775808), (-519142021/4611686018427387904)), (103/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-1777899318683/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889791456888047/316912650057057350374175801344), (-2105889127753/633825300114114700748351602688)), (46205/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890657529786411/39614081257132168796771975168), (-296099857951/4951760157141521099596496896)), (25993/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890489548612899/2475880078570760549798248448), (-314556453729/309485009821345068724781056)), (55243/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772155478189105/154742504910672534362390528), (-629001224247/38685626227668133590597632)), (13813/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550457576925023/9671406556917033397649408), (-294785002571/1208925819614629174706176)), (1619/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259579476518995/604462909807314587353088), (-2063020541311/604462909807314587353088)), (45341/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472269111681157/18889465931478580854784), (-104734966715/2361183241434822606848)), (2303/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649251098690519/2361183241434822606848), (-2512861136017/4722366482869645213696)), (55287/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811385491095657/295147905179352825856), (-431740009909/73786976294838206464)), (19011/147573952589676412928), by norm_num⟩
  | 8 => ⟨((57035213893005/2305843009213693952), (-4315504777805/73786976294838206464)), (23773/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912256884012329/4611686018427387904), (-2426168934483/4611686018427387904)), (107029/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595759920641887/1152921504606846976), (-2424541601069/576460752303423488)), (107093/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196130420428869/144115188075855872), (-529911061061/18014398509481984)), (93777/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493956605781653/36028797018963968), (-6351619571505/36028797018963968)), (17601/4503599627370496), by norm_num⟩
  | 3 => ⟨((746073729786545/4503599627370496), (-7926738725679/9007199254740992)), (176261/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116850014077265/2251799813685248), (-15815169388887/4503599627370496)), (44159/562949953421312), by norm_num⟩
  | 1 => ⟨((1112331433940993/1125899906842624), (-738348621063/70368744177664)), (531789/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197577540697185/2251799813685248), (-46872949862811/2251799813685248)), (1071125/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197577540697185/2251799813685248), (-46872949862811/2251799813685248)), (4086017617232512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2143685217758249/2251799813685248), (-45744271430665/1125899906842624)), (2135259/2251799813685248), by norm_num⟩
  | 2 => ⟨((2037044381779803/2251799813685248), (-174191893732423/2251799813685248)), (1059747/562949953421312), by norm_num⟩
  | 3 => ⟨((914647690363995/1125899906842624), (-315158227052607/2251799813685248)), (1040657/281474976710656), by norm_num⟩
  | 4 => ⟨((720978139828481/1125899906842624), (-512050392261327/2251799813685248)), (7928381/1125899906842624), by norm_num⟩
  | 5 => ⟨((806928882924737/2251799813685248), (-327895168182671/1125899906842624)), (6879879/562949953421312), by norm_num⟩
  | 6 => ⟨((196352495887449/4503599627370496), (-940005697380505/4503599627370496)), (71504271/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1099941105/33554432)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-56315997/33554432), (-298643121/8388608)), (1/33554432), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-423049329683431/4503599627370496), (726550954883101/4503599627370496)), (18701329/1125899906842624), by norm_num⟩
  | 1 => ⟨((785079941/4294967296), (-337076873/1073741824)), (141/4294967296), by norm_num⟩
  | 2 => ⟨((-763847513/4294967296), (163980327/536870912)), (35/1073741824), by norm_num⟩
  | 3 => ⟨((495459543/4294967296), (-850909287/4294967296)), (23/1073741824), by norm_num⟩
  | 4 => ⟨((-482059877/8589934592), (827896509/8589934592)), (91/8589934592), by norm_num⟩
  | 5 => ⟨((375218083/17179869184), (-80550611/2147483648)), (9/2147483648), by norm_num⟩
  | 6 => ⟨((-486760451/68719476736), (835969341/68719476736)), (95/68719476736), by norm_num⟩
  | 7 => ⟨((270626315/137438953472), (-464777493/137438953472)), (107/274877906944), by norm_num⟩
  | 8 => ⟨((-526614493/1099511627776), (904415241/1099511627776)), (53/549755813888), by norm_num⟩
  | 9 => ⟨((227720997/2199023255552), (-48886411/274877906944)), (93/4398046511104), by norm_num⟩
  | 10 => ⟨((-708999359/35184372088832), (1217645611/35184372088832)), (147/35184372088832), by norm_num⟩
  | 11 => ⟨((501690563/140737488355328), (-26925329/4398046511104)), (105/140737488355328), by norm_num⟩
  | 12 => ⟨((-650829839/1125899906842624), (1117744447/1125899906842624)), (69/562949953421312), by norm_num⟩
  | 13 => ⟨((389678889/4503599627370496), (-669240081/4503599627370496)), (167/9007199254740992), by norm_num⟩
  | 14 => ⟨((-433302917/36028797018963968), (744160609/36028797018963968)), (47/18014398509481984), by norm_num⟩
  | 15 => ⟨((224844945/144115188075855872), (-386151915/144115188075855872)), (99/288230376151711744), by norm_num⟩
  | 16 => ⟨((-109382015/576460752303423488), (751416931/2305843009213693952)), (49/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (2732980272747/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779374567575169/633825300114114700748351602688), (3236455303177/633825300114114700748351602688)), (11565/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945211494018033/19807040628566084398385987584), (3640462845123/39614081257132168796771975168)), (13013/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890240150655387/2475880078570760549798248448), (966832052573/618970019642690137449562112)), (27659/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771905858370199/154742504910672534362390528), (3866581759195/154742504910672534362390528)), (55331/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550223322760179/9671406556917033397649408), (3624127393617/9671406556917033397649408)), (25943/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259374268701083/604462909807314587353088), (3170318574667/604462909807314587353088)), (45415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472185635735755/18889465931478580854784), (5150281241893/75557863725914323419136)), (36913/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324562845985941/1180591620717411303424), (3861410530537/4722366482869645213696)), (55393/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622425487753803/590295810358705651712), (2653663385215/295147905179352825856)), (76203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824694038707617/73786976294838206464), (3315495087023/36893488147419103232)), (47655/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824025573737037/9223372036854775808), (7455508807981/9223372036854775808)), (107301/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398817529868579/288230376151711744), (7450066776457/1152921504606846976)), (107399/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597850020206829/72057594037927936), (6512688746051/144115188075855872)), (23521/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493307437128017/36028797018963968), (4878400132323/18014398509481984)), (141345/36028797018963968), by norm_num⟩
  | 3 => ⟨((186416215272207/1125899906842624), (12174607507297/9007199254740992)), (88533/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116022903799725/2251799813685248), (12142547663183/2251799813685248)), (44411/562949953421312), by norm_num⟩
  | 1 => ⟨((1111067482973337/1125899906842624), (18133774967115/1125899906842624)), (267913/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096168603769465/1125899906842624), (35947984018761/1125899906842624)), (541635/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096168603769465/1125899906842624), (35947984018761/1125899906842624)), (2066173557761764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1066074651077007/1125899906842624), (1093709885163/17592186044416)), (272313/281474976710656), by norm_num⟩
  | 2 => ⟨((502538242615507/562949953421312), (132556167978307/1125899906842624)), (2198187/1125899906842624), by norm_num⟩
  | 3 => ⟨((881612652654727/1125899906842624), (118331200311531/562949953421312)), (1110547/281474976710656), by norm_num⟩
  | 4 => ⟨((1281165000670075/2251799813685248), (370627203233435/1125899906842624)), (17648419/2251799813685248), by norm_num⟩
  | 5 => ⟨((484912405267669/2251799813685248), (421737845605207/1125899906842624)), (15850657/1125899906842624), by norm_num⟩
  | 6 => ⟨((-423049329683431/4503599627370496), (726550954883101/4503599627370496)), (18701329/1125899906842624), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-298643121/8388608)), (1/33554432), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-60180489/33554432), (-1276545913/33554432)), (1/16777216), by norm_num⟩
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
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((44071867091905/281474976710656), (-506697203612827/9007199254740992)), (125089247/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1398389759/4294967296), (502418143/4294967296)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((726967439/2147483648), (-522374579/4294967296)), (135/4294967296), by norm_num⟩
  | 3 => ⟨((-1007790861/4294967296), (362082467/4294967296)), (3/134217728), by norm_num⟩
  | 4 => ⟨((1047821091/8589934592), (-188232331/4294967296)), (51/4294967296), by norm_num⟩
  | 5 => ⟨((-435776541/8589934592), (313134503/17179869184)), (87/17179869184), by norm_num⟩
  | 6 => ⟨((1208229123/68719476736), (-108524149/17179869184)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((-717840523/137438953472), (515816283/274877906944)), (149/274877906944), by norm_num⟩
  | 8 => ⟨((373176851/274877906944), (-536304903/1099511627776)), (79/549755813888), by norm_num⟩
  | 9 => ⟨((-1379554571/4398046511104), (495650975/4398046511104)), (149/4398046511104), by norm_num⟩
  | 10 => ⟨((573740617/8796093022208), (-412270891/17592186044416)), (63/8796093022208), by norm_num⟩
  | 11 => ⟨((-867680053/70368744177664), (77935747/17592186044416)), (97/70368744177664), by norm_num⟩
  | 12 => ⟨((1202859965/562949953421312), (-216083773/281474976710656)), (137/562949953421312), by norm_num⟩
  | 13 => ⟨((-384811843/1125899906842624), (553025937/4503599627370496)), (89/2251799813685248), by norm_num⟩
  | 14 => ⟨((457253561/9007199254740992), (-328567173/18014398509481984)), (27/4503599627370496), by norm_num⟩
  | 15 => ⟨((-1014220853/144115188075855872), (364392655/144115188075855872)), (61/72057594037927936), by norm_num⟩
  | 16 => ⟨((1054506487/1152921504606846976), (-94716653/288230376151711744)), (129/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-449298111623/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444800593084589/158456325028528675187087900672), (-531967631769/633825300114114700748351602688)), (92253/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890229612670293/39614081257132168796771975168), (-149592325613/9903520314283042199192993792)), (25947/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945017564003843/1237940039285380274899124224), (-158912768489/618970019642690137449562112)), (55139/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442925332238489/38685626227668133590597632), (-635520265963/154742504910672534362390528)), (110283/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775016050116211/4835703278458516698824704), (-297830651751/4835703278458516698824704)), (103395/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629603736249277/302231454903657293676544), (-130266184273/151115727451828646838272)), (90475/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944236240038119/37778931862957161709568), (-846469843761/75557863725914323419136)), (147031/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298049694518443/4722366482869645213696), (-634624663019/4722366482869645213696)), (110281/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622149557439901/590295810358705651712), (-218059758893/147573952589676412928)), (4739/18446744073709551616), by norm_num⟩
  | 8 => ⟨((456087803190193/18446744073709551616), (-136218034405/9223372036854775808)), (189579/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823642760811095/9223372036854775808), (-1225200324627/9223372036854775808)), (106651/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594890884453563/1152921504606846976), (-153031070153/144115188075855872)), (213335/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195372228147691/144115188075855872), (-535073871749/72057594037927936)), (11669/9007199254740992), by norm_num⟩
  | 4 => ⟨((93301483661613/2251799813685248), (-1603084583295/36028797018963968)), (280129/36028797018963968), by norm_num⟩
  | 3 => ⟨((372684773944557/2251799813685248), (-250015182333/1125899906842624)), (350289/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115453196747643/2251799813685248), (-1994531107121/2251799813685248)), (175241/1125899906842624), by norm_num⟩
  | 1 => ⟨((555132477970347/562949953421312), (-2977859395903/1125899906842624)), (4111/8796093022208), by norm_num⟩
  | 0 => ⟨((1094770099326829/1125899906842624), (-11800401629979/2251799813685248)), (1054371/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094770099326829/1125899906842624), (-11800401629979/2251799813685248)), (4022106174949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2128940149522439/2251799813685248), (-22948268822185/2251799813685248)), (2061489/1125899906842624), by norm_num⟩
  | 2 => ⟨((2012549921029589/2251799813685248), (-43392392663563/2251799813685248)), (985011/281474976710656), by norm_num⟩
  | 3 => ⟨((898941873138689/1125899906842624), (-77564049785951/2251799813685248)), (14389385/2251799813685248), by norm_num⟩
  | 4 => ⟨((358199001938473/562949953421312), (-123857497063549/2251799813685248)), (749027/70368744177664), by norm_num⟩
  | 5 => ⟨((904860062547927/2251799813685248), (-78809193536885/1125899906842624)), (66278035/4503599627370496), by norm_num⟩
  | 6 => ⟨((44071867091905/281474976710656), (-506697203612827/9007199254740992)), (125089247/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1276545913/33554432)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile008Terms0
