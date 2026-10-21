/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand58.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand58.Tile001Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (4659/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4659/320))
  have he : value ((15/16), (4659/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/8388608), (-1354497089/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-595794211612839/9007199254740992), (-610610903291741/18014398509481984)), (15113895/1125899906842624), by norm_num⟩
  | 1 => ⟨((196920909/1073741824), (201818097/2147483648)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((-1091961383/4294967296), (-139889645/1073741824)), (113/2147483648), by norm_num⟩
  | 3 => ⟨((1009186605/4294967296), (32321371/268435456)), (211/4294967296), by norm_num⟩
  | 4 => ⟨((-349757425/2147483648), (-358455475/4294967296)), (295/8589934592), by norm_num⟩
  | 5 => ⟨((387893397/4294967296), (397539843/8589934592)), (165/8589934592), by norm_num⟩
  | 6 => ⟨((-716979239/17179869184), (-91851207/4294967296)), (155/17179869184), by norm_num⟩
  | 7 => ⟨((283984079/17179869184), (582092847/68719476736)), (31/8589934592), by norm_num⟩
  | 8 => ⟨((-787371055/137438953472), (-25217251/8589934592)), (87/68719476736), by norm_num⟩
  | 9 => ⟨((970247159/549755813888), (497188023/549755813888)), (27/68719476736), by norm_num⟩
  | 10 => ⟨((-269009633/549755813888), (-275699581/1099511627776)), (121/1099511627776), by norm_num⟩
  | 11 => ⟨((67804825/549755813888), (555928399/8796093022208)), (123/4398046511104), by norm_num⟩
  | 12 => ⟨((-501319715/17592186044416), (-513786937/35184372088832)), (229/35184372088832), by norm_num⟩
  | 13 => ⟨((855355931/140737488355328), (438313805/140737488355328)), (197/140737488355328), by norm_num⟩
  | 14 => ⟨((-1355171547/1125899906842624), (-694436521/1125899906842624)), (315/1125899906842624), by norm_num⟩
  | 15 => ⟨((125244445/562949953421312), (256718249/2251799813685248)), (235/4503599627370496), by norm_num⟩
  | 16 => ⟨((-1389005343/36028797018963968), (-355887061/18014398509481984)), (41/4503599627370496), by norm_num⟩
  | _ => zero

private def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580589886122463/10141204801825835211973625643008), (-3475429206139/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888975771849817/316912650057057350374175801344), (-2054714128393/316912650057057350374175801344)), (92605/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472205552222269/9903520314283042199192993792), (-4622047630373/39614081257132168796771975168)), (104207/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888539441284487/2475880078570760549798248448), (-4909621557715/2475880078570760549798248448)), (55375/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885102641322929/77371252455336267181195264), (-613519353803/19342813113834066795298816)), (1731/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((387157293812479/2417851639229258349412352), (-4599837160953/9671406556917033397649408)), (12987/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257979532121971/604462909807314587353088), (-502912497311/75557863725914323419136)), (45473/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471619090932325/18889465931478580854784), (-1633735762477/18889465931478580854784)), (147853/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296551984348361/4722366482869645213696), (-4898653766617/4722366482869645213696)), (110949/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620089195920615/590295810358705651712), (-6731501271785/590295810358705651712)), (152651/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455443562410625/18446744073709551616), (-1051019784805/9223372036854775808)), (190959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820741605599391/9223372036854775808), (-590664565273/576460752303423488)), (215027/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591987148933231/1152921504606846976), (-4719979755001/576460752303423488)), (53819/288230376151711744), by norm_num⟩
  | 5 => ⟨((298207142378793/36028797018963968), (-1030995935917/18014398509481984)), (188647/144115188075855872), by norm_num⟩
  | 4 => ⟨((744501251228087/18014398509481984), (-12347983671139/36028797018963968)), (141765/18014398509481984), by norm_num⟩
  | 3 => ⟨((742976281476215/4503599627370496), (-962068514583/562949953421312)), (355395/9007199254740992), by norm_num⟩
  | 2 => ⟨((555325912646941/1125899906842624), (-7665195481607/1125899906842624)), (356873/2251799813685248), by norm_num⟩
  | 1 => ⟨((2206052600520451/2251799813685248), (-45678485009315/2251799813685248)), (1078025/2251799813685248), by norm_num⟩
  | 0 => ⟨((2160298733373361/2251799813685248), (-45055625132621/1125899906842624)), (2185813/2251799813685248), by norm_num⟩
  | _ => zero

private def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2160298733373361/2251799813685248), (-45055625132621/1125899906842624)), (8338214882857512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1034454872870279/1125899906842624), (-86449611829439/1125899906842624)), (4368929/2251799813685248), by norm_num⟩
  | 2 => ⟨((1887598253026831/2251799813685248), (-317712868333001/2251799813685248)), (8699091/2251799813685248), by norm_num⟩
  | 3 => ⟨((1537474902113783/2251799813685248), (-532653259481389/2251799813685248)), (17038995/2251799813685248), by norm_num⟩
  | 4 => ⟨((923754219692103/2251799813685248), (-363682869589315/1125899906842624)), (31328633/2251799813685248), by norm_num⟩
  | 5 => ⟨((288001569142519/4503599627370496), (-1193546898338349/4503599627370496)), (11485775/562949953421312), by norm_num⟩
  | 6 => ⟨((-595794211612839/9007199254740992), (-610610903291741/18014398509481984)), (15113895/1125899906842624), by norm_num⟩
  | _ => zero

private def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/8388608), (-1354497089/33554432)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-89125185/33554432), (-692057065/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1160561231357563/18014398509481984), (503189997775575/18014398509481984)), (226776979/18014398509481984), by norm_num⟩
  | 1 => ⟨((391974159/2147483648), (-84975041/1073741824)), (155/4294967296), by norm_num⟩
  | 2 => ⟨((-555273209/2147483648), (60188105/536870912)), (221/4294967296), by norm_num⟩
  | 3 => ⟨((1048804977/4294967296), (-454735313/4294967296)), (211/4294967296), by norm_num⟩
  | 4 => ⟨((-725461/4194304), (322090539/4294967296)), (301/8589934592), by norm_num⟩
  | 5 => ⟨((420943009/4294967296), (-365020485/8589934592)), (43/2147483648), by norm_num⟩
  | 6 => ⟨((-198770225/4294967296), (172363485/8589934592)), (41/4294967296), by norm_num⟩
  | 7 => ⟨((1287219323/68719476736), (-34881609/4294967296)), (67/17179869184), by norm_num⟩
  | 8 => ⟨((-911741741/137438953472), (3088345/1073741824)), (3/2147483648), by norm_num⟩
  | 9 => ⟨((71754413/34359738368), (-124443595/137438953472)), (61/137438953472), by norm_num⟩
  | 10 => ⟨((-1301091587/2199023255552), (282060203/1099511627776)), (279/2199023255552), by norm_num⟩
  | 11 => ⟨((1340461835/8796093022208), (-290595175/4398046511104)), (289/8796093022208), by norm_num⟩
  | 12 => ⟨((-1265938119/35184372088832), (17152461/1099511627776)), (275/35184372088832), by norm_num⟩
  | 13 => ⟨((551795811/70368744177664), (-478489417/140737488355328)), (121/70368744177664), by norm_num⟩
  | 14 => ⟨((-223336465/140737488355328), (96833043/140737488355328)), (197/562949953421312), by norm_num⟩
  | 15 => ⟨((674943843/2251799813685248), (-292638581/2251799813685248)), (75/1125899906842624), by norm_num⟩
  | 16 => ⟨((-956129951/18014398509481984), (207276883/9007199254740992)), (215/18014398509481984), by norm_num⟩
  | _ => zero

private def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790257925728623/5070602400912917605986812821504), (444920300231/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888931782420209/316912650057057350374175801344), (4208277703877/633825300114114700748351602688)), (92615/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944361616121935/19807040628566084398385987584), (1183301211275/9903520314283042199192993792)), (52109/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944217137179953/1237940039285380274899124224), (2513832757341/1237940039285380274899124224)), (110763/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221262513875059/19342813113834066795298816), (5026130651269/154742504910672534362390528)), (55399/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387132642962079/2417851639229258349412352), (4710367125513/9671406556917033397649408)), (51955/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78618328074833/37778931862957161709568), (1029985340115/151115727451828646838272)), (45479/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886336144774819/75557863725914323419136), (1672962432113/18889465931478580854784)), (36969/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((20256981439949/73786976294838206464), (5016215219011/4722366482869645213696)), (13871/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809972285669351/295147905179352825856), (6892955735923/590295810358705651712)), (152679/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821593449935931/73786976294838206464), (4304843885895/36893488147419103232)), (190997/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910269090118101/4611686018427387904), (9676957262935/9223372036854775808)), (215075/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795891846028415/576460752303423488), (4832894335003/576460752303423488)), (107665/576460752303423488), by norm_num⟩
  | 5 => ⟨((596325255061855/72057594037927936), (4222505887111/72057594037927936)), (188701/144115188075855872), by norm_num⟩
  | 4 => ⟨((744367673091663/18014398509481984), (6321219713823/18014398509481984)), (283625/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485618504663537/9007199254740992), (15759226261551/9007199254740992)), (177769/4503599627370496), by norm_num⟩
  | 2 => ⟨((555158803398765/1125899906842624), (15693619517163/2251799813685248)), (357051/2251799813685248), by norm_num⟩
  | 1 => ⟨((551262302034091/562949953421312), (11688429879101/562949953421312)), (134843/281474976710656), by norm_num⟩
  | 0 => ⟨((2158289383023917/2251799813685248), (92204252180589/2251799813685248)), (2187983/2251799813685248), by norm_num⟩
  | _ => zero

private def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2158289383023917/2251799813685248), (92204252180589/2251799813685248)), (8346492775923918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258110834747337/281474976710656), (176750577330709/2251799813685248)), (1093357/562949953421312), by norm_num⟩
  | 2 => ⟨((939807393309157/1125899906842624), (162079200041287/1125899906842624)), (4353691/1125899906842624), by norm_num⟩
  | 3 => ⟨((1522281446555469/2251799813685248), (270580412298989/1125899906842624)), (17043341/2251799813685248), by norm_num⟩
  | 4 => ⟨((899052283486167/2251799813685248), (731680567590019/2251799813685248)), (31235415/2251799813685248), by norm_num⟩
  | 5 => ⟨((242418134857337/4503599627370496), (1168521430859679/4503599627370496)), (90481611/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1160561231357563/18014398509481984), (503189997775575/18014398509481984)), (226776979/18014398509481984), by norm_num⟩
  | _ => zero

private def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-89125185/33554432), (-692057065/16777216)), (1/16777216), by norm_num⟩, -7, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-45461617/16777216), (-353009455/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-48492324825141/2251799813685248), (1134455591063525/18014398509481984)), (52683911/4503599627370496), by norm_num⟩
  | 1 => ⟨((534671197/8589934592), (-195443535/1073741824)), (293/8589934592), by norm_num⟩
  | 2 => ⟨((-6036713/67108864), (282452237/1073741824)), (213/4294967296), by norm_num⟩
  | 3 => ⟨((372231355/4294967296), (-1088522625/4294967296)), (207/4294967296), by norm_num⟩
  | 4 => ⟨((-268971749/4294967296), (1573117527/8589934592)), (301/8589934592), by norm_num⟩
  | 5 => ⟨((310971339/8589934592), (-909378895/8589934592)), (11/536870912), by norm_num⟩
  | 6 => ⟨((-37450949/2147483648), (219036923/4294967296)), (171/17179869184), by norm_num⟩
  | 7 => ⟨((61855523/8589934592), (-723540727/34359738368)), (285/68719476736), by norm_num⟩
  | 8 => ⟨((-178785457/68719476736), (522825421/68719476736)), (13/8589934592), by norm_num⟩
  | 9 => ⟨((229669527/274877906944), (-20988331/8589934592)), (269/549755813888), by norm_num⟩
  | 10 => ⟨((-132766063/549755813888), (1553000427/2199023255552)), (313/2199023255552), by norm_num⟩
  | 11 => ⟨((279086021/4398046511104), (-816136105/4398046511104)), (83/2199023255552), by norm_num⟩
  | 12 => ⟨((-268887451/17592186044416), (1572624499/35184372088832)), (161/17592186044416), by norm_num⟩
  | 13 => ⟨((29891719/8796093022208), (-1398605981/140737488355328)), (289/140737488355328), by norm_num⟩
  | 14 => ⟨((-197481555/281474976710656), (577498747/281474976710656)), (241/562949953421312), by norm_num⟩
  | 15 => ⟨((152212029/1125899906842624), (-445116285/1125899906842624)), (187/2251799813685248), by norm_num⟩
  | 16 => ⟨((-219974675/9007199254740992), (1286551539/18014398509481984)), (17/1125899906842624), by norm_num⟩
  | _ => zero

private def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580446049662487/10141204801825835211973625643008), (618835238777/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888892972649207/316912650057057350374175801344), (1463183409247/316912650057057350374175801344)), (92489/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944318100379791/19807040628566084398385987584), (102855855037/1237940039285380274899124224)), (26017/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((7376336679027/9671406556917033397649408), (1748066052437/1237940039285380274899124224)), (55297/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221251057594857/19342813113834066795298816), (3495044694799/154742504910672534362390528)), (110619/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548445110819927/9671406556917033397649408), (3275449429291/9671406556917033397649408)), (103731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257818931468813/604462909807314587353088), (1432431864855/302231454903657293676544)), (45395/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943108120685693/37778931862957161709568), (2326619896227/37778931862957161709568)), (147581/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296357638793619/4722366482869645213696), (3488037505091/4722366482869645213696)), (110729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101238948870283/36893488147419103232), (2396489156879/295147905179352825856)), (595/2305843009213693952), by norm_num⟩
  | 8 => ⟨((28460055411167/1152921504606846976), (374163509327/4611686018427387904)), (190503/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820372054703411/9223372036854775808), (3364306998479/4611686018427387904)), (214457/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591620704780281/1152921504606846976), (840088772399/144115188075855872)), (107317/576460752303423488), by norm_num⟩
  | 5 => ⟨((37265981795761/4503599627370496), (1467935029165/36028797018963968)), (188005/144115188075855872), by norm_num⟩
  | 4 => ⟨((372133431580225/9007199254740992), (8789873832107/36028797018963968)), (282407/36028797018963968), by norm_num⟩
  | 3 => ⟨((371344677753017/2251799813685248), (5478181328077/4503599627370496)), (176855/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110096055581767/2251799813685248), (21820021934485/4503599627370496)), (709525/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204475038709549/2251799813685248), (32499097261465/2251799813685248)), (1069573/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157498632051495/2251799813685248), (64079376552013/2251799813685248)), (540097/562949953421312), by norm_num⟩
  | _ => zero

private def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2157498632051495/2251799813685248), (64079376552013/2251799813685248)), (2060306551219749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1032661552003939/1125899906842624), (7674481453317/140737488355328)), (4262787/2251799813685248), by norm_num⟩
  | 2 => ⟨((943796534605067/1125899906842624), (112623040541959/1125899906842624)), (1035557/281474976710656), by norm_num⟩
  | 3 => ⟨((779881003751031/1125899906842624), (377629431299151/2251799813685248)), (7773215/1125899906842624), by norm_num⟩
  | 4 => ⟨((1017076881676867/2251799813685248), (2043546026339/8796093022208)), (26751509/2251799813685248), by norm_num⟩
  | 5 => ⟨((168923049027125/1125899906842624), (945166639226965/4503599627370496)), (36595913/2251799813685248), by norm_num⟩
  | 6 => ⟨((-48492324825141/2251799813685248), (1134455591063525/18014398509481984)), (52683911/4503599627370496), by norm_num⟩
  | _ => zero

private def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45461617/16777216), (-353009455/8388608)), (1/16777216), by norm_num⟩, -7, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-92624041/33554432), (-1438451363/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((503605069859453/18014398509481984), (255597877205313/4503599627370496)), (155779529/18014398509481984), by norm_num⟩
  | 1 => ⟨((-176767635/2147483648), (-1435455995/8589934592)), (221/8589934592), by norm_num⟩
  | 2 => ⟨((520481515/4294967296), (528326573/2147483648)), (165/4294967296), by norm_num⟩
  | 3 => ⟨((-127710505/1073741824), (-518541785/2147483648)), (41/1073741824), by norm_num⟩
  | 4 => ⟨((376035789/4294967296), (381703661/2147483648)), (61/2147483648), by norm_num⟩
  | 5 => ⟨((-221442887/4294967296), (-449561255/4294967296)), (145/8589934592), by norm_num⟩
  | 6 => ⟨((434683379/17179869184), (882470455/17179869184)), (9/1073741824), by norm_num⟩
  | 7 => ⟨((-182842669/17179869184), (-371197201/17179869184)), (123/34359738368), by norm_num⟩
  | 8 => ⟨((269184541/68719476736), (273241877/34359738368)), (183/137438953472), by norm_num⟩
  | 9 => ⟨((-704531071/549755813888), (-178787563/68719476736)), (121/274877906944), by norm_num⟩
  | 10 => ⟨((414889749/1099511627776), (842286511/1099511627776)), (9/68719476736), by norm_num⟩
  | 11 => ⟨((-444224563/4398046511104), (-901840449/4398046511104)), (39/1099511627776), by norm_num⟩
  | 12 => ⟨((435997373/17592186044416), (885138057/17592186044416)), (155/17592186044416), by norm_num⟩
  | 13 => ⟨((-197502717/35184372088832), (-801918461/70368744177664)), (71/35184372088832), by norm_num⟩
  | 14 => ⟨((166152771/140737488355328), (168657141/70368744177664)), (241/562949953421312), by norm_num⟩
  | 15 => ⟨((-32615113/140737488355328), (-1059414741/2251799813685248)), (3/35184372088832), by norm_num⟩
  | 16 => ⟨((48016605/1125899906842624), (779845515/9007199254740992)), (143/9007199254740992), by norm_num⟩
  | _ => zero

private def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580380022885053/10141204801825835211973625643008), (1449944702091/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777710908716111/633825300114114700748351602688), (856996030075/316912650057057350374175801344)), (92369/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944275985054491/19807040628566084398385987584), (963891192255/19807040628566084398385987584)), (103927/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944126470935733/1237940039285380274899124224), (2047692237183/2475880078570760549798248448)), (55217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884959745244849/77371252455336267181195264), (2047043945549/154742504910672534362390528)), (110449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548361996008355/9671406556917033397649408), (1918415164009/9671406556917033397649408)), (103561/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157218312570665/75557863725914323419136), (1677925042959/604462909807314587353088)), (90631/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886099092896639/75557863725914323419136), (1362669214519/37778931862957161709568)), (147303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296270259663249/4722366482869645213696), (2042875933495/4722366482869645213696)), (55251/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50615744318971/18446744073709551616), (350890352593/73786976294838206464)), (37995/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821295513747559/73786976294838206464), (109567446759/2305843009213693952)), (47509/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455051781688171/2305843009213693952), (3940656886753/9223372036854775808)), (213873/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591457783311451/1152921504606846976), (491993515899/144115188075855872)), (106989/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192371112462649/144115188075855872), (3438664448173/144115188075855872)), (46837/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488327756394033/36028797018963968), (1286858574883/9007199254740992)), (281257/36028797018963968), by norm_num⟩
  | 3 => ⟨((92820566763325/562949953421312), (3207924524517/4503599627370496)), (351983/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109858075108657/2251799813685248), (12776527587457/4503599627370496)), (88151/562949953421312), by norm_num⟩
  | 1 => ⟨((2203818941152905/2251799813685248), (9513713473933/1125899906842624)), (1060927/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078207510297039/1125899906842624), (37508754962391/2251799813685248)), (2134399/2251799813685248), by norm_num⟩
  | _ => zero

private def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1078207510297039/1125899906842624), (37508754962391/2251799813685248)), (8142086037642668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((129027867122459/140737488355328), (8979977051369/281474976710656)), (2079541/1125899906842624), by norm_num⟩
  | 2 => ⟨((945194102383207/1125899906842624), (65862609844019/1125899906842624)), (7891455/2251799813685248), by norm_num⟩
  | 3 => ⟨((789638583679891/1125899906842624), (55291727100955/562949953421312)), (14173035/2251799813685248), by norm_num⟩
  | 4 => ⟨((1085887633132569/2251799813685248), (310226376692051/2251799813685248)), (11332161/1125899906842624), by norm_num⟩
  | 5 => ⟨((961818666484837/4503599627370496), (598403079837027/4503599627370496)), (14051861/1125899906842624), by norm_num⟩
  | 6 => ⟨((503605069859453/18014398509481984), (255597877205313/4503599627370496)), (155779529/18014398509481984), by norm_num⟩
  | _ => zero

private def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-92624041/33554432), (-1438451363/33554432)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-94237589/33554432), (-365877439/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((507062091995191/9007199254740992), (389039660891955/18014398509481984)), (93708731/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1448652529/8589934592), (-555733999/8589934592)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((135617973/536870912), (416207569/4294967296)), (13/536870912), by norm_num⟩
  | 3 => ⟨((-541700185/2147483648), (-207807741/2147483648)), (53/2147483648), by norm_num⟩
  | 4 => ⟨((811394363/4294967296), (155634089/2147483648)), (81/4294967296), by norm_num⟩
  | 5 => ⟨((-60768007/536870912), (-372990451/8589934592)), (99/8589934592), by norm_num⟩
  | 6 => ⟨((970904959/17179869184), (93114961/4294967296)), (25/4294967296), by norm_num⟩
  | 7 => ⟨((-831020377/34359738368), (-19924821/2147483648)), (87/34359738368), by norm_num⟩
  | 8 => ⟨((622378641/68719476736), (477515435/137438953472)), (33/34359738368), by norm_num⟩
  | 9 => ⟨((-828657681/274877906944), (-79472689/68719476736)), (45/137438953472), by norm_num⟩
  | 10 => ⟨((31030457/34359738368), (380926239/1099511627776)), (55/549755813888), by norm_num⟩
  | 11 => ⟨((-1081704047/4398046511104), (-207482369/2199023255552)), (61/2199023255552), by norm_num⟩
  | 12 => ⟨((1080165241/17592186044416), (414374419/17592186044416)), (31/4398046511104), by norm_num⟩
  | 13 => ⟨((-124457149/8796093022208), (-381955329/70368744177664)), (29/17592186044416), by norm_num⟩
  | 14 => ⟨((852206395/281474976710656), (326924545/281474976710656)), (101/281474976710656), by norm_num⟩
  | 15 => ⟨((-1361590507/2251799813685248), (-32645947/140737488355328)), (41/562949953421312), by norm_num⟩
  | 16 => ⟨((254935039/2251799813685248), (97798517/2251799813685248)), (125/9007199254740992), by norm_num⟩
  | _ => zero

private def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580317383576375/10141204801825835211973625643008), (477156527145/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777638270619713/633825300114114700748351602688), (70500750701/79228162514264337593543950336)), (2883/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1888470348649365/39614081257132168796771975168), (317176938747/19807040628566084398385987584)), (6487/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472041586783873/618970019642690137449562112), (673808036527/2475880078570760549798248448)), (110283/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442458259916693/38685626227668133590597632), (673591078493/154742504910672534362390528)), (6893/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548281101153085/9671406556917033397649408), (315630608247/4835703278458516698824704)), (12925/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628837935113539/302231454903657293676544), (552123255515/604462909807314587353088)), (5655/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((471496151139087/18889465931478580854784), (896768696045/75557863725914323419136)), (147039/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296184643344339/4722366482869645213696), (672199112043/4722366482869645213696)), (6893/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619586501394115/590295810358705651712), (461830463975/295147905179352825856)), (151659/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910574737629527/36893488147419103232), (1153657652861/73786976294838206464)), (189593/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910021833662947/4611686018427387904), (324150790407/2305843009213693952)), (26665/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591295364012375/1152921504606846976), (647513955665/576460752303423488)), (53339/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192230162681989/144115188075855872), (1131379836457/144115188075855872)), (93363/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488118658357695/36028797018963968), (211692124903/4503599627370496)), (35021/4503599627370496), by norm_num⟩
  | 3 => ⟨((1484871750275119/9007199254740992), (2110753336219/9007199254740992)), (350349/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109606805189381/2251799813685248), (4203060432397/4503599627370496)), (701121/4503599627370496), by norm_num⟩
  | 1 => ⟨((550773783817545/562949953421312), (391167229417/140737488355328)), (526375/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155086015197413/2251799813685248), (12334890200099/2251799813685248)), (2109845/2251799813685248), by norm_num⟩
  | _ => zero

private def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2155086015197413/2251799813685248), (12334890200099/2251799813685248)), (8048419960982512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((515614615823969/562949953421312), (11805112163023/1125899906842624)), (1015393/562949953421312), by norm_num⟩
  | 2 => ⟨((944395111030629/1125899906842624), (43249943166017/2251799813685248)), (7525287/2251799813685248), by norm_num⟩
  | 3 => ⟨((791735109777559/1125899906842624), (72555357061679/2251799813685248)), (6456683/1125899906842624), by norm_num⟩
  | 4 => ⟨((1111161676616661/2251799813685248), (51021074998817/1125899906842624)), (2374197/281474976710656), by norm_num⟩
  | 5 => ⟨((1087368125501173/4503599627370496), (100706400087471/2251799813685248)), (10233183/1125899906842624), by norm_num⟩
  | 6 => ⟨((507062091995191/9007199254740992), (389039660891955/18014398509481984)), (93708731/18014398509481984), by norm_num⟩
  | _ => zero

private def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-94237589/33554432), (-365877439/8388608)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-95772395/33554432), (-1487345291/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((30525458873195/562949953421312), (-174994645245545/9007199254740992)), (88016969/18014398509481984), by norm_num⟩
  | 1 => ⟨((-177260293/1073741824), (992371/16777216)), (65/4294967296), by norm_num⟩
  | 2 => ⟨((1079345879/4294967296), (-386725859/4294967296)), (101/4294967296), by norm_num⟩
  | 3 => ⟨((-1095364249/4294967296), (392465185/4294967296)), (13/536870912), by norm_num⟩
  | 4 => ⟨((833715259/4294967296), (-298717265/4294967296)), (81/4294967296), by norm_num⟩
  | 5 => ⟨((-1015305925/8589934592), (181890283/4294967296)), (101/8589934592), by norm_num⟩
  | 6 => ⟨((515186945/8589934592), (-369179365/17179869184)), (13/2147483648), by norm_num⟩
  | 7 => ⟨((-448142347/17179869184), (160567837/17179869184)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((1364379431/137438953472), (-488852383/137438953472)), (71/68719476736), by norm_num⟩
  | 9 => ⟨((-923085287/274877906944), (330738233/274877906944)), (49/137438953472), by norm_num⟩
  | 10 => ⟨((1124141547/1099511627776), (-402775989/1099511627776)), (61/549755813888), by norm_num⟩
  | 11 => ⟨((-1244536059/4398046511104), (222956461/2199023255552)), (137/4398046511104), by norm_num⟩
  | 12 => ⟨((631502993/8796093022208), (-56566329/2199023255552)), (141/17592186044416), by norm_num⟩
  | 13 => ⟨((-591576933/35184372088832), (52989987/8796093022208)), (67/35184372088832), by norm_num⟩
  | 14 => ⟨((1029182427/281474976710656), (-368752467/281474976710656)), (119/281474976710656), by norm_num⟩
  | 15 => ⟨((-835565065/1125899906842624), (299380043/1125899906842624)), (99/1125899906842624), by norm_num⟩
  | 16 => ⟨((635974147/4503599627370496), (-455734629/9007199254740992)), (153/9007199254740992), by norm_num⟩
  | _ => zero

private def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580257801099253/10141204801825835211973625643008), (-448159257929/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777567866035885/633825300114114700748351602688), (-66211346395/79228162514264337593543950336)), (23063/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944195581915553/19807040628566084398385987584), (-595756365867/39614081257132168796771975168)), (25947/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888082239030269/2475880078570760549798248448), (-632806975619/2475880078570760549798248448)), (110279/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769748960529055/154742504910672534362390528), (-632599909323/154742504910672534362390528)), (110283/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548202307725573/9671406556917033397649408), (-592842502485/9671406556917033397649408)), (103395/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628803478363241/302231454903657293676544), (-129629346151/151115727451828646838272)), (22619/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117867042358631/4722366482869645213696), (-421089421821/37778931862957161709568)), (147031/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648050374307593/2361183241434822606848), (-631273942703/4722366482869645213696)), (55141/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202433903494285/73786976294838206464), (-433708394821/295147905179352825856)), (151649/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910502753034887/36893488147419103232), (-1083394411699/73786976294838206464)), (47395/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909940935200545/4611686018427387904), (-1217614634765/9223372036854775808)), (26663/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591133777339819/1152921504606846976), (-1216111353787/1152921504606846976)), (213337/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192089010514539/144115188075855872), (-265602184631/36028797018963968)), (186707/144115188075855872), by norm_num⟩
  | 4 => ⟨((185988425192905/4503599627370496), (-1590241943365/36028797018963968)), (35017/4503599627370496), by norm_num⟩
  | 3 => ⟨((1484608502238357/9007199254740992), (-1981916876261/9007199254740992)), (175151/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109344787568905/2251799813685248), (-1973116447963/2251799813685248)), (701001/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101157603096151/1125899906842624), (-2937770947783/1125899906842624)), (32891/70368744177664), by norm_num⟩
  | 0 => ⟨((2153550483121007/2251799813685248), (-723563578405/140737488355328)), (131821/140737488355328), by norm_num⟩
  | _ => zero

private def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2153550483121007/2251799813685248), (-723563578405/140737488355328)), (502857208788824037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2059528394947479/2251799813685248), (-22143790002969/2251799813685248)), (4055911/2251799813685248), by norm_num⟩
  | 2 => ⟨((235432055082321/281474976710656), (-40506055649975/2251799813685248)), (468685/140737488355328), by norm_num⟩
  | 3 => ⟨((1574637053331573/2251799813685248), (-33880183725019/1125899906842624)), (12814389/2251799813685248), by norm_num⟩
  | 4 => ⟨((1099072114353461/2251799813685248), (-47383423999655/1125899906842624)), (2336611/281474976710656), by norm_num⟩
  | 5 => ⟨((532453528854077/2251799813685248), (-92508756211997/2251799813685248)), (19820855/2251799813685248), by norm_num⟩
  | 6 => ⟨((30525458873195/562949953421312), (-174994645245545/9007199254740992)), (88016969/18014398509481984), by norm_num⟩
  | _ => zero

private def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95772395/33554432), (-1487345291/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 16 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 16 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 16 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 16 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 16 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiBand58.Tile001Terms2
