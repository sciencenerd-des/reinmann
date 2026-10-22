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
namespace Reinmann.XiBand97.Tile025Terms3
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

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22364231/8388608), (-601302061/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1050522137440145/18014398509481984), (-341019578565201/9007199254740992)), (114306705/4503599627370496), by norm_num⟩
  | 1 => ⟨((774194843/4294967296), (502636907/4294967296)), (339/4294967296), by norm_num⟩
  | 2 => ⟨((-1196534563/4294967296), (-776836009/4294967296)), (263/2147483648), by norm_num⟩
  | 3 => ⟨((1232846377/4294967296), (200102757/1073741824)), (17/134217728), by norm_num⟩
  | 4 => ⟨((-476347561/2147483648), (-618526117/4294967296)), (211/2147483648), by norm_num⟩
  | 5 => ⟨((1177928427/8589934592), (382378097/4294967296)), (131/2147483648), by norm_num⟩
  | 6 => ⟨((-151709449/2147483648), (-787964621/17179869184)), (271/8589934592), by norm_num⟩
  | 7 => ⟨((1071863651/34359738368), (173973721/8589934592)), (481/34359738368), by norm_num⟩
  | 8 => ⟨((-207073503/17179869184), (-537760157/68719476736)), (187/34359738368), by norm_num⟩
  | 9 => ⟨((71119221/17179869184), (184693275/68719476736)), (129/68719476736), by norm_num⟩
  | 10 => ⟨((-175866025/137438953472), (-456715803/549755813888)), (321/549755813888), by norm_num⟩
  | 11 => ⟨((197676127/549755813888), (513355613/2199023255552)), (181/1099511627776), by norm_num⟩
  | 12 => ⟨((-814700401/8796093022208), (-66116833/1099511627776)), (375/8796093022208), by norm_num⟩
  | 13 => ⟨((774853393/35184372088832), (251532231/17592186044416)), (179/17592186044416), by norm_num⟩
  | 14 => ⟨((-342157819/70368744177664), (-27767743/8796093022208)), (159/70368744177664), by norm_num⟩
  | 15 => ⟨((564066317/562949953421312), (366213429/562949953421312)), (263/562949953421312), by norm_num⟩
  | 16 => ⟨((-435888233/2251799813685248), (-141497657/1125899906842624)), (51/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-3342179904351/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888924731200283/316912650057057350374175801344), (-3951435643967/633825300114114700748351602688)), (92589/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888707432651891/39614081257132168796771975168), (-4444324393877/39614081257132168796771975168)), (26047/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888417574595271/2475880078570760549798248448), (-4720808895415/2475880078570760549798248448)), (110729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770083509355063/154742504910672534362390528), (-2359681391773/77371252455336267181195264)), (221523/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548515111976793/9671406556917033397649408), (-1105716637899/2417851639229258349412352)), (207747/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157234978236267/75557863725914323419136), (-3868472664503/604462909807314587353088)), (22731/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886314526858815/75557863725914323419136), (-6283389930385/75557863725914323419136)), (295633/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296430769115709/4722366482869645213696), (-4710025107797/4722366482869645213696)), (221839/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619922788690175/590295810358705651712), (-809024474625/73786976294838206464)), (305213/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910783317897033/36893488147419103232), (-505257191957/4611686018427387904)), (190897/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113781786424061/576460752303423488), (-9086206699963/9223372036854775808)), (429901/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591754803644561/1152921504606846976), (-9075686576469/1152921504606846976)), (107595/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192626028325085/144115188075855872), (-7929402054517/144115188075855872)), (377121/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488700209350467/36028797018963968), (-11870484274217/36028797018963968)), (566761/36028797018963968), by norm_num⟩
  | 3 => ⟨((5803036512009/35184372088832), (-14796836747135/9007199254740992)), (355171/4503599627370496), by norm_num⟩
  | 2 => ⟨((69392535675909/140737488355328), (-29470124902017/4503599627370496)), (1426367/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204958543691253/2251799813685248), (-43897215707191/2251799813685248)), (1076903/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079094422385585/1125899906842624), (-86567941009215/2251799813685248)), (4364887/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079094422385585/1125899906842624), (-86567941009215/2251799813685248)), (16650722512252043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2065141427325009/2251799813685248), (-165938342711855/2251799813685248)), (8702471/2251799813685248), by norm_num⟩
  | 2 => ⟨((470431869156409/562949953421312), (-304366439532717/2251799813685248)), (17244791/2251799813685248), by norm_num⟩
  | 3 => ⟨((765667388774385/1125899906842624), (-127172648463387/562949953421312)), (16741601/1125899906842624), by norm_num⟩
  | 4 => ⟨((926467827191531/2251799813685248), (-345934657532909/1125899906842624)), (60668433/2251799813685248), by norm_num⟩
  | 5 => ⟨((84301340506377/1125899906842624), (-1138635250138835/4503599627370496)), (174406233/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1050522137440145/18014398509481984), (-341019578565201/9007199254740992)), (114306705/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-601302061/8388608)), (1/8388608), by norm_num⟩, -11, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45371695/16777216), (-609949285/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-541382503099489/9007199254740992), (264857440449943/9007199254740992)), (217587933/18014398509481984), by norm_num⟩
  | 1 => ⟨((404715945/2147483648), (-12374803/134217728)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-158623063/536870912), (155204493/1073741824)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((1326297857/4294967296), (-648857053/4294967296)), (137/2147483648), by norm_num⟩
  | 4 => ⟨((-1039649815/4294967296), (127155471/1073741824)), (217/4294967296), by norm_num⟩
  | 5 => ⟨((162990799/1073741824), (-318956195/4294967296)), (137/4294967296), by norm_num⟩
  | 6 => ⟨((-681408943/8589934592), (41670221/1073741824)), (289/17179869184), by norm_num⟩
  | 7 => ⟨((1220887885/34359738368), (-149321985/8589934592)), (261/34359738368), by norm_num⟩
  | 8 => ⟨((-957021725/68719476736), (117049555/17179869184)), (103/34359738368), by norm_num⟩
  | 9 => ⟨((1333660481/274877906944), (-652459027/274877906944)), (289/274877906944), by norm_num⟩
  | 10 => ⟨((-836336945/549755813888), (409156301/549755813888)), (183/549755813888), by norm_num⟩
  | 11 => ⟨((953574419/2199023255552), (-466511715/2199023255552)), (211/2199023255552), by norm_num⟩
  | 12 => ⟨((-498321179/4398046511104), (487581595/8796093022208)), (223/8796093022208), by norm_num⟩
  | 13 => ⟨((961528107/35184372088832), (-470402853/35184372088832)), (217/35184372088832), by norm_num⟩
  | 14 => ⟨((-430695117/70368744177664), (210706489/70368744177664)), (197/140737488355328), by norm_num⟩
  | 15 => ⟨((720235759/562949953421312), (-88089197/140737488355328)), (331/1125899906842624), by norm_num⟩
  | 16 => ⟨((-141143441/562949953421312), (552406335/4503599627370496)), (261/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (1749800027371/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444447402774067/158456325028528675187087900672), (2068645157919/316912650057057350374175801344)), (1447/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((236080009018351/4951760157141521099596496896), (581668180739/4951760157141521099596496896)), (52105/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888345964329279/2475880078570760549798248448), (2471406880053/1237940039285380274899124224)), (55377/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770011854470481/154742504910672534362390528), (617659706037/19342813113834066795298816)), (27697/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193555986021629/1208925819614629174706176), (4630816132807/9671406556917033397649408)), (25975/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257820957777397/604462909807314587353088), (506291620807/75557863725914323419136)), (90949/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235777347206917/9444732965739290427392), (3289366877113/37778931862957161709568)), (147859/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296358879895801/4722366482869645213696), (4931376253433/4722366482869645213696)), (110955/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809911907815297/295147905179352825856), (6776299040089/590295810358705651712)), (152659/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910721365924001/36893488147419103232), (4231931206129/36893488147419103232)), (95485/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910184466799555/4611686018427387904), (2378224466055/2305843009213693952)), (215041/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795807416999313/576460752303423488), (9501722389999/1152921504606846976)), (215291/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596251597937317/72057594037927936), (8301446662187/144115188075855872)), (94331/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488515246414813/36028797018963968), (6213539540961/18014398509481984)), (141779/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485344901889683/9007199254740992), (3872501783127/2251799813685248)), (355437/9007199254740992), by norm_num⟩
  | 2 => ⟨((555023140091967/1125899906842624), (30848758577681/4503599627370496)), (178463/1125899906842624), by norm_num⟩
  | 1 => ⟨((551061640469323/562949953421312), (45945941669845/2251799813685248)), (1078243/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156729141481191/2251799813685248), (90588755556073/2251799813685248)), (2186481/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156729141481191/2251799813685248), (90588755556073/2251799813685248)), (8340763100630950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062028000385129/2251799813685248), (173528222012375/2251799813685248)), (4364259/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874876889534923/2251799813685248), (317808048896641/2251799813685248)), (8665555/2251799813685248), by norm_num⟩
  | 3 => ⟨((1516192236192219/2251799813685248), (529221969522539/2251799813685248)), (8438065/1125899906842624), by norm_num⟩
  | 4 => ⟨((448255433674715/1125899906842624), (712676354741529/2251799813685248)), (3832343/281474976710656), by norm_num⟩
  | 5 => ⟨((131372312436519/2251799813685248), (1134953636723349/4503599627370496)), (87637737/4503599627370496), by norm_num⟩
  | 6 => ⟨((-541382503099489/9007199254740992), (264857440449943/9007199254740992)), (217587933/18014398509481984), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-609949285/8388608)), (1/16777216), by norm_num⟩, -12, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45987547/16777216), (-1236456857/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-149309847411541/18014398509481984), (36009916806319/562949953421312)), (195672705/9007199254740992), by norm_num⟩
  | 1 => ⟨((226266257/8589934592), (-1746238007/8589934592)), (595/8589934592), by norm_num⟩
  | 2 => ⟨((-89885793/2147483648), (346852399/1073741824)), (475/4294967296), by norm_num⟩
  | 3 => ⟨((190441259/4294967296), (-1469754127/4294967296)), (505/4294967296), by norm_num⟩
  | 4 => ⟨((-151308143/4294967296), (1167739433/4294967296)), (403/4294967296), by norm_num⟩
  | 5 => ⟨((192346169/8589934592), (-1484455511/8589934592)), (257/4294967296), by norm_num⟩
  | 6 => ⟨((-12735135/1073741824), (1572559841/17179869184)), (547/17179869184), by norm_num⟩
  | 7 => ⟨((185019175/34359738368), (-713954261/17179869184)), (499/34359738368), by norm_num⟩
  | 8 => ⟨((-4593757/2147483648), (1134492537/68719476736)), (199/34359738368), by norm_num⟩
  | 9 => ⟨((207633167/274877906944), (-1602434823/274877906944)), (141/68719476736), by norm_num⟩
  | 10 => ⟨((-32993469/137438953472), (1018524825/549755813888)), (45/68719476736), by norm_num⟩
  | 11 => ⟨((152516393/2199023255552), (-588532131/1099511627776)), (209/1099511627776), by norm_num⟩
  | 12 => ⟨((-40392109/2199023255552), (1246924529/8796093022208)), (445/8796093022208), by norm_num⟩
  | 13 => ⟨((78995875/17592186044416), (-76207563/2199023255552)), (437/35184372088832), by norm_num⟩
  | 14 => ⟨((-143458939/140737488355328), (276790557/35184372088832)), (199/70368744177664), by norm_num⟩
  | 15 => ⟨((15197341/70368744177664), (-1876597951/1125899906842624)), (677/1125899906842624), by norm_num⟩
  | 16 => ⟨((-193191871/4503599627370496), (745491163/2251799813685248)), (135/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (2213986424933/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777738590974121/633825300114114700748351602688), (327156994991/79228162514264337593543950336)), (46229/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472145747582771/9903520314283042199192993792), (2943713640261/39614081257132168796771975168)), (208063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944142868565105/1237940039285380274899124224), (3126821115945/2475880078570760549798248448)), (110553/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769952101768599/154742504910672534362390528), (3125837583087/154742504910672534362390528)), (110575/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548392373762145/9671406556917033397649408), (366178514107/1208925819614629174706176)), (207373/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157221610744759/75557863725914323419136), (1281102703809/302231454903657293676544)), (90749/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943070801823851/37778931862957161709568), (2080813421367/37778931862957161709568)), (73755/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324075455820457/1180591620717411303424), (1559754359401/2361183241434822606848)), (221341/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619746699793807/590295810358705651712), (1071636288357/147573952589676412928)), (152233/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821348339386901/73786976294838206464), (5354015432977/73786976294838206464)), (190383/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455066372533723/2305843009213693952), (6017543961311/9223372036854775808)), (53577/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397878704469555/288230376151711744), (6010396996641/1152921504606846976)), (428933/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298104881731411/36028797018963968), (5251067046283/144115188075855872)), (187837/72057594037927936), by norm_num⟩
  | 4 => ⟨((372099351709277/9007199254740992), (3930282456975/18014398509481984)), (564227/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485210954725081/9007199254740992), (4898849955337/4503599627370496)), (353269/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219864485910527/4503599627370496), (9755802704143/2251799813685248)), (88553/281474976710656), by norm_num⟩
  | 1 => ⟨((2204003173068079/2251799813685248), (14529352681863/1125899906842624)), (2134737/2251799813685248), by norm_num⟩
  | 0 => ⟨((539158079378519/562949953421312), (28643642911493/1125899906842624)), (1076881/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539158079378519/562949953421312), (28643642911493/1125899906842624)), (4107975008250999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2064029445060975/2251799813685248), (54866161386843/1125899906842624)), (8470125/2251799813685248), by norm_num⟩
  | 2 => ⟨((943284643155053/1125899906842624), (201164192219337/2251799813685248)), (4088293/562949953421312), by norm_num⟩
  | 3 => ⟨((1562606328694367/2251799813685248), (337072757746867/2251799813685248)), (15161679/1125899906842624), by norm_num⟩
  | 4 => ⟨((1033893190820749/2251799813685248), (233907126772389/1125899906842624)), (6395401/281474976710656), by norm_num⟩
  | 5 => ⟨((755027111237407/4503599627370496), (26849076923343/140737488355328)), (68240677/2251799813685248), by norm_num⟩
  | 6 => ⟨((-149309847411541/18014398509481984), (36009916806319/562949953421312)), (195672705/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1236456857/16777216)), (1/8388608), by norm_num⟩, -12, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/1048576), (-39135597/524288)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((409239047322499/9007199254740992), (767084841002031/18014398509481984)), (63261741/9007199254740992), by norm_num⟩
  | 1 => ⟨((-314066333/2147483648), (-588691437/4294967296)), (99/4294967296), by norm_num⟩
  | 2 => ⟨((1010940527/4294967296), (473731159/2147483648)), (81/2147483648), by norm_num⟩
  | 3 => ⟨((-1084697341/4294967296), (-508293925/2147483648)), (11/268435456), by norm_num⟩
  | 4 => ⟨((27277391/134217728), (409033757/2147483648)), (9/268435456), by norm_num⟩
  | 5 => ⟨((-561936221/4294967296), (-526651549/4294967296)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((301467153/4294967296), (565075313/8589934592)), (51/4294967296), by norm_num⟩
  | 7 => ⟨((-554505903/17179869184), (-259843895/8589934592)), (95/17179869184), by norm_num⟩
  | 8 => ⟨((892442823/68719476736), (52275327/4294967296)), (155/68719476736), by norm_num⟩
  | 9 => ⟨((-638369473/137438953472), (-598285463/137438953472)), (113/137438953472), by norm_num⟩
  | 10 => ⟨((410966413/274877906944), (770322645/549755813888)), (37/137438953472), by norm_num⟩
  | 11 => ⟨((-240518155/549755813888), (-901662887/2199023255552)), (175/2199023255552), by norm_num⟩
  | 12 => ⟨((258066025/2199023255552), (967446957/8796093022208)), (95/4398046511104), by norm_num⟩
  | 13 => ⟨((-63898653/2199023255552), (-479091019/17592186044416)), (95/17592186044416), by norm_num⟩
  | 14 => ⟨((58766237/8796093022208), (440609857/70368744177664)), (177/140737488355328), by norm_num⟩
  | 15 => ⟨((-403543935/281474976710656), (-378204911/281474976710656)), (77/281474976710656), by norm_num⟩
  | 16 => ⟨((162369727/562949953421312), (608697323/2251799813685248)), (63/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (980861693179/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444421832134181/158456325028528675187087900672), (144931826747/79228162514264337593543950336)), (46157/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236065686935899/4951760157141521099596496896), (1304075124881/39614081257132168796771975168)), (51931/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944112441723319/1237940039285380274899124224), (1385187641885/2475880078570760549798248448)), (55181/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769891511691105/154742504910672534362390528), (346186668569/38685626227668133590597632)), (110371/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774167925210255/4835703278458516698824704), (1297731672915/9671406556917033397649408)), (103483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628861853818141/302231454903657293676544), (1135047097793/604462909807314587353088)), (45279/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235757776573717/9444732965739290427392), (230446784981/9444732965739290427392)), (18397/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((40507585553135/147573952589676412928), (1381913575747/4722366482869645213696)), (110399/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619666199892277/590295810358705651712), (949442720761/295147905179352825856)), (75913/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821248826905941/73786976294838206464), (592934932937/18446744073709551616)), (189823/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820155065276057/9223372036854775808), (2665642440525/9223372036854775808)), (213607/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198925787135669/144115188075855872), (665610046293/288230376151711744)), (213677/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596163353711073/72057594037927936), (1163018847299/72057594037927936)), (23381/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488262435283823/36028797018963968), (435234282837/4503599627370496)), (280731/36028797018963968), by norm_num⟩
  | 3 => ⟨((742524829160551/4503599627370496), (2169901131471/4503599627370496)), (351195/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109782007940557/2251799813685248), (8642096262509/4503599627370496)), (703235/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203607317225007/2251799813685248), (12869769584087/2251799813685248)), (264245/562949953421312), by norm_num⟩
  | 0 => ⟨((2156057271508577/2251799813685248), (25368405716513/2251799813685248)), (2122543/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156057271508577/2251799813685248), (25368405716513/2251799813685248)), (8096858986861418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064099736472441/2251799813685248), (48579572019907/2251799813685248)), (2056209/1125899906842624), by norm_num⟩
  | 2 => ⟨((118187341782371/140737488355328), (44530193667673/1125899906842624)), (7716691/2251799813685248), by norm_num⟩
  | 3 => ⟨((1584483510330213/2251799813685248), (74790381441921/1125899906842624)), (6785459/1125899906842624), by norm_num⟩
  | 4 => ⟨((552494403534763/1125899906842624), (52626403735281/562949953421312)), (10450683/1125899906842624), by norm_num⟩
  | 5 => ⟨((1045108577304171/4503599627370496), (206595938876601/2251799813685248)), (12210513/1125899906842624), by norm_num⟩
  | 6 => ⟨((409239047322499/9007199254740992), (767084841002031/18014398509481984)), (63261741/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-39135597/524288)), (1/16777216), by norm_num⟩, -12, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47145793/16777216), (-1267598355/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((535590922945969/9007199254740992), (-169050651974905/18014398509481984)), (156784677/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1664168293/8589934592), (262633965/8589934592)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((1355505239/4294967296), (-213921703/4294967296)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-1472122309/4294967296), (232325853/4294967296)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((599539575/2147483648), (-94617507/2147483648)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((-1562686251/8589934592), (123309189/4294967296)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((1697127555/17179869184), (-267835495/17179869184)), (131/8589934592), by norm_num⟩
  | 7 => ⟨((-789915059/17179869184), (249323971/34359738368)), (123/17179869184), by norm_num⟩
  | 8 => ⟨((40212805/2147483648), (-25385049/8589934592)), (101/34359738368), by norm_num⟩
  | 9 => ⟨((-58229867/8589934592), (2297415/2147483648)), (37/34359738368), by norm_num⟩
  | 10 => ⟨((303549645/137438953472), (-47905279/137438953472)), (195/549755813888), by norm_num⟩
  | 11 => ⟨((-1438536797/2199023255552), (227025489/2199023255552)), (233/2199023255552), by norm_num⟩
  | 12 => ⟨((1562297253/8796093022208), (-246556987/8796093022208)), (255/8796093022208), by norm_num⟩
  | 13 => ⟨((-783094657/17592186044416), (61792805/8796093022208)), (129/17592186044416), by norm_num⟩
  | 14 => ⟨((1457941709/140737488355328), (-230087913/140737488355328)), (121/70368744177664), by norm_num⟩
  | 15 => ⟨((-1266697289/562949953421312), (99953151/281474976710656)), (53/140737488355328), by norm_num⟩
  | 16 => ⟨((1031755513/2251799813685248), (-40707127/562949953421312)), (87/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-203892567107/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888817966197805/316912650057057350374175801344), (-60250840145/158456325028528675187087900672)), (184447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888467726391113/39614081257132168796771975168), (-33882930117/4951760157141521099596496896)), (51877/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888163572052017/2475880078570760549798248448), (-287922408959/2475880078570760549798248448)), (3445/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((442457569254261/38685626227668133590597632), (-71957412889/38685626227668133590597632)), (220485/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548278524368907/9671406556917033397649408), (-269741785843/9671406556917033397649408)), (51677/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257673628728569/604462909807314587353088), (-235925597685/604462909807314587353088)), (90437/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885980986822001/75557863725914323419136), (-191597287757/37778931862957161709568)), (293929/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324045487907659/1180591620717411303424), (-143617288475/2361183241434822606848)), (110227/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809791417658945/295147905179352825856), (-98671382771/147573952589676412928)), (9473/18446744073709551616), by norm_num⟩
  | 8 => ⟨((910572472561781/36893488147419103232), (-123241056561/18446744073709551616)), (189469/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820038642917123/9223372036854775808), (-138511336491/2305843009213693952)), (213165/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591290429388193/1152921504606846976), (-69171486215/144115188075855872)), (426361/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192225945608759/144115188075855872), (-483443869893/144115188075855872)), (373101/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488112533483557/36028797018963968), (-723655494879/36028797018963968)), (559723/36028797018963968), by norm_num⟩
  | 3 => ⟨((185608055484585/1125899906842624), (-901932517961/9007199254740992)), (699781/9007199254740992), by norm_num⟩
  | 2 => ⟨((277400005039313/562949953421312), (-1795979191031/4503599627370496)), (1399947/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203077364882837/2251799813685248), (-668585094727/562949953421312)), (2100911/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077530340671507/1125899906842624), (-5270682201381/2251799813685248)), (4205919/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1077530340671507/1125899906842624), (-5270682201381/2251799813685248)), (16044307717330168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32226018799179/35184372088832), (-10088498903871/2251799813685248)), (8070149/2251799813685248), by norm_num⟩
  | 2 => ⟨((1889004924208823/2251799813685248), (-18480486422257/2251799813685248)), (14855511/2251799813685248), by norm_num⟩
  | 3 => ⟨((1584509446009531/2251799813685248), (-31006068693367/2251799813685248)), (6292005/562949953421312), by norm_num⟩
  | 4 => ⟨((278633650396555/562949953421312), (-10908920151267/562949953421312)), (18056369/1125899906842624), by norm_num⟩
  | 5 => ⟨((1101592866269285/4503599627370496), (-21597601883855/1125899906842624)), (37147797/2251799813685248), by norm_num⟩
  | 6 => ⟨((535590922945969/9007199254740992), (-169050651974905/18014398509481984)), (156784677/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1267598355/16777216)), (1/8388608), by norm_num⟩, -12, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47691909/16777216), (-1282281645/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((269431194255057/9007199254740992), (-225210218275629/4503599627370496)), (138171357/18014398509481984), by norm_num⟩
  | 1 => ⟨((-423431999/4294967296), (707870617/4294967296)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((174445349/1073741824), (-583256519/2147483648)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-47911951/268435456), (640772779/2147483648)), (51/1073741824), by norm_num⟩
  | 4 => ⟨((315819949/2147483648), (-527970637/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((-104089103/1073741824), (174010509/1073741824)), (57/2147483648), by norm_num⟩
  | 6 => ⟨((457414271/8589934592), (-382340167/4294967296)), (127/8589934592), by norm_num⟩
  | 7 => ⟨((-215366117/8589934592), (720074753/17179869184)), (121/17179869184), by norm_num⟩
  | 8 => ⟨((177452897/17179869184), (-1186624459/68719476736)), (201/68719476736), by norm_num⟩
  | 9 => ⟨((-259935911/68719476736), (869093475/137438953472)), (149/137438953472), by norm_num⟩
  | 10 => ⟨((685365087/549755813888), (-572878063/274877906944)), (99/274877906944), by norm_num⟩
  | 11 => ⟨((-102675069/274877906944), (343293207/549755813888)), (121/1099511627776), by norm_num⟩
  | 12 => ⟨((225600185/2199023255552), (-47143267/274877906944)), (135/4398046511104), by norm_num⟩
  | 13 => ⟨((-457563943/17592186044416), (764930547/17592186044416)), (139/17592186044416), by norm_num⟩
  | 14 => ⟨((430873175/70368744177664), (-360155185/35184372088832)), (133/70368744177664), by norm_num⟩
  | 15 => ⟨((-94672513/70368744177664), (1266146919/562949953421312)), (59/140737488355328), by norm_num⟩
  | 16 => ⟨((624050317/2251799813685248), (-1043253423/2251799813685248)), (49/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-41997757297/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444396122984063/158456325028528675187087900672), (-794226597545/316912650057057350374175801344)), (92357/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888409797873889/39614081257132168796771975168), (-1786573201739/39614081257132168796771975168)), (12989/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888101943391437/2475880078570760549798248448), (-948841925479/1237940039285380274899124224)), (55209/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221221069865697/19342813113834066795298816), (-1897065229071/154742504910672534362390528)), (110431/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548220568729559/9671406556917033397649408), (-222230204939/1208925819614629174706176)), (103543/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257622822718893/604462909807314587353088), (-1554954729109/604462909807314587353088)), (90615/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471474562369591/18889465931478580854784), (-2525570764681/75557863725914323419136)), (73637/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296119743461441/4722366482869645213696), (-1893101889389/4722366482869645213696)), (110479/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404874261839603/147573952589676412928), (-40644805013/9223372036854775808)), (75973/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821037333301513/73786976294838206464), (-812241293123/18446744073709551616)), (47497/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819917062581647/9223372036854775808), (-912871962365/2305843009213693952)), (213813/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795584102250779/576460752303423488), (-1823497793291/576460752303423488)), (106955/576460752303423488), by norm_num⟩
  | 5 => ⟨((596059138052619/72057594037927936), (-1593037241287/72057594037927936)), (187281/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487949589739071/36028797018963968), (-4769036236471/36028797018963968)), (281139/36028797018963968), by norm_num⟩
  | 3 => ⟨((742329129236933/4503599627370496), (-5943703224791/9007199254740992)), (175903/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218780205677839/4503599627370496), (-5917395003625/2251799813685248)), (704765/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202429139127577/2251799813685248), (-8810600745259/1125899906842624)), (265011/562949953421312), by norm_num⟩
  | 0 => ⟨((2153691442146211/2251799813685248), (-17360900784151/1125899906842624)), (532939/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153691442146211/2251799813685248), (-17360900784151/1125899906842624)), (2033000948192405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2059322145906285/2251799813685248), (-66418023875015/2251799813685248)), (2071749/1125899906842624), by norm_num⟩
  | 2 => ⟨((940668953114311/1125899906842624), (-60740793485237/1125899906842624)), (7823077/2251799813685248), by norm_num⟩
  | 3 => ⟨((782634966043323/1125899906842624), (-101495662752687/1125899906842624)), (1739521/281474976710656), by norm_num⟩
  | 4 => ⟨((1069750724475729/2251799813685248), (-70551613060127/562949953421312)), (21855781/2251799813685248), by norm_num⟩
  | 5 => ⟨((236416693073543/1125899906842624), (-268132677604179/2251799813685248)), (52487935/4503599627370496), by norm_num⟩
  | 6 => ⟨((269431194255057/9007199254740992), (-225210218275629/4503599627370496)), (138171357/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1282281645/16777216)), (1/16777216), by norm_num⟩, -12, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile025Terms3
