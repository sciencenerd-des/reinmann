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
namespace Reinmann.XiBand58.Tile007Terms3
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
  | 0 => ⟨((15/16), (2893/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2893/160))
  have he : value ((15/16), (2893/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24308947/8388608), (-937677115/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((785488708664563/18014398509481984), (608057949395505/18014398509481984)), (52903705/9007199254740992), by norm_num⟩
  | 1 => ⟨((-289437645/2147483648), (-112028893/1073741824)), (79/4294967296), by norm_num⟩
  | 2 => ⟨((55916503/268435456), (692572129/4294967296)), (31/1073741824), by norm_num⟩
  | 3 => ⟨((-921814851/4294967296), (-713589951/4294967296)), (65/2147483648), by norm_num⟩
  | 4 => ⟨((356171105/2147483648), (17232319/134217728)), (51/2147483648), by norm_num⟩
  | 5 => ⟨((-880752005/8589934592), (-681802619/8589934592)), (1/67108864), by norm_num⟩
  | 6 => ⟨((907480613/17179869184), (702493613/17179869184)), (67/8589934592), by norm_num⟩
  | 7 => ⟨((-801446029/34359738368), (-620410737/34359738368)), (15/4294967296), by norm_num⟩
  | 8 => ⟨((619325925/68719476736), (239714491/34359738368)), (47/34359738368), by norm_num⟩
  | 9 => ⟨((-850827879/274877906944), (-658637927/274877906944)), (131/274877906944), by norm_num⟩
  | 10 => ⟨((525989019/549755813888), (407175559/549755813888)), (41/274877906944), by norm_num⟩
  | 11 => ⟨((-1182439555/4398046511104), (-228835807/1099511627776)), (187/4398046511104), by norm_num⟩
  | 12 => ⟨((609161811/8796093022208), (117890199/2199023255552)), (49/4398046511104), by norm_num⟩
  | 13 => ⟨((-289683849/17592186044416), (-896993501/70368744177664)), (189/70368744177664), by norm_num⟩
  | 14 => ⟨((1023342943/281474976710656), (792184283/281474976710656)), (169/281474976710656), by norm_num⟩
  | 15 => ⟨((-421759531/562949953421312), (-652980067/1125899906842624)), (141/1125899906842624), by norm_num⟩
  | 16 => ⟨((162959577/1125899906842624), (504597277/4503599627370496)), (111/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580200990935661/10141204801825835211973625643008), (214525943975/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27773442525413/9903520314283042199192993792), (1014141479971/633825300114114700748351602688)), (23075/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888315173307295/39614081257132168796771975168), (570312939577/19807040628566084398385987584)), (103845/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888001493233659/2475880078570760549798248448), (605778496645/1237940039285380274899124224)), (55171/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769668208163967/154742504910672534362390528), (1211154467263/154742504910672534362390528)), (110351/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387031648855807/2417851639229258349412352), (283757453799/2417851639229258349412352)), (103463/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257540701523203/604462909807314587353088), (992723799859/604462909807314587353088)), (90539/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((14732539063031/590295810358705651712), (1612375453729/75557863725914323419136)), (147143/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296019979063651/4722366482869645213696), (1208581403875/4722366482869645213696)), (27593/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809680075772445/295147905179352825856), (1660662460207/590295810358705651712)), (151785/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820866633292067/73786976294838206464), (518531019073/18446744073709551616)), (189767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819725601275645/9223372036854775808), (72845279729/288230376151711744)), (106769/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1590977462010733/1152921504606846976), (2328126700359/1152921504606846976)), (6675/36028797018963968), by norm_num⟩
  | 5 => ⟨((1191952183115595/144115188075855872), (508457048625/36028797018963968)), (93485/72057594037927936), by norm_num⟩
  | 4 => ⟨((371925514675473/9007199254740992), (1522094547953/18014398509481984)), (280595/36028797018963968), by norm_num⟩
  | 3 => ⟨((742175824195895/4503599627370496), (3793795540983/9007199254740992)), (175495/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218175352530505/4503599627370496), (7553377386391/4503599627370496)), (702725/4503599627370496), by norm_num⟩
  | 1 => ⟨((1100771311583031/1125899906842624), (11244911423595/2251799813685248)), (527981/1125899906842624), by norm_num⟩
  | 0 => ⟨((2152000547824331/2251799813685248), (11075736130565/1125899906842624)), (1059751/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2152000547824331/2251799813685248), (11075736130565/1125899906842624)), (4042629246238326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2056406454059749/2251799813685248), (42339447895283/2251799813685248)), (4092833/2251799813685248), by norm_num⟩
  | 2 => ⟨((1877171696063279/2251799813685248), (77331131643265/2251799813685248)), (7629291/2251799813685248), by norm_num⟩
  | 3 => ⟨((781107061826849/1125899906842624), (64465682367967/1125899906842624)), (13244047/2251799813685248), by norm_num⟩
  | 4 => ⟨((1076423248904855/2251799813685248), (178895475297855/2251799813685248)), (19893075/2251799813685248), by norm_num⟩
  | 5 => ⟨((1000695899212223/4503599627370496), (171034074667005/2251799813685248)), (22179725/2251799813685248), by norm_num⟩
  | 6 => ⟨((785488708664563/18014398509481984), (608057949395505/18014398509481984)), (52903705/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24308947/8388608), (-937677115/16777216)), (1/16777216), by norm_num⟩, -9, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-98634119/33554432), (-237790423/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1885598117411951/36028797018963968), (-34414890817889/4503599627370496)), (136600537/36028797018963968), by norm_num⟩
  | 1 => ⟨((-1409597871/8589934592), (205817587/8589934592)), (13/1073741824), by norm_num⟩
  | 2 => ⟨((1104946493/4294967296), (-161334963/4294967296)), (83/4294967296), by norm_num⟩
  | 3 => ⟨((-144356389/536870912), (84310807/2147483648)), (89/4294967296), by norm_num⟩
  | 4 => ⟨((1810514491/8589934592), (-16522253/536870912)), (71/4294967296), by norm_num⟩
  | 5 => ⟨((-1135371543/8589934592), (41444343/2147483648)), (91/8589934592), by norm_num⟩
  | 6 => ⟨((593325151/8589934592), (-21658083/2147483648)), (97/17179869184), by norm_num⟩
  | 7 => ⟨((-265766797/8589934592), (38805025/8589934592)), (89/34359738368), by norm_num⟩
  | 8 => ⟨((1666620509/137438953472), (-243345863/137438953472)), (71/68719476736), by norm_num⟩
  | 9 => ⟨((-145157749/34359738368), (169557677/274877906944)), (101/274877906944), by norm_num⟩
  | 10 => ⟨((1456452103/1099511627776), (-106329423/549755813888)), (129/1099511627776), by norm_num⟩
  | 11 => ⟨((-1660617143/4398046511104), (121234651/2199023255552)), (149/4398046511104), by norm_num⟩
  | 12 => ⟨((867809241/8796093022208), (-253420365/17592186044416)), (79/8796093022208), by norm_num⟩
  | 13 => ⟨((-1674468219/70368744177664), (30561465/8796093022208)), (155/70368744177664), by norm_num⟩
  | 14 => ⟨((1500081547/281474976710656), (-109514625/140737488355328)), (141/281474976710656), by norm_num⟩
  | 15 => ⟨((-627132935/562949953421312), (183137319/1125899906842624)), (119/1125899906842624), by norm_num⟩
  | 16 => ⟨((983185845/4503599627370496), (-143556501/4503599627370496)), (95/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395036676633591/2535301200456458802993406410752), (-47215442429/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777436693643483/633825300114114700748351602688), (-111594523379/316912650057057350374175801344)), (92223/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888243638218533/39614081257132168796771975168), (-251024573725/39614081257132168796771975168)), (12969/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1887925548463051/2475880078570760549798248448), (-266633699157/2475880078570760549798248448)), (110239/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884796166119399/77371252455336267181195264), (-266543853151/154742504910672534362390528)), (110241/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193506941854857/1208925819614629174706176), (-249789443759/9671406556917033397649408)), (103353/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257478596547859/604462909807314587353088), (-54617598229/151115727451828646838272)), (22609/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885664216299185/75557863725914323419136), (-88708917849/18889465931478580854784)), (146961/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((323986127706249/1180591620717411303424), (-66492619595/1180591620717411303424)), (110225/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619256576810749/590295810358705651712), (-365455652273/590295810358705651712)), (37891/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1820737455602231/73786976294838206464), (-456439267179/73786976294838206464)), (189463/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909790337727435/4611686018427387904), (-512971809573/9223372036854775808)), (213157/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590833034036193/1152921504606846976), (-256159833533/576460752303423488)), (53293/288230376151711744), by norm_num⟩
  | 5 => ⟨((297956591834203/36028797018963968), (-223773583715/72057594037927936)), (93271/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487514448994209/36028797018963968), (-83732307707/4503599627370496)), (279847/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484119077975309/9007199254740992), (-208692585493/2251799813685248)), (87467/2251799813685248), by norm_num⟩
  | 2 => ⟨((2217716006107673/4503599627370496), (-1661907500941/4503599627370496)), (349959/2251799813685248), by norm_num⟩
  | 1 => ⟨((2200867982430897/2251799813685248), (-2473865585797/2251799813685248)), (525173/1125899906842624), by norm_num⟩
  | 0 => ⟨((134419258937907/140737488355328), (-1218067494681/562949953421312)), (2102645/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((134419258937907/140737488355328), (-1218067494681/562949953421312)), (8020954140670012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2054144311260841/2251799813685248), (-9307071307567/2251799813685248)), (4025599/2251799813685248), by norm_num⟩
  | 2 => ⟨((1873799884104055/2251799813685248), (-16980255051757/2251799813685248)), (7377769/2251799813685248), by norm_num⟩
  | 3 => ⟨((194890641214515/281474976710656), (-28259705640501/2251799813685248)), (6194929/1125899906842624), by norm_num⟩
  | 4 => ⟨((2158338005341971/4503599627370496), (-78267023479991/4503599627370496)), (34936451/4503599627370496), by norm_num⟩
  | 5 => ⟨((2066034995679873/9007199254740992), (-150037041761181/9007199254740992)), (17350353/2251799813685248), by norm_num⟩
  | 6 => ⟨((1885598117411951/36028797018963968), (-34414890817889/4503599627370496)), (136600537/36028797018963968), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-98634119/33554432), (-237790423/4194304)), (1/16777216), by norm_num⟩, -9, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-99972929/33554432), (-1928144561/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((558630115014815/18014398509481984), (-362672128977795/9007199254740992)), (56829975/9007199254740992), by norm_num⟩
  | 1 => ⟨((-846555985/8589934592), (1099196957/8589934592)), (87/4294967296), by norm_num⟩
  | 2 => ⟨((672600123/4294967296), (-873326775/4294967296)), (35/1073741824), by norm_num⟩
  | 3 => ⟨((-712519799/4294967296), (462579917/2147483648)), (75/2147483648), by norm_num⟩
  | 4 => ⟨((566106569/4294967296), (-367525969/2147483648)), (121/4294967296), by norm_num⟩
  | 5 => ⟨((-179911715/2147483648), (934413851/8589934592)), (39/2147483648), by norm_num⟩
  | 6 => ⟨((190589705/4294967296), (-494936253/8589934592)), (167/17179869184), by norm_num⟩
  | 7 => ⟨((-346116767/17179869184), (224704865/8589934592)), (77/17179869184), by norm_num⟩
  | 8 => ⟨((274994429/34359738368), (-714124157/68719476736)), (31/17179869184), by norm_num⟩
  | 9 => ⟨((-776841865/274877906944), (1008677783/274877906944)), (177/274877906944), by norm_num⟩
  | 10 => ⟨((493769053/549755813888), (-320563229/274877906944)), (57/274877906944), by norm_num⟩
  | 11 => ⟨((-285313569/1099511627776), (370460799/1099511627776)), (133/2199023255552), by norm_num⟩
  | 12 => ⟨((604494587/8796093022208), (-784896241/8796093022208)), (143/8796093022208), by norm_num⟩
  | 13 => ⟨((-591112719/35184372088832), (767520771/35184372088832)), (71/17592186044416), by norm_num⟩
  | 14 => ⟨((33546215/8796093022208), (-87115083/17592186044416)), (131/140737488355328), by norm_num⟩
  | 15 => ⟨((-454876489/562949953421312), (147656759/140737488355328)), (7/35184372088832), by norm_num⟩
  | 16 => ⟨((90351373/562949953421312), (-938522257/4503599627370496)), (45/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395023683197255/2535301200456458802993406410752), (-1191261869705/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888687119042321/316912650057057350374175801344), (-175961411337/79228162514264337593543950336)), (92339/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944086668711335/19807040628566084398385987584), (-1583248745415/39614081257132168796771975168)), (103891/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((235981350013773/309485009821345068724781056), (-840845425531/1237940039285380274899124224)), (110395/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769517523513735/154742504910672534362390528), (-1681116371461/154742504910672534362390528)), (55203/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96749083599019/604462909807314587353088), (-393859120691/2417851639229258349412352)), (51759/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257417109954955/604462909807314587353088), (-1377897109847/604462909807314587353088)), (90591/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885564180763833/75557863725914323419136), (-2237940048249/75557863725914323419136)), (147233/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295869379498213/4722366482869645213696), (-1677455768247/4722366482869645213696)), (110445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404788275363845/147573952589676412928), (-2304879075513/590295810358705651712)), (151895/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910303928644581/36893488147419103232), (-2878667041913/73786976294838206464)), (189919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819434528835953/9223372036854775808), (-1617580056575/4611686018427387904)), (213727/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590686453113953/1152921504606846976), (-3230989850289/1152921504606846976)), (213813/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191697622280591/144115188075855872), (-1411215804335/72057594037927936)), (11699/9007199254740992), by norm_num⟩
  | 4 => ⟨((92957522656509/2251799813685248), (-528036994125/4503599627370496)), (280969/36028797018963968), by norm_num⟩
  | 3 => ⟨((741937392289071/4503599627370496), (-1316011080351/2251799813685248)), (5493/140737488355328), by norm_num⟩
  | 2 => ⟨((277152800561893/562949953421312), (-5239634571501/2251799813685248)), (352065/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100057592922841/1125899906842624), (-974837750869/140737488355328)), (132347/281474976710656), by norm_num⟩
  | 0 => ⟨((268644228063385/281474976710656), (-30712089877439/2251799813685248)), (2127963/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((268644228063385/281474976710656), (-30712089877439/2251799813685248)), (8117534646041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((256345996037453/281474976710656), (-29312110702541/1125899906842624)), (4119971/2251799813685248), by norm_num⟩
  | 2 => ⟨((933078605595753/1125899906842624), (-106780962227091/2251799813685248)), (7718835/2251799813685248), by norm_num⟩
  | 3 => ⟨((1541496069895805/2251799813685248), (-176987369362939/2251799813685248)), (6762939/1125899906842624), by norm_num⟩
  | 4 => ⟨((65083649708203/140737488355328), (-7572424195861/70368744177664)), (10322409/1125899906842624), by norm_num⟩
  | 5 => ⟨((113872005912635/562949953421312), (-448236281777407/4503599627370496)), (47074957/4503599627370496), by norm_num⟩
  | 6 => ⟨((558630115014815/18014398509481984), (-362672128977795/9007199254740992)), (56829975/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-99972929/33554432), (-1928144561/33554432)), (1/16777216), by norm_num⟩, -9, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-50628539/16777216), (-1952911513/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-144056260156953/36028797018963968), (-878203525041599/18014398509481984)), (36807557/4503599627370496), by norm_num⟩
  | 1 => ⟨((27638627/2147483648), (336984169/2147483648)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((-22241327/1073741824), (-1084710195/4294967296)), (185/4294967296), by norm_num⟩
  | 3 => ⟨((95456093/4294967296), (1163849141/4294967296)), (25/536870912), by norm_num⟩
  | 4 => ⟨((-153630655/8589934592), (-468285733/2147483648)), (81/2147483648), by norm_num⟩
  | 5 => ⟨((6181475/536870912), (301470725/2147483648)), (105/4294967296), by norm_num⟩
  | 6 => ⟨((-106119469/17179869184), (-646931219/8589934592)), (227/17179869184), by norm_num⟩
  | 7 => ⟨((97595827/34359738368), (148742233/4294967296)), (211/34359738368), by norm_num⟩
  | 8 => ⟨((-19634303/17179869184), (-239391389/17179869184)), (341/137438953472), by norm_num⟩
  | 9 => ⟨((112356237/274877906944), (1369904275/274877906944)), (123/137438953472), by norm_num⟩
  | 10 => ⟨((-72332155/549755813888), (-881910351/549755813888)), (319/1099511627776), by norm_num⟩
  | 11 => ⟨((84664809/2199023255552), (1032276331/2199023255552)), (47/549755813888), by norm_num⟩
  | 12 => ⟨((-22710459/2199023255552), (-69224361/549755813888)), (51/2199023255552), by norm_num⟩
  | 13 => ⟨((44985937/17592186044416), (1096982755/35184372088832)), (51/8796093022208), by norm_num⟩
  | 14 => ⟨((-41372613/70368744177664), (-63054487/8796093022208)), (189/140737488355328), by norm_num⟩
  | 15 => ⟨((35512881/281474976710656), (1731964279/1125899906842624)), (327/1125899906842624), by norm_num⟩
  | 16 => ⟨((-57155777/2251799813685248), (-1393744487/4503599627370496)), (265/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98752805064393/633825300114114700748351602688), (-2152736056619/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888656460341705/316912650057057350374175801344), (-635921493779/158456325028528675187087900672)), (92451/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888104243090883/39614081257132168796771975168), (-715226049053/9903520314283042199192993792)), (13003/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((117986077034965/154742504910672534362390528), (-3038775169847/2475880078570760549798248448)), (6909/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769443782051431/154742504910672534362390528), (-379715403531/19342813113834066795298816)), (110565/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547916020366207/9671406556917033397649408), (-1423374151481/4835703278458516698824704)), (103677/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257356272999065/604462909807314587353088), (-2489788064153/604462909807314587353088)), (22685/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471366243854729/18889465931478580854784), (-2021906449971/37778931862957161709568)), (73747/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1295794673798703/4722366482869645213696), (-1515514834021/2361183241434822606848)), (110657/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619049891693765/590295810358705651712), (-4164694111089/590295810358705651712)), (76107/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820478112387993/73786976294838206464), (-650176718807/9223372036854775808)), (47589/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909643780347065/4611686018427387904), (-5845472275299/9223372036854775808)), (214275/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795269116028007/576460752303423488), (-5837833378395/1152921504606846976)), (214429/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595783262059243/72057594037927936), (-5099522596177/144115188075855872)), (23475/18014398509481984), by norm_num⟩
  | 4 => ⟨((1487120917744133/36028797018963968), (-954018875825/4503599627370496)), (4407/562949953421312), by norm_num⟩
  | 3 => ⟨((23181572028021/140737488355328), (-4755137170387/4503599627370496)), (353171/9007199254740992), by norm_num⟩
  | 2 => ⟨((2216699555294999/4503599627370496), (-4732769354081/1125899906842624)), (708181/4503599627370496), by norm_num⟩
  | 1 => ⟨((2199295035210363/2251799813685248), (-28173887416151/2251799813685248)), (1066887/2251799813685248), by norm_num⟩
  | 0 => ⟨((2147372234862743/2251799813685248), (-55462536762875/2251799813685248)), (538087/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2147372234862743/2251799813685248), (-55462536762875/2251799813685248)), (2052639009715843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1023210721057319/1125899906842624), (-52890452692923/1125899906842624)), (1052773/562949953421312), by norm_num⟩
  | 2 => ⟨((231850711896037/281474976710656), (-48066509205723/562949953421312)), (8049671/2251799813685248), by norm_num⟩
  | 3 => ⟨((1511385655700599/2251799813685248), (-316738759741619/2251799813685248)), (14635631/2251799813685248), by norm_num⟩
  | 4 => ⟨((242468618331645/562949953421312), (-212591907668039/1125899906842624)), (23763885/2251799813685248), by norm_num⟩
  | 5 => ⟨((84363096196279/562949953421312), (-732525025466061/4503599627370496)), (920153/70368744177664), by norm_num⟩
  | 6 => ⟨((-144056260156953/36028797018963968), (-878203525041599/18014398509481984)), (36807557/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/16777216), (-1952911513/33554432)), (1/16777216), by norm_num⟩, -9, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-102490855/33554432), (-988353479/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-301963134266181/9007199254740992), (-597204940180747/18014398509481984)), (156940483/18014398509481984), by norm_num⟩
  | 1 => ⟨((938248675/8589934592), (57987909/536870912)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((-382113095/2147483648), (-377860411/2147483648)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((829974235/4294967296), (820737131/4294967296)), (221/4294967296), by norm_num⟩
  | 4 => ⟨((-338017023/2147483648), (-668510201/4294967296)), (91/2147483648), by norm_num⟩
  | 5 => ⟨((440516837/4294967296), (871228309/8589934592)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((-956830921/17179869184), (-946181979/17179869184)), (131/8589934592), by norm_num⟩
  | 7 => ⟨((890699289/34359738368), (55049147/2147483648)), (123/17179869184), by norm_num⟩
  | 8 => ⟨((-181374017/17179869184), (-717421741/68719476736)), (101/34359738368), by norm_num⟩
  | 9 => ⟨((1050549435/274877906944), (1038857463/274877906944)), (295/274877906944), by norm_num⟩
  | 10 => ⟨((-85569787/68719476736), (-676939581/549755813888)), (97/274877906944), by norm_num⟩
  | 11 => ⟨((405519457/1099511627776), (802012547/2199023255552)), (29/274877906944), by norm_num⟩
  | 12 => ⟨((-880814359/8796093022208), (-435505717/4398046511104)), (127/4398046511104), by norm_num⟩
  | 13 => ⟨((883008681/35184372088832), (873181335/35184372088832)), (257/35184372088832), by norm_num⟩
  | 14 => ⟨((-821979293/140737488355328), (-812831167/140737488355328)), (241/140737488355328), by norm_num⟩
  | 15 => ⟨((357078385/281474976710656), (706208643/562949953421312)), (211/562949953421312), by norm_num⟩
  | 16 => ⟨((-581697925/2251799813685248), (-35951499/140737488355328)), (173/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((789998492377765/5070602400912917605986812821504), (-3076495513723/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444313176607485/158456325028528675187087900672), (-1817492405203/316912650057057350374175801344)), (92559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888036324984607/39614081257132168796771975168), (-2044138282459/19807040628566084398385987584)), (13019/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1887704825647527/2475880078570760549798248448), (-4342439755985/2475880078570760549798248448)), (3459/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((884685550562815/77371252455336267181195264), (-4340917036643/154742504910672534362390528)), (55359/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((773923795573313/4835703278458516698824704), (-2033996219811/4835703278458516698824704)), (51915/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257296106904703/604462909807314587353088), (-3557876785049/604462909807314587353088)), (22721/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117835416341615/4722366482869645213696), (-5778520101511/75557863725914323419136)), (147745/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1295720462978553/4722366482869645213696), (-2165620280395/2361183241434822606848)), (55431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1618947080652617/590295810358705651712), (-5951153025515/590295810358705651712)), (19065/73786976294838206464), by norm_num⟩
  | 8 => ⟨((56885888877951/2305843009213693952), (-7432491915849/73786976294838206464)), (95389/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819140100093343/9223372036854775808), (-8352693245409/9223372036854775808)), (214801/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590388797217453/1152921504606846976), (-8341629615891/1152921504606846976)), (107511/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191433555131597/144115188075855872), (-7286495228261/144115188075855872)), (23549/18014398509481984), by norm_num⟩
  | 4 => ⟨((1486917056000487/36028797018963968), (-5452460589935/18014398509481984)), (283085/36028797018963968), by norm_num⟩
  | 3 => ⟨((741679055103477/4503599627370496), (-13587802813439/9007199254740992)), (354729/9007199254740992), by norm_num⟩
  | 2 => ⟨((2216151706530003/4503599627370496), (-27045916150931/4503599627370496)), (712081/4503599627370496), by norm_num⟩
  | 1 => ⟨((549604180535879/562949953421312), (-10061474034177/562949953421312)), (537351/1125899906842624), by norm_num⟩
  | 0 => ⟨((1072696466189833/1125899906842624), (-79207336071055/2251799813685248)), (2175869/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1072696466189833/1125899906842624), (-79207336071055/2251799813685248)), (8300281533248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2041228089762881/2251799813685248), (-150928921804427/2251799813685248)), (4299175/2251799813685248), by norm_num⟩
  | 2 => ⟨((57507229186959/70368744177664), (-136815161308955/1125899906842624)), (8370609/2251799813685248), by norm_num⟩
  | 3 => ⟨((735317986303601/1125899906842624), (-447236109132793/2251799813685248)), (15715705/2251799813685248), by norm_num⟩
  | 4 => ⟨((871636108452241/2251799813685248), (-584174051656175/2251799813685248)), (26770331/2251799813685248), by norm_num⟩
  | 5 => ⟨((371693949334229/4503599627370496), (-226124540001201/1125899906842624)), (69229103/4503599627370496), by norm_num⟩
  | 6 => ⟨((-301963134266181/9007199254740992), (-597204940180747/18014398509481984)), (156940483/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-102490855/33554432), (-988353479/16777216)), (1/16777216), by norm_num⟩, -9, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-103678063/33554432), (-499901061/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1631858571079721/36028797018963968), (-79732090707701/18014398509481984)), (138299255/18014398509481984), by norm_num⟩
  | 1 => ⟨((1282296095/8589934592), (125305159/8589934592)), (55/2147483648), by norm_num⟩
  | 2 => ⟨((-528279843/2147483648), (-103246341/4294967296)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((1160749455/4294967296), (113427699/4294967296)), (203/4294967296), by norm_num⟩
  | 4 => ⟨((-1912820423/8589934592), (-46729899/2147483648)), (21/536870912), by norm_num⟩
  | 5 => ⟨((630434407/4294967296), (123211299/8589934592)), (223/8589934592), by norm_num⟩
  | 6 => ⟨((-1385205973/17179869184), (-135361447/17179869184)), (247/17179869184), by norm_num⟩
  | 7 => ⟨((1304403689/34359738368), (127465499/34359738368)), (117/17179869184), by norm_num⟩
  | 8 => ⟨((-537387721/34359738368), (-105026373/68719476736)), (195/68719476736), by norm_num⟩
  | 9 => ⟨((1574348677/274877906944), (1201909/2147483648)), (9/8589934592), by norm_num⟩
  | 10 => ⟨((-518879641/274877906944), (-101409177/549755813888)), (191/549755813888), by norm_num⟩
  | 11 => ⟨((1243740109/2199023255552), (30384373/549755813888)), (231/2199023255552), by norm_num⟩
  | 12 => ⟨((-170798521/1099511627776), (-66761291/4398046511104)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((692829615/17592186044416), (67702869/17592186044416)), (261/35184372088832), by norm_num⟩
  | 14 => ⟨((-1304830507/140737488355328), (-127507207/140737488355328)), (31/17592186044416), by norm_num⟩
  | 15 => ⟨((143350283/70368744177664), (28016197/140737488355328)), (55/140737488355328), by norm_num⟩
  | 16 => ⟨((-944918295/2251799813685248), (-92336815/2251799813685248)), (365/4503599627370496), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1579950896329045/10141204801825835211973625643008), (-1982693836447/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888596780133053/316912650057057350374175801344), (-1171241827971/158456325028528675187087900672)), (46331/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((943984775755567/19807040628566084398385987584), (-2634582917261/19807040628566084398385987584)), (104275/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1887633556122845/2475880078570760549798248448), (-1399180437353/618970019642690137449562112)), (110827/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442324867265769/38685626227668133590597632), (-2797367257039/77371252455336267181195264)), (110865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1547780051276063/9671406556917033397649408), (-5242952849851/9671406556917033397649408)), (51989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628618312569355/302231454903657293676544), (-4585473750803/604462909807314587353088)), (45511/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885269283803763/75557863725914323419136), (-1861860058143/18889465931478580854784)), (147987/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((647823400415851/2361183241434822606848), (-697765189061/590295810358705651712)), (55529/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1618844774957371/590295810358705651712), (-1917449949709/147573952589676412928)), (76407/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1820219034616577/73786976294838206464), (-2394707288859/18446744073709551616)), (191183/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454748104797867/2305843009213693952), (-1345576642751/1152921504606846976)), (53827/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795119252287283/576460752303423488), (-5375082027595/576460752303423488)), (26949/144115188075855872), by norm_num⟩
  | 5 => ⟨((1191299120892025/144115188075855872), (-4695078089511/72057594037927936)), (47241/36028797018963968), by norm_num⟩
  | 4 => ⟨((1486709573314939/36028797018963968), (-14052804158375/36028797018963968)), (142043/18014398509481984), by norm_num⟩
  | 3 => ⟨((1483088608201603/9007199254740992), (-1094334556533/562949953421312)), (356231/9007199254740992), by norm_num⟩
  | 2 => ⟨((1107791240281335/2251799813685248), (-34849150450985/4503599627370496)), (715843/4503599627370496), by norm_num⟩
  | 1 => ⟨((1098744054555183/1125899906842624), (-51851242257379/2251799813685248)), (1082245/2251799813685248), by norm_num⟩
  | 0 => ⟨((133952579354747/140737488355328), (-102020977742725/2251799813685248)), (2198589/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((133952579354747/140737488355328), (-102020977742725/2251799813685248)), (8386951455123137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((15900735104097/17592186044416), (-97102579253283/1125899906842624)), (4384413/2251799813685248), by norm_num⟩
  | 2 => ⟨((28482122235237/35184372088832), (-87766374612729/562949953421312)), (8681985/2251799813685248), by norm_num⟩
  | 3 => ⟨((355222114772185/562949953421312), (-284191243038475/1125899906842624)), (8381719/1125899906842624), by norm_num⟩
  | 4 => ⟨((753115508930229/2251799813685248), (-717300099153299/2251799813685248)), (29618105/2251799813685248), by norm_num⟩
  | 5 => ⟨((93549235106681/9007199254740992), (-1919210849726271/9007199254740992)), (77361983/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1631858571079721/36028797018963968), (-79732090707701/18014398509481984)), (138299255/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-103678063/33554432), (-499901061/8388608)), (1/16777216), by norm_num⟩, -9, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand58.Tile007Terms3
