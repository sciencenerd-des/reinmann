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
namespace Reinmann.XiBand97.Tile039Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (34337/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (34337/1280))
  have he : value ((69/80), (34337/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-15897303/8388608), (-494443563/8388608)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term9 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-992411537976371/9007199254740992), (-920816504965733/9007199254740992)), (719645/70368744177664), by norm_num⟩
  | 1 => ⟨((4159071011/17179869184), (3859025299/17179869184)), (97/4294967296), by norm_num⟩
  | 2 => ⟨((-2284603261/8589934592), (-529946577/2147483648)), (215/8589934592), by norm_num⟩
  | 3 => ⟨((1673262145/8589934592), (3105097717/17179869184)), (317/17179869184), by norm_num⟩
  | 4 => ⟨((-3676532709/34359738368), (-1705649255/17179869184)), (351/34359738368), by norm_num⟩
  | 5 => ⟨((3231267211/68719476736), (2998155571/68719476736)), (311/68719476736), by norm_num⟩
  | 6 => ⟨((-2366606577/137438953472), (-2195873703/137438953472)), (115/68719476736), by norm_num⟩
  | 7 => ⟨((2971409221/549755813888), (1378522191/274877906944)), (291/549755813888), by norm_num⟩
  | 8 => ⟨((-3264426685/2199023255552), (-3028922839/2199023255552)), (161/1099511627776), by norm_num⟩
  | 9 => ⟨((1593928565/4398046511104), (1478938601/4398046511104)), (317/8796093022208), by norm_num⟩
  | 10 => ⟨((-1400887607/17592186044416), (-1299824097/17592186044416)), (35/4398046511104), by norm_num⟩
  | 11 => ⟨((2238592495/140737488355328), (1038547437/70368744177664)), (113/70368744177664), by norm_num⟩
  | 12 => ⟨((-1639563483/562949953421312), (-3042562605/1125899906842624)), (333/1125899906842624), by norm_num⟩
  | 13 => ⟨((2216916419/4503599627370496), (4113965129/9007199254740992)), (453/9007199254740992), by norm_num⟩
  | 14 => ⟨((-1391732355/18014398509481984), (-2582658655/36028797018963968)), (143/18014398509481984), by norm_num⟩
  | 15 => ⟨((3261811771/288230376151711744), (756624143/72057594037927936)), (169/144115188075855872), by norm_num⟩
  | 16 => ⟨((-3583466495/2305843009213693952), (-1662473163/1152921504606846976)), (187/1152921504606846976), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-1558964388259/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889519285439989/316912650057057350374175801344), (-1845499892557/316912650057057350374175801344)), (4339/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890044958151939/39614081257132168796771975168), (-4151668469603/39614081257132168796771975168)), (9765/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944919221484149/1237940039285380274899124224), (-2205146569753/1237940039285380274899124224)), (41511/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885752046748369/77371252455336267181195264), (-551166472081/19342813113834066795298816)), (20761/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549846607525907/9671406556917033397649408), (-4132727233095/9671406556917033397649408)), (38939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629522291156335/302231454903657293676544), (-3615115179309/604462909807314587353088)), (34085/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888206689241997/75557863725914323419136), (-5872647846401/75557863725914323419136)), (55409/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297849394740179/4722366482869645213696), (-4402811190621/4722366482869645213696)), (41577/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202734074033323/73786976294838206464), (-6051144639065/590295810358705651712)), (3575/36893488147419103232), by norm_num⟩
  | 8 => ⟨((57000083737313/2305843009213693952), (-3779925390021/36893488147419103232)), (71549/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911623733139653/4611686018427387904), (-8499223895951/9223372036854775808)), (40279/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797245801628659/576460752303423488), (-8492216300305/1152921504606846976)), (40321/576460752303423488), by norm_num⟩
  | 5 => ⟨((597509190677123/72057594037927936), (-3711404712875/72057594037927936)), (69/140737488355328), by norm_num⟩
  | 4 => ⟨((1492284040001551/36028797018963968), (-11118463746891/36028797018963968)), (26543/9007199254740992), by norm_num⟩
  | 3 => ⟨((186256112469503/1125899906842624), (-3467634354097/2251799813685248)), (33261/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114739745143689/2251799813685248), (-13829265934681/2251799813685248)), (133539/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109137001349545/1125899906842624), (-5160216821067/281474976710656)), (201549/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092285245206599/1125899906842624), (-40870493555325/1125899906842624)), (408077/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092285245206599/1125899906842624), (-40870493555325/1125899906842624)), (1556690220359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((529095282987317/562949953421312), (-4956283947121/70368744177664)), (821415/1125899906842624), by norm_num⟩
  | 2 => ⟨((123620968769745/140737488355328), (-4658223065177/35184372088832)), (51867/35184372088832), by norm_num⟩
  | 3 => ⟨((106119268008137/140737488355328), (-261868102853783/1125899906842624)), (6710509/2251799813685248), by norm_num⟩
  | 4 => ⟨((1158447978314321/2251799813685248), (-789818028281473/2251799813685248)), (13241289/2251799813685248), by norm_num⟩
  | 5 => ⟨((159470037322441/1125899906842624), (-406325239276695/1125899906842624)), (22912831/2251799813685248), by norm_num⟩
  | 6 => ⟨((-992411537976371/9007199254740992), (-920816504965733/9007199254740992)), (719645/70368744177664), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-494443563/8388608)), (3/134217728), by norm_num⟩, -9, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-266553675/134217728), (-8290447061/134217728)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term10 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((600881322068383/9007199254740992), (1080342234406639/9007199254740992)), (61132077/9007199254740992), by norm_num⟩
  | 1 => ⟨((-329871267/2147483648), (-4744682167/17179869184)), (271/17179869184), by norm_num⟩
  | 2 => ⟨((379778331/2147483648), (2731258607/8589934592)), (157/8589934592), by norm_num⟩
  | 3 => ⟨((-2331925129/17179869184), (-2096318451/8589934592)), (243/17179869184), by norm_num⟩
  | 4 => ⟨((671182005/8589934592), (4826951615/34359738368)), (141/17179869184), by norm_num⟩
  | 5 => ⟨((-2472725887/68719476736), (-4445786733/68719476736)), (131/34359738368), by norm_num⟩
  | 6 => ⟨((1897887255/137438953472), (3412267419/137438953472)), (203/137438953472), by norm_num⟩
  | 7 => ⟨((-1248584829/274877906944), (-2244867455/274877906944)), (135/274877906944), by norm_num⟩
  | 8 => ⟨((1437486407/1099511627776), (5168998337/2199023255552)), (157/1099511627776), by norm_num⟩
  | 9 => ⟨((-1471082121/4398046511104), (-5289803785/8796093022208)), (81/2199023255552), by norm_num⟩
  | 10 => ⟨((1354916705/17592186044416), (609011167/4398046511104)), (301/35184372088832), by norm_num⟩
  | 11 => ⟨((-567238365/35184372088832), (-2039709141/70368744177664)), (127/70368744177664), by norm_num⟩
  | 12 => ⟨((870743069/281474976710656), (3131069241/562949953421312)), (197/562949953421312), by norm_num⟩
  | 13 => ⟨((-1233821545/2251799813685248), (-4436648221/4503599627370496)), (281/4503599627370496), by norm_num⟩
  | 14 => ⟨((1623416627/18014398509481984), (2918788587/18014398509481984)), (187/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1993629293/144115188075855872), (-224025303/9007199254740992)), (29/18014398509481984), by norm_num⟩
  | 16 => ⟨((2295250545/1152921504606846976), (4126698585/1152921504606846976)), (269/1152921504606846976), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790694403444907/5070602400912917605986812821504), (1384948507627/10141204801825835211973625643008)), (7279/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778904301995883/633825300114114700748351602688), (1639254322461/633825300114114700748351602688)), (8659/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889894265960409/39614081257132168796771975168), (1843839495875/39614081257132168796771975168)), (19485/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889678795916097/2475880078570760549798248448), (1958682497035/2475880078570760549798248448)), (20705/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221418120929141/19342813113834066795298816), (122389752893/9671406556917033397649408)), (41415/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549697980083971/9671406556917033397649408), (458843017475/2417851639229258349412352)), (2427/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258915086197647/604462909807314587353088), (1605476484395/604462909807314587353088)), (33983/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235999661750165/9444732965739290427392), (2608010704897/75557863725914323419136)), (863/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297693254027925/4722366482869645213696), (1955230830791/4722366482869645213696)), (20717/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621659369202513/590295810358705651712), (1343590014879/295147905179352825856)), (56985/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911869176989335/36893488147419103232), (3357082514815/73786976294838206464)), (17813/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911476562735795/4611686018427387904), (471764658739/1152921504606846976)), (20047/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797100519237471/576460752303423488), (3770869057813/1152921504606846976)), (80225/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597384188572885/72057594037927936), (823964901005/36028797018963968)), (70239/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491917493531907/36028797018963968), (4936496297899/36028797018963968)), (52721/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489605476208923/9007199254740992), (3078938307995/4503599627370496)), (131949/9007199254740992), by norm_num⟩
  | 2 => ⟨((278579592671507/562949953421312), (767349911859/281474976710656)), (264339/4503599627370496), by norm_num⟩
  | 1 => ⟨((554279873645677/562949953421312), (4580319750913/562949953421312)), (397613/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182696164884127/2251799813685248), (18131842539815/1125899906842624)), (799663/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182696164884127/2251799813685248), (18131842539815/1125899906842624)), (3050472268111418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2115129179955631/2251799813685248), (70301636821201/2251799813685248)), (788001/1125899906842624), by norm_num⟩
  | 2 => ⟨((1984558796301901/2251799813685248), (132069505055879/2251799813685248)), (95597/70368744177664), by norm_num⟩
  | 3 => ⟨((1741287674856171/2251799813685248), (232791295557429/2251799813685248)), (179717/70368744177664), by norm_num⟩
  | 4 => ⟨((165306156503159/281474976710656), (360028996631413/2251799813685248)), (10083329/2251799813685248), by norm_num⟩
  | 5 => ⟨((359545980936189/1125899906842624), (3303746701923/17592186044416)), (3766983/562949953421312), by norm_num⟩
  | 6 => ⟨((600881322068383/9007199254740992), (1080342234406639/9007199254740992)), (61132077/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-266553675/134217728), (-8290447061/134217728)), (3/134217728), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-34698381/16777216), (-4316805463/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term11 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((43928142987971/4503599627370496), (-1135251123970207/9007199254740992)), (22348939/2251799813685248), by norm_num⟩
  | 1 => ⟨((-200910733/8589934592), (5192209823/17179869184)), (411/17179869184), by norm_num⟩
  | 2 => ⟨((481762897/17179869184), (-6225187695/17179869184)), (495/17179869184), by norm_num⟩
  | 3 => ⟨((-96268081/4294967296), (4975782715/17179869184)), (199/8589934592), by norm_num⟩
  | 4 => ⟨((461681553/34359738368), (-5965702925/34359738368)), (15/1073741824), by norm_num⟩
  | 5 => ⟨((-442825605/68719476736), (5722052337/68719476736)), (463/68719476736), by norm_num⟩
  | 6 => ⟨((22121863/8589934592), (-4573627417/137438953472)), (93/34359738368), by norm_num⟩
  | 7 => ⟨((-30311949/34359738368), (6266902607/549755813888)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((290739517/1099511627776), (-1878422017/549755813888)), (77/274877906944), by norm_num⟩
  | 9 => ⟨((-38731273/549755813888), (2001893011/2199023255552)), (165/2199023255552), by norm_num⟩
  | 10 => ⟨((594390633/35184372088832), (-1920131915/8796093022208)), (159/8796093022208), by norm_num⟩
  | 11 => ⟨((-129571499/35184372088832), (6697127625/140737488355328)), (557/140737488355328), by norm_num⟩
  | 12 => ⟨((103566295/140737488355328), (-2676501779/281474976710656)), (447/562949953421312), by norm_num⟩
  | 13 => ⟨((-611301241/4503599627370496), (3949520593/2251799813685248)), (331/2251799813685248), by norm_num⟩
  | 14 => ⟨((418810387/18014398509481984), (-5411735291/18014398509481984)), (57/2251799813685248), by norm_num⟩
  | 15 => ⟨((-133901793/36028797018963968), (6920946385/144115188075855872)), (585/144115188075855872), by norm_num⟩
  | 16 => ⟨((80270619/144115188075855872), (-4148926155/576460752303423488)), (353/576460752303423488), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-972764963345/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889388083646431/316912650057057350374175801344), (-287807246155/79228162514264337593543950336)), (23107/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944875030502113/19807040628566084398385987584), (-2589793709157/39614081257132168796771975168)), (25999/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118095344165571/154742504910672534362390528), (-2751074972341/2475880078570760549798248448)), (6907/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885595798907045/77371252455336267181195264), (-2750421705683/154742504910672534362390528)), (55265/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549554110761509/9671406556917033397649408), (-1288913217509/4835703278458516698824704)), (25911/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258789115314059/604462909807314587353088), (-1127452210511/302231454903657293676544)), (45355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943896215840979/37778931862957161709568), (-3662919412957/75557863725914323419136)), (73719/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648769733887491/2361183241434822606848), (-1373026128313/2361183241434822606848)), (27653/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621447686706265/590295810358705651712), (-943493637307/147573952589676412928)), (9509/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911736705902101/36893488147419103232), (-4714698654887/73786976294838206464)), (47565/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911327300104083/4611686018427387904), (-2650115096725/4611686018427387904)), (107077/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398475483221747/288230376151711744), (-165483638101/36028797018963968)), (107147/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194506008706277/144115188075855872), (-4628198635793/144115188075855872)), (11729/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491522643302595/36028797018963968), (-6931623395863/36028797018963968)), (17613/4503599627370496), by norm_num⟩
  | 3 => ⟨((1489109652846103/9007199254740992), (-4322937765369/4503599627370496)), (176405/9007199254740992), by norm_num⟩
  | 2 => ⟨((556909588374653/1125899906842624), (-17235896855455/4503599627370496)), (353633/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215605201463733/2251799813685248), (-3214322942527/281474976710656)), (133129/562949953421312), by norm_num⟩
  | 0 => ⟨((2179601579008867/2251799813685248), (-50874358703261/2251799813685248)), (1073333/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179601579008867/2251799813685248), (-50874358703261/2251799813685248)), (4094440468795012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2108568805267765/2251799813685248), (-98486403530887/2251799813685248)), (2126339/2251799813685248), by norm_num⟩
  | 2 => ⟨((1970140865944661/2251799813685248), (-46110972424405/562949953421312)), (260511/140737488355328), by norm_num⟩
  | 3 => ⟨((1708604583691549/2251799813685248), (-161373334502755/1125899906842624)), (7976455/2251799813685248), by norm_num⟩
  | 4 => ⟨((1250184050086753/2251799813685248), (-489782825882295/2251799813685248)), (3597785/562949953421312), by norm_num⟩
  | 5 => ⟨((587562417636387/2251799813685248), (-543848234823641/2251799813685248)), (5560021/562949953421312), by norm_num⟩
  | 6 => ⟨((43928142987971/4503599627370496), (-1135251123970207/9007199254740992)), (22348939/2251799813685248), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-4316805463/67108864)), (1/33554432), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17978733/8388608), (-4473447495/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term12 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-817288493502739/9007199254740992), (334609373241101/4503599627370496)), (96123089/9007199254740992), by norm_num⟩
  | 1 => ⟨((242100431/1073741824), (-792954499/4294967296)), (229/8589934592), by norm_num⟩
  | 2 => ⟨((-601596971/2147483648), (1970417907/8589934592)), (287/8589934592), by norm_num⟩
  | 3 => ⟨((996608209/4294967296), (-102006345/536870912)), (239/8589934592), by norm_num⟩
  | 4 => ⟨((-1238239183/8589934592), (253476245/2147483648)), (299/17179869184), by norm_num⟩
  | 5 => ⟨((153845439/2147483648), (-1007783691/17179869184)), (299/34359738368), by norm_num⟩
  | 6 => ⟨((-1019444145/34359738368), (834749465/34359738368)), (249/68719476736), by norm_num⟩
  | 7 => ⟨((2895112611/274877906944), (-4630077/536870912)), (89/68719476736), by norm_num⟩
  | 8 => ⟨((-3597042289/1099511627776), (92042473/34359738368)), (445/1099511627776), by norm_num⟩
  | 9 => ⟨((3972584135/4398046511104), (-3252863335/4398046511104)), (247/2199023255552), by norm_num⟩
  | 10 => ⟨((-3948600293/17592186044416), (3233224693/17592186044416)), (247/8796093022208), by norm_num⟩
  | 11 => ⟨((3567964773/70368744177664), (-2921549651/70368744177664)), (449/70368744177664), by norm_num⟩
  | 12 => ⟨((-1477676565/140737488355328), (604981513/70368744177664)), (187/140737488355328), by norm_num⟩
  | 13 => ⟨((2259623583/1125899906842624), (-1850243181/1125899906842624)), (287/1125899906842624), by norm_num⟩
  | 14 => ⟨((-3208544953/9007199254740992), (2627246619/9007199254740992)), (205/4503599627370496), by norm_num⟩
  | 15 => ⟨((2126115917/36028797018963968), (-3481846717/72057594037927936)), (273/36028797018963968), by norm_num⟩
  | 16 => ⟨((-1320799895/144115188075855872), (2163016015/288230376151711744)), (341/288230376151711744), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (799632964661/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778655650124305/633825300114114700748351602688), (3784867527855/633825300114114700748351602688)), (46287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944807116015669/19807040628566084398385987584), (4257162796165/39614081257132168796771975168)), (52085/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472345215797909/618970019642690137449562112), (4522244744125/2475880078570760549798248448)), (27677/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885523294426675/77371252455336267181195264), (4521130326417/154742504910672534362390528)), (27685/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549417776787219/9671406556917033397649408), (4237375832727/9671406556917033397649408)), (25963/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258669435320675/604462909807314587353088), (3706520253113/604462909807314587353088)), (11363/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887597225285271/75557863725914323419136), (6020876686955/75557863725914323419136)), (73889/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297392428024191/4722366482869645213696), (4513716658173/4722366482869645213696)), (55445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810622238236957/295147905179352825856), (3101603750135/295147905179352825856)), (9535/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911608927645921/36893488147419103232), (7749281747807/73786976294838206464)), (11927/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455591244997443/2305843009213693952), (8711444290033/9223372036854775808)), (53717/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796804834474827/576460752303423488), (8703326414031/1152921504606846976)), (107549/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194247310731039/144115188075855872), (7606283806409/144115188075855872)), (47117/72057594037927936), by norm_num⟩
  | 4 => ⟨((745564340069951/18014398509481984), (2847796654667/9007199254740992)), (17701/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488606885662629/9007199254740992), (14207097561133/9007199254740992)), (88731/4503599627370496), by norm_num⟩
  | 2 => ⟨((139162627474343/281474976710656), (7079667224637/1125899906842624)), (44535/562949953421312), by norm_num⟩
  | 1 => ⟨((553493585194437/562949953421312), (21119823270961/1125899906842624)), (67227/281474976710656), by norm_num⟩
  | 0 => ⟨((1088018820335499/1125899906842624), (10441077850277/281474976710656)), (544639/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088018820335499/1125899906842624), (10441077850277/281474976710656)), (2077632908347701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049863037125791/1125899906842624), (40359144313447/562949953421312)), (273259/281474976710656), by norm_num⟩
  | 2 => ⟨((973174389610541/1125899906842624), (150534069919365/1125899906842624)), (1097581/562949953421312), by norm_num⟩
  | 3 => ⟨((821039135689859/1125899906842624), (65057249191977/281474976710656)), (4381779/1125899906842624), by norm_num⟩
  | 4 => ⟨((1077158152141633/2251799813685248), (189766594072227/562949953421312)), (16832325/2251799813685248), by norm_num⟩
  | 5 => ⟨((518774286739901/4503599627370496), (1452410698796679/4503599627370496)), (27451755/2251799813685248), by norm_num⟩
  | 6 => ⟨((-817288493502739/9007199254740992), (334609373241101/4503599627370496)), (96123089/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-4473447495/67108864)), (1/33554432), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-148462847/67108864), (-1154386049/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term13 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((469691782395639/4503599627370496), (74779355364741/2251799813685248)), (40211059/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2297850867/8589934592), (-731678999/8589934592)), (199/17179869184), by norm_num⟩
  | 2 => ⟨((5893871105/17179869184), (938359789/8589934592)), (129/8589934592), by norm_num⟩
  | 3 => ⟨((-5039160301/17179869184), (-1604563559/17179869184)), (223/17179869184), by norm_num⟩
  | 4 => ⟨((201956109/1073741824), (2057812135/34359738368)), (9/1073741824), by norm_num⟩
  | 5 => ⟨((-3315246029/34359738368), (-1055636783/34359738368)), (75/17179869184), by norm_num⟩
  | 6 => ⟨((5668958781/137438953472), (1805103259/137438953472)), (259/137438953472), by norm_num⟩
  | 7 => ⟨((-4154454909/274877906944), (-661428349/137438953472)), (3/4294967296), by norm_num⟩
  | 8 => ⟨((5327983225/1099511627776), (1696530219/1099511627776)), (249/1099511627776), by norm_num⟩
  | 9 => ⟨((-6073780955/4398046511104), (-241750783/549755813888)), (287/4398046511104), by norm_num⟩
  | 10 => ⟨((6231576223/17592186044416), (992125625/8796093022208)), (297/17592186044416), by norm_num⟩
  | 11 => ⟨((-2906123169/35184372088832), (-462682179/17592186044416)), (279/70368744177664), by norm_num⟩
  | 12 => ⟨((4969372503/281474976710656), (791170905/140737488355328)), (241/281474976710656), by norm_num⟩
  | 13 => ⟨((-3921904249/1125899906842624), (-1248808187/1125899906842624)), (3/17592186044416), by norm_num⟩
  | 14 => ⟨((2874138795/4503599627370496), (1830359861/9007199254740992)), (71/2251799813685248), by norm_num⟩
  | 15 => ⟨((-3931744243/36028797018963968), (-625970713/18014398509481984)), (49/9007199254740992), by norm_num⟩
  | 16 => ⟨((5042362435/288230376151711744), (802791589/144115188075855872)), (253/288230376151711744), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039973471/10141204801825835211973625643008), (200776740675/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889278395938465/316912650057057350374175801344), (475109711751/633825300114114700748351602688)), (11531/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889503463623517/39614081257132168796771975168), (66799446439/4951760157141521099596496896)), (51891/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944631877252235/1237940039285380274899124224), (283833602043/1237940039285380274899124224)), (1723/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770930135227973/154742504910672534362390528), (567523160683/154742504910672534362390528)), (27569/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549309297069625/9671406556917033397649408), (132974992111/2417851639229258349412352)), (25847/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629287605310579/302231454903657293676544), (116314883889/151115727451828646838272)), (22617/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887445412305693/75557863725914323419136), (377880055811/37778931862957161709568)), (73509/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324319926652417/1180591620717411303424), (2213161727/18446744073709551616)), (1723/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810545666149629/295147905179352825856), (389312900249/295147905179352825856)), (75817/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227878649153961/9223372036854775808), (486335981053/36893488147419103232)), (94779/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822156535711341/9223372036854775808), (273354366095/2305843009213693952)), (53319/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99587872927279/72057594037927936), (546185163935/576460752303423488)), (106653/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194074394632147/144115188075855872), (477323677023/72057594037927936)), (46669/72057594037927936), by norm_num⟩
  | 4 => ⟨((372719980829771/9007199254740992), (1429621025557/36028797018963968)), (17505/4503599627370496), by norm_num⟩
  | 3 => ⟨((744157227217647/4503599627370496), (1782921321229/9007199254740992)), (43777/2251799813685248), by norm_num⟩
  | 2 => ⟨((556518115000971/1125899906842624), (3553557898909/4503599627370496)), (350389/4503599627370496), by norm_num⟩
  | 1 => ⟨((276664658224203/281474976710656), (5299730217981/2251799813685248)), (263013/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087633606055175/1125899906842624), (10477663237417/2251799813685248)), (526921/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087633606055175/1125899906842624), (10477663237417/2251799813685248)), (2010044102195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525321748618459/562949953421312), (10121555726833/1125899906842624)), (1022929/1125899906842624), by norm_num⟩
  | 2 => ⟨((1960652640057763/2251799813685248), (9445019616477/562949953421312)), (1927503/1125899906842624), by norm_num⟩
  | 3 => ⟨((853257784569147/1125899906842624), (65790582391553/2251799813685248)), (6842501/2251799813685248), by norm_num⟩
  | 4 => ⟨((322838088149255/562949953421312), (12464768456717/281474976710656)), (10770947/2251799813685248), by norm_num⟩
  | 5 => ⟨((368071615316793/1125899906842624), (7148241141745/140737488355328)), (3326927/562949953421312), by norm_num⟩
  | 6 => ⟨((469691782395639/4503599627370496), (74779355364741/2251799813685248)), (40211059/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148462847/67108864), (-1154386049/16777216)), (1/33554432), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2386755/1048576), (-2375478451/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term14 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-201099969569051/18014398509481984), (-1838663014747895/18014398509481984)), (4806697/562949953421312), by norm_num⟩
  | 1 => ⟨((126532161/4294967296), (578443659/2147483648)), (389/17179869184), by norm_num⟩
  | 2 => ⟨((-333925627/8589934592), (-763272989/2147483648)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((587499249/17179869184), (83930049/268435456)), (57/2147483648), by norm_num⟩
  | 4 => ⟨((-193805525/8589934592), (-7087878751/34359738368)), (151/8589934592), by norm_num⟩
  | 5 => ⟨((409171113/34359738368), (7482127347/68719476736)), (5/536870912), by norm_num⟩
  | 6 => ⟨((-44992751/8589934592), (-6581921005/137438953472)), (565/137438953472), by norm_num⟩
  | 7 => ⟨((135701085/68719476736), (620359531/34359738368)), (107/68719476736), by norm_num⟩
  | 8 => ⟨((-358122943/549755813888), (-6548657469/1099511627776)), (567/1099511627776), by norm_num⟩
  | 9 => ⟨((840095091/4398046511104), (7681014441/4398046511104)), (167/1099511627776), by norm_num⟩
  | 10 => ⟨((-443411821/8796093022208), (-1013531873/2199023255552)), (355/8796093022208), by norm_num⟩
  | 11 => ⟨((425523351/35184372088832), (3890572681/35184372088832)), (343/35184372088832), by norm_num⟩
  | 12 => ⟨((-748653679/281474976710656), (-1711240725/70368744177664)), (303/140737488355328), by norm_num⟩
  | 13 => ⟨((607919993/1125899906842624), (5558230619/1125899906842624)), (247/562949953421312), by norm_num⟩
  | 14 => ⟨((-7162213/70368744177664), (-2095498465/2251799813685248)), (375/4503599627370496), by norm_num⟩
  | 15 => ⟨((645170883/36028797018963968), (2949408311/18014398509481984)), (265/18014398509481984), by norm_num⟩
  | 16 => ⟨((-425660737/144115188075855872), (-1945914405/72057594037927936)), (351/144115188075855872), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-2188043999707/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889227408337659/316912650057057350374175801344), (-647143727851/158456325028528675187087900672)), (46229/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944694284756525/19807040628566084398385987584), (-2911565362547/39614081257132168796771975168)), (52015/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944570725919357/1237940039285380274899124224), (-3092819521275/2475880078570760549798248448)), (55275/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885403788342835/77371252455336267181195264), (-3092011258713/154742504910672534362390528)), (27643/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549194126768711/9671406556917033397649408), (-181118876333/604462909807314587353088)), (25921/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258474165166971/604462909807314587353088), (-1267403005393/302231454903657293676544)), (45373/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887280704972227/75557863725914323419136), (-1029362780005/18889465931478580854784)), (9219/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648577865839431/2361183241434822606848), (-3086681359283/4722366482869645213696)), (55333/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202615018183807/73786976294838206464), (-2120950811703/295147905179352825856)), (76113/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822814129322465/73786976294838206464), (-5298951081759/73786976294838206464)), (47593/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821913105857209/9223372036854775808), (-5956612409287/9223372036854775808)), (107147/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796580343558779/576460752303423488), (-5950732639957/1152921504606846976)), (107225/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193857699039377/144115188075855872), (-325017671721/9007199254740992)), (46955/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490550741376799/36028797018963968), (-7787223554969/36028797018963968)), (141041/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487895764004551/9007199254740992), (-9710964552225/9007199254740992)), (88305/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225213557671473/4503599627370496), (-19352878668077/4503599627370496)), (88537/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211975518551035/2251799813685248), (-28857196022999/2251799813685248)), (266775/1125899906842624), by norm_num⟩
  | 0 => ⟨((543093147672463/562949953421312), (-57028923027881/2251799813685248)), (1076449/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543093147672463/562949953421312), (-57028923027881/2251799813685248)), (4106327065474700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094302675600987/2251799813685248), (-27508677394279/562949953421312)), (532871/562949953421312), by norm_num⟩
  | 2 => ⟨((1942444454047335/2251799813685248), (-51169288068105/562949953421312)), (1043279/562949953421312), by norm_num⟩
  | 3 => ⟨((1656984647445415/2251799813685248), (-88279161603425/562949953421312)), (3979123/1125899906842624), by norm_num⟩
  | 4 => ⟨((36372387822383/70368744177664), (-129920266070929/562949953421312)), (14208085/2251799813685248), by norm_num⟩
  | 5 => ⟨((120418453167617/562949953421312), (-537228323027991/2251799813685248)), (42491693/4503599627370496), by norm_num⟩
  | 6 => ⟨((-201099969569051/18014398509481984), (-1838663014747895/18014398509481984)), (4806697/562949953421312), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-2375478451/33554432)), (1/33554432), by norm_num⟩, -11, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

private theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-39186431/16777216), (-4875161161/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
private theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term15 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-100788412152941/1125899906842624), (82607423939965/2251799813685248)), (77483631/9007199254740992), by norm_num⟩
  | 1 => ⟨((32536993/134217728), (-1706734093/17179869184)), (201/8589934592), by norm_num⟩
  | 2 => ⟨((-1409788967/4294967296), (1155480401/8589934592)), (273/8589934592), by norm_num⟩
  | 3 => ⟨((2545186197/8589934592), (-2086065955/17179869184)), (495/17179869184), by norm_num⟩
  | 4 => ⟨((-861561499/4294967296), (44134151/536870912)), (337/17179869184), by norm_num⟩
  | 5 => ⟨((3733042865/34359738368), (-1529823955/34359738368)), (367/34359738368), by norm_num⟩
  | 6 => ⟨((-3369755827/68719476736), (690473345/34359738368)), (333/68719476736), by norm_num⟩
  | 7 => ⟨((651819139/34359738368), (-1068477989/137438953472)), (259/137438953472), by norm_num⟩
  | 8 => ⟨((-3530317901/549755813888), (1446746017/549755813888)), (353/549755813888), by norm_num⟩
  | 9 => ⟨((2124506245/1099511627776), (-870635743/1099511627776)), (427/2199023255552), by norm_num⟩
  | 10 => ⟨((-4602615651/8796093022208), (1886180239/8796093022208)), (465/8796093022208), by norm_num⟩
  | 11 => ⟨((2266202589/17592186044416), (-1857407555/35184372088832)), (115/8796093022208), by norm_num⟩
  | 12 => ⟨((-2045663459/70368744177664), (209581371/17592186044416)), (417/140737488355328), by norm_num⟩
  | 13 => ⟨((213067667/35184372088832), (-698531537/281474976710656)), (349/562949953421312), by norm_num⟩
  | 14 => ⟨((-5275409723/4503599627370496), (2161895393/4503599627370496)), (543/4503599627370496), by norm_num⟩
  | 15 => ⟨((1904809915/9007199254740992), (-390301417/4503599627370496)), (197/9007199254740992), by norm_num⟩
  | 16 => ⟨((-2579160437/72057594037927936), (1056955831/72057594037927936)), (67/18014398509481984), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (3585648783831/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778357068742339/633825300114114700748351602688), (4241600556113/633825300114114700748351602688)), (23155/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889278287653209/39614081257132168796771975168), (4770808344893/39614081257132168796771975168)), (3257/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944511929628531/1237940039285380274899124224), (633471708205/309485009821345068724781056)), (6923/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770689514177149/154742504910672534362390528), (2533206180901/77371252455336267181195264)), (27701/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549082944245475/9671406556917033397649408), (1187078871199/2417851639229258349412352)), (51957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629188190980137/302231454903657293676544), (4153330260299/604462909807314587353088)), (22741/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887120873473611/75557863725914323419136), (6746451489457/75557863725914323419136)), (36971/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648517520943881/2361183241434822606848), (5057467877409/4722366482869645213696)), (867/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1620752872417121/590295810358705651712), (1737541784481/147573952589676412928)), (9543/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822603054059563/73786976294838206464), (271310447985/2305843009213693952)), (5969/4611686018427387904), by norm_num⟩
  | 7 => ⟨((455418230758297/2305843009213693952), (9759239652971/9223372036854775808)), (107545/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592917107504053/1152921504606846976), (9749324437021/1152921504606846976)), (107673/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298410188827981/36028797018963968), (8519511663625/144115188075855872)), (94359/144115188075855872), by norm_num⟩
  | 4 => ⟨((186277215896989/4503599627370496), (12756991572503/36028797018963968)), (141827/36028797018963968), by norm_num⟩
  | 3 => ⟨((23241660215069/140737488355328), (7953649151971/4503599627370496)), (177789/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112157514779127/2251799813685248), (7924485040793/1125899906842624)), (89275/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105264862284679/1125899906842624), (11813963696493/562949953421312)), (269733/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084546790959239/1125899906842624), (46675504835981/1125899906842624)), (68391/140737488355328), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084546790959239/1125899906842624), (46675504835981/1125899906842624)), (260890961230230287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1042777543450315/1125899906842624), (22480581390323/281474976710656)), (549715/562949953421312), by norm_num⟩
  | 2 => ⟨((1917220125750991/2251799813685248), (333134344110929/2251799813685248)), (2212141/1125899906842624), by norm_num⟩
  | 3 => ⟨((395767254452831/562949953421312), (567272334979955/2251799813685248)), (8842885/2251799813685248), by norm_num⟩
  | 4 => ⟨((970028330158579/2251799813685248), (797611983721195/2251799813685248)), (8444455/1125899906842624), by norm_num⟩
  | 5 => ⟨((135345106115717/2251799813685248), (687189168398865/2251799813685248)), (26515251/2251799813685248), by norm_num⟩
  | 6 => ⟨((-100788412152941/1125899906842624), (82607423939965/2251799813685248)), (77483631/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-4875161161/67108864)), (1/33554432), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 16 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile039Terms1
