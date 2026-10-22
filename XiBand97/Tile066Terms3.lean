/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile066Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨66,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (81741/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (81741/2560))
  have he : value ((69/80), (81741/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-11450486389/4294967296), (-423901362271/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-325554324028789/18014398509481984), (1209457923925657/18014398509481984)), (424287/4503599627370496), by norm_num⟩
  | 1 => ⟨((15354953559/274877906944), (-114089532117/549755813888)), (161/549755813888), by norm_num⟩
  | 2 => ⟨((-5932851665/68719476736), (352655587257/1099511627776)), (125/274877906944), by norm_num⟩
  | 3 => ⟨((97806380619/1099511627776), (-45419724651/137438953472)), (259/549755813888), by norm_num⟩
  | 4 => ⟨((-18895229669/274877906944), (35098574279/137438953472)), (201/549755813888), by norm_num⟩
  | 5 => ⟨((93449531317/2199023255552), (-86792946519/549755813888)), (499/2199023255552), by norm_num⟩
  | 6 => ⟨((-24071372379/1099511627776), (44713447057/549755813888)), (129/1099511627776), by norm_num⟩
  | 7 => ⟨((42517505105/4398046511104), (-157955614959/4398046511104)), (229/4398046511104), by norm_num⟩
  | 8 => ⟨((-65711706645/17592186044416), (15257734737/1099511627776)), (89/4398046511104), by norm_num⟩
  | 9 => ⟨((22568630547/17592186044416), (-335376396901/70368744177664)), (491/70368744177664), by norm_num⟩
  | 10 => ⟨((-13952119027/35184372088832), (207332536135/140737488355328)), (609/281474976710656), by norm_num⟩
  | 11 => ⟨((62729588693/562949953421312), (-233044971329/562949953421312)), (43/70368744177664), by norm_num⟩
  | 12 => ⟨((-64633273911/2251799813685248), (240117299973/2251799813685248)), (89/562949953421312), by norm_num⟩
  | 13 => ⟨((15368014889/2251799813685248), (-228373159385/9007199254740992)), (85/2251799813685248), by norm_num⟩
  | 14 => ⟨((-27144677969/18014398509481984), (403377789067/72057594037927936)), (603/72057594037927936), by norm_num⟩
  | 15 => ⟨((89499042117/288230376151711744), (-332495432199/288230376151711744)), (499/288230376151711744), by norm_num⟩
  | 16 => ⟨((-8645166835/144115188075855872), (256939374119/1152921504606846976)), (97/288230376151711744), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486515511/5070602400912917605986812821504), (1194324170831/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1777853559090583/633825300114114700748351602688), (1412041013327/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888712265475913/39614081257132168796771975168), (99261119573/1237940039285380274899124224)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944211504826571/1237940039285380274899124224), (3373959967023/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442522320437025/38685626227668133590597632), (1686463754621/77371252455336267181195264)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12097819388439/75557863725914323419136), (3161022930969/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257885232210119/604462909807314587353088), (2764798880199/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943161991145899/37778931862957161709568), (2245371868215/37778931862957161709568)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162054805797735/590295810358705651712), (210391316589/295147905179352825856)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619934295366045/590295810358705651712), (4625690957089/590295810358705651712)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821582442494381/73786976294838206464), (5777739639867/73786976294838206464)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910264159354091/4611686018427387904), (6493947566785/9223372036854775808)), (419/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795888487856865/576460752303423488), (810805356411/144115188075855872)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((596324080940339/72057594037927936), (2833602287321/72057594037927936)), (1469/144115188075855872), by norm_num⟩
  | 4 => ⟨((744369428267417/18014398509481984), (8483965709681/36028797018963968)), (2207/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485635145073405/9007199254740992), (10575540604257/9007199254740992)), (2763/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220705033263199/4503599627370496), (21063053220851/4503599627370496)), (5541/4503599627370496), by norm_num⟩
  | 1 => ⟨((551311130584927/562949953421312), (31375284044037/2251799813685248)), (8351/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159037796096703/2251799813685248), (30939009194281/1125899906842624)), (8431/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159037796096703/2251799813685248), (30939009194281/1125899906842624)), (32161716941451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2068396705385573/2251799813685248), (118657954971433/2251799813685248)), (33263/2251799813685248), by norm_num⟩
  | 2 => ⟨((946839322629043/1125899906842624), (217987159994505/2251799813685248)), (32307/1125899906842624), by norm_num⟩
  | 3 => ⟨((1571409850946295/2251799813685248), (366637946511307/2251799813685248)), (121187/2251799813685248), by norm_num⟩
  | 4 => ⟨((1036906354480851/2251799813685248), (63964220684397/281474976710656)), (52151/562949953421312), by norm_num⟩
  | 5 => ⟨((722376656435473/4503599627370496), (471266807885703/2251799813685248)), (286925/2251799813685248), by norm_num⟩
  | 6 => ⟨((-325554324028789/18014398509481984), (1209457923925657/18014398509481984)), (424287/4503599627370496), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-11450486389/4294967296), (-423901362271/4294967296)), (1/2147483648), by norm_num⟩, -16, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-11615153911/4294967296), (-214998708297/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((275843344400907/4503599627370496), (485329897472595/18014398509481984)), (420995/9007199254740992), by norm_num⟩
  | 1 => ⟨((-52789624687/274877906944), (-46440096629/549755813888)), (163/1099511627776), by norm_num⟩
  | 2 => ⟨((165521562867/549755813888), (145612654367/1099511627776)), (129/549755813888), by norm_num⟩
  | 3 => ⟨((-86498650497/274877906944), (-152189211845/1099511627776)), (17/68719476736), by norm_num⟩
  | 4 => ⟨((271216018319/1099511627776), (119297098367/1099511627776)), (215/1099511627776), by norm_num⟩
  | 5 => ⟨((-340158502683/2199023255552), (-149622144763/2199023255552)), (17/137438953472), by norm_num⟩
  | 6 => ⟨((177760836277/2199023255552), (156379789827/4398046511104)), (287/4398046511104), by norm_num⟩
  | 7 => ⟨((-159248021133/4398046511104), (-140093693283/8796093022208)), (259/8796093022208), by norm_num⟩
  | 8 => ⟨((62415156145/4398046511104), (27453935311/4398046511104)), (205/17592186044416), by norm_num⟩
  | 9 => ⟨((-347915308585/70368744177664), (-153034053995/70368744177664)), (287/70368744177664), by norm_num⟩
  | 10 => ⟨((54544321885/35184372088832), (23991869557/35184372088832)), (91/70368744177664), by norm_num⟩
  | 11 => ⟨((-248761317501/562949953421312), (-27355042991/140737488355328)), (209/562949953421312), by norm_num⟩
  | 12 => ⟨((259996557391/2251799813685248), (114362105433/2251799813685248)), (55/562949953421312), by norm_num⟩
  | 13 => ⟨((-250836215957/9007199254740992), (-27583209239/2251799813685248)), (107/4503599627370496), by norm_num⟩
  | 14 => ⟨((224713001223/36028797018963968), (6177642359/2251799813685248)), (97/18014398509481984), by norm_num⟩
  | 15 => ⟨((-375779368309/288230376151711744), (-20661292677/36028797018963968)), (327/288230376151711744), by norm_num⟩
  | 16 => ⟨((147281754475/576460752303423488), (129566727365/1152921504606846976)), (129/576460752303423488), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395113257840647/2535301200456458802993406410752), (8434199573/158456325028528675187087900672)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777798574334151/633825300114114700748351602688), (159537006147/158456325028528675187087900672)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59020332655513/1237940039285380274899124224), (717749537547/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472089463658961/618970019642690137449562112), (47649914833/154742504910672534362390528)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770024482688481/154742504910672534362390528), (381081117155/77371252455336267181195264)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774230255253725/4835703278458516698824704), (357138009705/4835703278458516698824704)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257832784967513/604462909807314587353088), (624740557615/604462909807314587353088)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886239462747759/75557863725914323419136), (507366551715/37778931862957161709568)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296375674830673/4722366482869645213696), (760638558687/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809924493783475/295147905179352825856), (32662817723/18446744073709551616)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821477310029167/73786976294838206464), (1305511738233/73786976294838206464)), (1483/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820412106523737/9223372036854775808), (1467325679211/9223372036854775808)), (417/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591663335134589/1152921504606846976), (732804428419/576460752303423488)), (417/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192551611615035/144115188075855872), (1280479016865/144115188075855872)), (365/36028797018963968), by norm_num⟩
  | 4 => ⟨((744299891060913/18014398509481984), (958433890077/18014398509481984)), (1095/18014398509481984), by norm_num⟩
  | 3 => ⟨((742735661262457/4503599627370496), (2389361014637/9007199254740992)), (1369/4503599627370496), by norm_num⟩
  | 2 => ⟨((277550909386981/562949953421312), (2379305566097/2251799813685248)), (685/562949953421312), by norm_num⟩
  | 1 => ⟨((551217998559771/562949953421312), (442990603231/140737488355328)), (4115/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158585547265711/2251799813685248), (13976687308365/2251799813685248)), (1031/140737488355328), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158585547265711/2251799813685248), (13976687308365/2251799813685248)), (3932953417730287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2069143175498797/2251799813685248), (6699058024415/562949953421312)), (3979/281474976710656), by norm_num⟩
  | 2 => ⟨((1900984011386437/2251799813685248), (6155658291313/281474976710656)), (29629/1125899906842624), by norm_num⟩
  | 3 => ⟨((1603746076069127/2251799813685248), (20786586658773/562949953421312)), (102645/2251799813685248), by norm_num⟩
  | 4 => ⟨((1139127974857761/2251799813685248), (118434708400905/2251799813685248)), (76895/1125899906842624), by norm_num⟩
  | 5 => ⟨((1140053174486099/4503599627370496), (14978273014509/281474976710656)), (171775/2251799813685248), by norm_num⟩
  | 6 => ⟨((275843344400907/4503599627370496), (485329897472595/18014398509481984)), (420995/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-11615153911/4294967296), (-214998708297/2147483648)), (1/2147483648), by norm_num⟩, -16, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-5886406071/2147483648), (-217916992145/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((340517615680559/9007199254740992), (-470722748021917/9007199254740992)), (1141075/18014398509481984), by norm_num⟩
  | 1 => ⟨((-66051227589/549755813888), (91307509301/549755813888)), (223/1099511627776), by norm_num⟩
  | 2 => ⟨((209914356839/1099511627776), (-145090089837/549755813888)), (357/1099511627776), by norm_num⟩
  | 3 => ⟨((-222373041933/1099511627776), (307402743835/1099511627776)), (95/274877906944), by norm_num⟩
  | 4 => ⟨((44169593605/274877906944), (-61058904219/274877906944)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((-112298676913/1099511627776), (19404848443/137438953472)), (389/2199023255552), by norm_num⟩
  | 6 => ⟨((118963746769/2199023255552), (-164452407791/2199023255552)), (207/2199023255552), by norm_num⟩
  | 7 => ⟨((-216041823481/8796093022208), (298650631137/8796093022208)), (189/4398046511104), by norm_num⟩
  | 8 => ⟨((171648136157/17592186044416), (-237281945555/17592186044416)), (303/17592186044416), by norm_num⟩
  | 9 => ⟨((-15152972683/4398046511104), (167576621321/35184372088832)), (27/4398046511104), by norm_num⟩
  | 10 => ⟨((38525570301/35184372088832), (-213027009307/140737488355328)), (277/140737488355328), by norm_num⟩
  | 11 => ⟨((-44522304095/140737488355328), (123092964163/281474976710656)), (161/281474976710656), by norm_num⟩
  | 12 => ⟨((94329519377/1125899906842624), (-130398688749/1125899906842624)), (343/2251799813685248), by norm_num⟩
  | 13 => ⟨((-46120660057/2251799813685248), (255024032155/9007199254740992)), (169/4503599627370496), by norm_num⟩
  | 14 => ⟨((163586987/35184372088832), (-57891435873/9007199254740992)), (309/36028797018963968), by norm_num⟩
  | 15 => ⟨((-141964151639/144115188075855872), (98123786411/72057594037927936)), (263/144115188075855872), by norm_num⟩
  | 16 => ⟨((28198107243/144115188075855872), (-77960668813/288230376151711744)), (105/288230376151711744), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790202607763683/5070602400912917605986812821504), (-1230371639793/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888870565422629/316912650057057350374175801344), (-181809917101/79228162514264337593543950336)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888585986033827/39614081257132168796771975168), (-817951484409/19807040628566084398385987584)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944144553061913/1237940039285380274899124224), (-868830559271/1237940039285380274899124224)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769955679825597/154742504910672534362390528), (-1737114886167/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((96774746883365/604462909807314587353088), (-813982533697/4835703278458516698824704)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628888118508225/302231454903657293676544), (-1423889558395/604462909807314587353088)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235768433052633/9444732965739290427392), (-2312733823877/75557863725914323419136)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648153290903325/2361183241434822606848), (-108350003489/295147905179352825856)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1619753831715757/590295810358705651712), (-297769608117/73786976294838206464)), (297/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821358136255243/73786976294838206464), (-1487691545685/36893488147419103232)), (1485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820277721946155/9223372036854775808), (-836032146161/2305843009213693952)), (1671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591528559059715/1152921504606846976), (-417520161309/144115188075855872)), (1671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74527077726971/9007199254740992), (-2918184030931/144115188075855872)), (183/18014398509481984), by norm_num⟩
  | 4 => ⟨((744210678046325/18014398509481984), (-4368377097419/36028797018963968)), (2197/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485246768878607/9007199254740992), (-2722466229027/4503599627370496)), (687/2251799813685248), by norm_num⟩
  | 2 => ⟨((138747102392931/281474976710656), (-10843384864173/4503599627370496)), (5503/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204180333020265/2251799813685248), (-16149354237133/2251799813685248)), (8275/2251799813685248), by norm_num⟩
  | 0 => ⟨((539289525762871/562949953421312), (-31838667957221/2251799813685248)), (16633/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((539289525762871/562949953421312), (-31838667957221/2251799813685248)), (63449868209075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066043949603807/2251799813685248), (-61001018080629/2251799813685248)), (32339/2251799813685248), by norm_num⟩
  | 2 => ⟨((1893958979643007/2251799813685248), (-27984455713871/562949953421312)), (7637/281474976710656), by norm_num⟩
  | 3 => ⟨((396854831262145/562949953421312), (-94149419264703/1125899906842624)), (108849/2251799813685248), by norm_num⟩
  | 4 => ⟨((275828655576645/562949953421312), (-66371178589937/562949953421312)), (171673/2251799813685248), by norm_num⟩
  | 5 => ⟨((509290841604597/2251799813685248), (-130079577044027/1125899906842624)), (104355/1125899906842624), by norm_num⟩
  | 6 => ⟨((340517615680559/9007199254740992), (-470722748021917/9007199254740992)), (1141075/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5886406071/2147483648), (-217916992145/2147483648)), (1/2147483648), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-5962016759/2147483648), (-220716128577/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-351450070303989/9007199254740992), (-874217906239175/18014398509481984)), (803235/9007199254740992), by norm_num⟩
  | 1 => ⟨((17261873397/137438953472), (21469107697/137438953472)), (317/1099511627776), by norm_num⟩
  | 2 => ⟨((-111127653939/549755813888), (-276425566989/1099511627776)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((119235372913/549755813888), (74148297913/274877906944)), (551/1099511627776), by norm_num⟩
  | 4 => ⟨((-191901929669/1099511627776), (-238674163607/1099511627776)), (445/1099511627776), by norm_num⟩
  | 5 => ⟨((123541696431/1099511627776), (153652499051/1099511627776)), (9/34359738368), by norm_num⟩
  | 6 => ⟨((-33138781667/549755813888), (-82431385771/1099511627776)), (311/2199023255552), by norm_num⟩
  | 7 => ⟨((243816281539/8796093022208), (303241594135/8796093022208)), (575/8796093022208), by norm_num⟩
  | 8 => ⟨((-196203583589/17592186044416), (-122012129557/8796093022208)), (465/17592186044416), by norm_num⟩
  | 9 => ⟨((70172774663/17592186044416), (174551952965/35184372088832)), (167/17592186044416), by norm_num⟩
  | 10 => ⟨((-180701958341/140737488355328), (-224744424633/140737488355328)), (27/8796093022208), by norm_num⟩
  | 11 => ⟨((26438962055/70368744177664), (263063416445/562949953421312)), (127/140737488355328), by norm_num⟩
  | 12 => ⟨((-226943295449/2251799813685248), (-282256157201/2251799813685248)), (547/2251799813685248), by norm_num⟩
  | 13 => ⟨((224769934565/9007199254740992), (139776541667/4503599627370496)), (17/281474976710656), by norm_num⟩
  | 14 => ⟨((-103358072647/18014398509481984), (-257099046203/36028797018963968)), (251/18014398509481984), by norm_num⟩
  | 15 => ⟨((44359573513/36028797018963968), (220685307845/144115188075855872)), (433/144115188075855872), by norm_num⟩
  | 16 => ⟨((-71393979391/288230376151711744), (-177589650581/576460752303423488)), (175/288230376151711744), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351912437/10141204801825835211973625643008), (-1464130055463/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777681621395627/633825300114114700748351602688), (-1730715308881/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888518764676583/39614081257132168796771975168), (-3893167515135/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888217313964371/2475880078570760549798248448), (-258457390453/154742504910672534362390528)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884941736267009/77371252455336267181195264), (-4133999949383/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548327815106127/9671406556917033397649408), (-3874224727477/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314429044652487/151115727451828646838272), (-1694273467947/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886049044950989/75557863725914323419136), (-687970680779/9444732965739290427392)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296232046636583/4722366482869645213696), (-4125529789453/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404912544165481/147573952589676412928), (-2834438659233/295147905179352825856)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((113826676041549/4611686018427387904), (-7080511087165/73786976294838206464)), (1491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455031896248497/2305843009213693952), (-3978950379491/4611686018427387904)), (839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795687713215457/576460752303423488), (-3974158442613/576460752303423488)), (105/72057594037927936), by norm_num⟩
  | 5 => ⟨((298073973129841/36028797018963968), (-6944007638425/144115188075855872)), (23/2251799813685248), by norm_num⟩
  | 4 => ⟨((186026079304181/4503599627370496), (-10394502718281/36028797018963968)), (2211/36028797018963968), by norm_num⟩
  | 3 => ⟨((46405287717977/281474976710656), (-809722296471/562949953421312)), (1385/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109681879945291/2251799813685248), (-25798672784253/4503599627370496)), (5559/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203209412859771/2251799813685248), (-4802233248297/281474976710656)), (8387/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154876530098327/2251799813685248), (-75720899848695/2251799813685248)), (16969/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154876530098327/2251799813685248), (-75720899848695/2251799813685248)), (64731606490325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029789410477091/1125899906842624), (-36230838312141/562949953421312)), (33619/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874439333263127/2251799813685248), (-265104444185841/2251799813685248)), (65827/2251799813685248), by norm_num⟩
  | 3 => ⟨((1529106817946527/2251799813685248), (-27584723261409/140737488355328)), (31273/562949953421312), by norm_num⟩
  | 4 => ⟨((951848786276509/2251799813685248), (-599413687186095/2251799813685248)), (218927/2251799813685248), by norm_num⟩
  | 5 => ⟨((485584322573759/4503599627370496), (-1013502509695761/4503599627370496)), (603275/4503599627370496), by norm_num⟩
  | 6 => ⟨((-351450070303989/9007199254740992), (-874217906239175/18014398509481984)), (803235/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5962016759/2147483648), (-220716128577/2147483648)), (1/2147483648), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-3017330773/1073741824), (-223405466233/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-1015411680045867/18014398509481984), (95180008381409/4503599627370496)), (1510929/18014398509481984), by norm_num⟩
  | 1 => ⟨((201923173793/1099511627776), (-37854694311/549755813888)), (151/549755813888), by norm_num⟩
  | 2 => ⟨((-82235649185/274877906944), (61667124241/549755813888)), (247/549755813888), by norm_num⟩
  | 3 => ⟨((357242245215/1099511627776), (-66972481333/549755813888)), (269/549755813888), by norm_num⟩
  | 4 => ⟨((-2273300239/8589934592), (109101404787/1099511627776)), (55/137438953472), by norm_num⟩
  | 5 => ⟨((189609769947/1099511627776), (-35546290923/549755813888)), (9/34359738368), by norm_num⟩
  | 6 => ⟨((-402192015/4294967296), (77208831597/2199023255552)), (157/1099511627776), by norm_num⟩
  | 7 => ⟨((95844967255/2199023255552), (-17968130495/1099511627776)), (587/8796093022208), by norm_num⟩
  | 8 => ⟨((-9758504875/549755813888), (117083807521/17592186044416)), (15/549755813888), by norm_num⟩
  | 9 => ⟨((226091740085/35184372088832), (-5298199277/2199023255552)), (349/35184372088832), by norm_num⟩
  | 10 => ⟨((-147325743129/70368744177664), (55238543111/70368744177664)), (457/140737488355328), by norm_num⟩
  | 11 => ⟨((174545997691/281474976710656), (-130889095327/562949953421312)), (17/17592186044416), by norm_num⟩
  | 12 => ⟨((-379125140535/2251799813685248), (71074884725/1125899906842624)), (593/2251799813685248), by norm_num⟩
  | 13 => ⟨((380069633185/9007199254740992), (-8906493687/562949953421312)), (597/9007199254740992), by norm_num⟩
  | 14 => ⟨((-353801016025/36028797018963968), (66327351423/18014398509481984)), (279/18014398509481984), by norm_num⟩
  | 15 => ⟨((307391430789/144115188075855872), (-115253820825/144115188075855872)), (487/144115188075855872), by norm_num⟩
  | 16 => ⟨((-125188869559/288230376151711744), (2933656833/18014398509481984)), (399/576460752303423488), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643670667/5070602400912917605986812821504), (1812501542101/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777626112043683/633825300114114700748351602688), (4284795359513/633825300114114700748351602688)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888456145573237/39614081257132168796771975168), (2409603208675/19807040628566084398385987584)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888150548316067/2475880078570760549798248448), (5118937061725/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769816445254965/154742504910672534362390528), (1279321005181/38685626227668133590597632)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774132349652359/4835703278458516698824704), (4795697925295/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257660674843701/604462909807314587353088), (4194480415645/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885958331740885/75557863725914323419136), (851592596029/9444732965739290427392)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296163557697417/4722366482869645213696), (2553339064755/2361183241434822606848)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619555267711317/590295810358705651712), (3508504434333/295147905179352825856)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910553538742179/36893488147419103232), (4382127378275/36893488147419103232)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909995682521417/4611686018427387904), (9850159414049/9223372036854775808)), (841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795618659809283/576460752303423488), (9838135203245/1152921504606846976)), (421/288230376151711744), by norm_num⟩
  | 5 => ⟨((298043233251371/36028797018963968), (8594854502753/144115188075855872)), (369/36028797018963968), by norm_num⟩
  | 4 => ⟨((744009989845099/18014398509481984), (12865287743983/36028797018963968)), (2217/36028797018963968), by norm_num⟩
  | 3 => ⟨((742363024405479/4503599627370496), (8017222866127/4503599627370496)), (695/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109427786650429/2251799813685248), (31927701862167/4503599627370496)), (2791/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202392976734209/2251799813685248), (47539636444655/2251799813685248)), (8433/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153030134219539/2251799813685248), (46838975932339/1125899906842624)), (4277/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153030134219539/2251799813685248), (46838975932339/1125899906842624)), (16315462352561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((64209237929267/70368744177664), (179137996238249/2251799813685248)), (8535/562949953421312), by norm_num⟩
  | 2 => ⟨((1860593298724539/2251799813685248), (326915432612903/2251799813685248)), (8467/281474976710656), by norm_num⟩
  | 3 => ⟨((1489889866225527/2251799813685248), (135060110466423/562949953421312)), (131605/2251799813685248), by norm_num⟩
  | 4 => ⟨((856164951581153/2251799813685248), (714893708374205/2251799813685248)), (59325/562949953421312), by norm_num⟩
  | 5 => ⟨((98563561775815/2251799813685248), (543624645047089/2251799813685248)), (662249/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1015411680045867/18014398509481984), (95180008381409/4503599627370496)), (1510929/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3017330773/1073741824), (-223405466233/2147483648)), (1/2147483648), by norm_num⟩, -17, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-6104564357/2147483648), (-451986589769/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-7374428411707/18014398509481984), (2099364251460385/36028797018963968)), (1338173/18014398509481984), by norm_num⟩
  | 1 => ⟨((370863541/274877906944), (-105578034899/549755813888)), (541/2199023255552), by norm_num⟩
  | 2 => ⟨((-2444611461/1099511627776), (86991994915/274877906944)), (7/17179869184), by norm_num⟩
  | 3 => ⟨((41963753/17179869184), (-382281898517/1099511627776)), (247/549755813888), by norm_num⟩
  | 4 => ⟨((-2212890947/1099511627776), (314984693585/1099511627776)), (409/1099511627776), by norm_num⟩
  | 5 => ⟨((2917331025/2199023255552), (-207627633069/1099511627776)), (541/2199023255552), by norm_num⟩
  | 6 => ⟨((-1602507857/2199023255552), (456204538313/4398046511104)), (149/1099511627776), by norm_num⟩
  | 7 => ⟨((3018059699/8796093022208), (-214796533687/4398046511104)), (563/8796093022208), by norm_num⟩
  | 8 => ⟨((-2486758105/17592186044416), (44245895901/2199023255552)), (233/8796093022208), by norm_num⟩
  | 9 => ⟨((3642644017/70368744177664), (-506344635/68719476736)), (685/70368744177664), by norm_num⟩
  | 10 => ⟨((-300139011/17592186044416), (341776243699/140737488355328)), (453/140737488355328), by norm_num⟩
  | 11 => ⟨((2877699541/562949953421312), (-204807044347/281474976710656)), (545/562949953421312), by norm_num⟩
  | 12 => ⟨((-3161476079/2251799813685248), (450007071451/2251799813685248)), (601/2251799813685248), by norm_num⟩
  | 13 => ⟨((3206064435/9007199254740992), (-456353814169/9007199254740992)), (153/2251799813685248), by norm_num⟩
  | 14 => ⟨((-1509523623/18014398509481984), (429733635623/36028797018963968)), (289/18014398509481984), by norm_num⟩
  | 15 => ⟨((663352481/36028797018963968), (-47211065295/18014398509481984)), (255/72057594037927936), by norm_num⟩
  | 16 => ⟨((-1093150781/288230376151711744), (311199938965/576460752303423488)), (211/288230376151711744), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790136442993283/5070602400912917605986812821504), (1027644401445/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((222197834889561/79228162514264337593543950336), (607311087077/158456325028528675187087900672)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888407660247965/39614081257132168796771975168), (1366114667279/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118006221214277/154742504910672534362390528), (2902151957915/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769766005826249/154742504910672534362390528), (2901205481537/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774109008439797/4835703278458516698824704), (1359437450147/4835703278458516698824704)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314405107921563/151115727451828646838272), (1161138057/295147905179352825856)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885894067822975/75557863725914323419136), (3862384397313/75557863725914323419136)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648058174175339/2361183241434822606848), (1447570780605/2361183241434822606848)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619491959036195/590295810358705651712), (3978145456325/590295810358705651712)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910515171955415/36893488147419103232), (2484336803751/36893488147419103232)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1819908336410501/9223372036854775808), (5584251504915/9223372036854775808)), (1675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591158402070591/1152921504606846976), (2788688051377/576460752303423488)), (419/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192108491786343/144115188075855872), (4872479533007/144115188075855872)), (1467/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487932507858141/36028797018963968), (911661978749/4503599627370496)), (551/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484632716819885/9007199254740992), (4544843163739/4503599627370496)), (2759/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109358317395539/2251799813685248), (9049401141013/2251799813685248)), (2765/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202302843760381/2251799813685248), (13473790270409/1125899906842624)), (8329/2251799813685248), by norm_num⟩
  | 0 => ⟨((134582297800435/140737488355328), (13274368020945/562949953421312)), (4199/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((134582297800435/140737488355328), (13274368020945/562949953421312)), (16017915965843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((514472214614095/562949953421312), (101550480741673/2251799813685248)), (8229/562949953421312), by norm_num⟩
  | 2 => ⟨((469024158802349/562949953421312), (92805586721835/1125899906842624)), (63133/2251799813685248), by norm_num⟩
  | 3 => ⟨((773889192048767/1125899906842624), (309285484294485/2251799813685248)), (14451/281474976710656), by norm_num⟩
  | 4 => ⟨((255346900899711/562949953421312), (425175794221869/2251799813685248)), (190685/2251799813685248), by norm_num⟩
  | 5 => ⟨((383008372037171/2251799813685248), (771417215561083/4503599627370496)), (122497/1125899906842624), by norm_num⟩
  | 6 => ⟨((-7374428411707/18014398509481984), (2099364251460385/36028797018963968)), (1338173/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6104564357/2147483648), (-451986589769/4294967296)), (1/2147483648), by norm_num⟩, -17, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨66,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile066Terms3
