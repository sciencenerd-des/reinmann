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
namespace Reinmann.XiBand97.Tile010Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (24671/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (24671/1280))
  have he : value ((69/80), (24671/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-1421023053/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-41747582264297/4503599627370496), (1351226203870519/9007199254740992)), (110505259/4503599627370496), by norm_num⟩
  | 1 => ⟨((43739707/2147483648), (-1415704453/4294967296)), (117/2147483648), by norm_num⟩
  | 2 => ⟨((-96105959/4294967296), (777655155/2147483648)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((8798599/536870912), (-1139122013/4294967296)), (3/67108864), by norm_num⟩
  | 4 => ⟨((-9666249/1073741824), (625726721/4294967296)), (213/8589934592), by norm_num⟩
  | 5 => ⟨((530973/134217728), (-137486213/2147483648)), (189/17179869184), by norm_num⟩
  | 6 => ⟨((-49777789/34359738368), (402784115/17179869184)), (35/8589934592), by norm_num⟩
  | 7 => ⟨((62498847/137438953472), (-1011436751/137438953472)), (89/68719476736), by norm_num⟩
  | 8 => ⟨((-68662001/549755813888), (277794211/137438953472)), (99/274877906944), by norm_num⟩
  | 9 => ⟨((67051483/2199023255552), (-1085113365/2199023255552)), (195/2199023255552), by norm_num⟩
  | 10 => ⟨((-117861733/17592186044416), (476847551/4398046511104)), (345/17592186044416), by norm_num⟩
  | 11 => ⟨((94170435/70368744177664), (-380996785/17592186044416)), (139/35184372088832), by norm_num⟩
  | 12 => ⟨((-34485599/140737488355328), (1116180667/281474976710656)), (205/281474976710656), by norm_num⟩
  | 13 => ⟨((2914331/70368744177664), (-188653815/281474976710656)), (279/2251799813685248), by norm_num⟩
  | 14 => ⟨((-117091469/18014398509481984), (473731199/4503599627370496)), (353/18014398509481984), by norm_num⟩
  | 15 => ⟨((68607001/72057594037927936), (-277571689/18014398509481984)), (13/4503599627370496), by norm_num⟩
  | 16 => ⟨((-37686247/288230376151711744), (609887337/288230376151711744)), (231/576460752303423488), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (2126526551425/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444760617205477/158456325028528675187087900672), (2517379198481/633825300114114700748351602688)), (2889/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1890049565316339/39614081257132168796771975168), (2831576101263/39614081257132168796771975168)), (26005/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((29528806636321/38685626227668133590597632), (1503983733781/1237940039285380274899124224)), (110539/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110719349844543/9671406556917033397649408), (751828175375/38685626227668133590597632)), (3455/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774926054871065/4835703278458516698824704), (1409330060499/4835703278458516698824704)), (12959/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((78690608670539/37778931862957161709568), (2465632240469/604462909807314587353088)), (5671/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944107854573715/37778931862957161709568), (1001337236123/18889465931478580854784)), (73743/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648928359915425/2361183241434822606848), (750717889173/1180591620717411303424)), (110651/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621883573635399/590295810358705651712), (2063548163001/295147905179352825856)), (152203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912008884398015/36893488147419103232), (644511688017/9223372036854775808)), (95171/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113954144532425/576460752303423488), (2898394444357/4611686018427387904)), (13391/576460752303423488), by norm_num⟩
  | 6 => ⟨((1594512784301693/1152921504606846976), (5792021416675/1152921504606846976)), (26801/144115188075855872), by norm_num⟩
  | 5 => ⟨((298759884049301/36028797018963968), (2531329664889/72057594037927936)), (93889/72057594037927936), by norm_num⟩
  | 4 => ⟨((746160501035709/18014398509481984), (1895820040463/9007199254740992)), (282009/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490104225169935/9007199254740992), (2365095551211/2251799813685248)), (353111/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229617392443049/4503599627370496), (4716175051285/1125899906842624)), (708021/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109274287515113/1125899906842624), (28157203819567/2251799813685248)), (1066545/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092694031307519/1125899906842624), (55756903946271/2251799813685248)), (537799/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092694031307519/1125899906842624), (55756903946271/2251799813685248)), (2051540376903343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2119554377292337/2251799813685248), (54112479960257/1125899906842624)), (1070509/562949953421312), by norm_num⟩
  | 2 => ⟨((994937047493607/1125899906842624), (50934520497273/562949953421312)), (4236359/1125899906842624), by norm_num⟩
  | 3 => ⟨((1739981362480143/2251799813685248), (360079194472429/2251799813685248)), (8253779/1125899906842624), by norm_num⟩
  | 4 => ⟨((643458201274059/1125899906842624), (556471391098947/2251799813685248)), (962199/70368744177664), by norm_num⟩
  | 5 => ⟨((597963198083825/2251799813685248), (636053130834927/2251799813685248)), (50411755/2251799813685248), by norm_num⟩
  | 6 => ⟨((-41747582264297/4503599627370496), (1351226203870519/9007199254740992)), (110505259/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1421023053/33554432)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-66638419/33554432), (-1489163435/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((284866953324321/2251799813685248), (-239692921433339/4503599627370496)), (107922657/9007199254740992), by norm_num⟩
  | 1 => ⟨((-78192997/268435456), (526345585/4294967296)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((720184117/2147483648), (-605977749/4294967296)), (71/2147483648), by norm_num⟩
  | 3 => ⟨((-1105523475/4294967296), (465105111/4294967296)), (111/4294967296), by norm_num⟩
  | 4 => ⟨((1272780937/8589934592), (-33467003/536870912)), (65/4294967296), by norm_num⟩
  | 5 => ⟨((-1172274565/17179869184), (246593991/8589934592)), (61/8589934592), by norm_num⟩
  | 6 => ⟨((224938495/8589934592), (-378535765/34359738368)), (3/1073741824), by norm_num⟩
  | 7 => ⟨((-1183862915/137438953472), (62257915/17179869184)), (129/137438953472), by norm_num⟩
  | 8 => ⟨((681486275/274877906944), (-143354147/137438953472)), (151/549755813888), by norm_num⟩
  | 9 => ⟨((-1394826789/2199023255552), (586817995/2199023255552)), (157/2199023255552), by norm_num⟩
  | 10 => ⟨((1284682949/8796093022208), (-540479347/8796093022208)), (147/8796093022208), by norm_num⟩
  | 11 => ⟨((-268917437/8796093022208), (452545341/35184372088832)), (125/35184372088832), by norm_num⟩
  | 12 => ⟨((412803521/70368744177664), (-347341385/140737488355328)), (49/70368744177664), by norm_num⟩
  | 13 => ⟨((-1169864903/1125899906842624), (492174213/1125899906842624)), (141/1125899906842624), by norm_num⟩
  | 14 => ⟨((769632425/4503599627370496), (-323792287/4503599627370496)), (95/4503599627370496), by norm_num⟩
  | 15 => ⟨((-472571773/18014398509481984), (397631623/36028797018963968)), (119/36028797018963968), by norm_num⟩
  | 16 => ⟨((68008545/18014398509481984), (-114447581/72057594037927936)), (139/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806880109/10141204801825835211973625643008), (-129685289429/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905538225279/633825300114114700748351602688), (-613992997091/633825300114114700748351602688)), (92261/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889895726790717/39614081257132168796771975168), (-690622138871/39614081257132168796771975168)), (51899/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889680438927833/2475880078570760549798248448), (-733637392311/2475880078570760549798248448)), (110289/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885673356301669/77371252455336267181195264), (-733470242063/154742504910672534362390528)), (55147/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387424931164593/2417851639229258349412352), (-343725404003/4835703278458516698824704)), (51703/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258916721103235/604462909807314587353088), (-601341972949/604462909807314587353088)), (45243/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888000153820619/75557863725914323419136), (-488424025307/37778931862957161709568)), (73525/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297695576445121/4722366482869645213696), (-1430361507/9223372036854775808)), (13787/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810831425376855/295147905179352825856), (-1006501951301/590295810358705651712)), (18959/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911871568871043/36893488147419103232), (-628709515677/36893488147419103232)), (189611/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822959100124853/9223372036854775808), (-353405756557/2305843009213693952)), (106671/4611686018427387904), by norm_num⟩
  | 6 => ⟨((6227374035235/4503599627370496), (-1412407310347/1152921504606846976)), (213379/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194775083024781/144115188075855872), (-617245054703/72057594037927936)), (186749/144115188075855872), by norm_num⟩
  | 4 => ⟨((372982302336241/9007199254740992), (-924503034521/18014398509481984)), (280207/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489623011038637/9007199254740992), (-576622371927/2251799813685248)), (43801/1125899906842624), by norm_num⟩
  | 2 => ⟨((2228680442608213/4503599627370496), (-4598705898361/4503599627370496)), (350631/2251799813685248), by norm_num⟩
  | 1 => ⟨((2217206490657255/2251799813685248), (-6862485185179/2251799813685248)), (526507/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091477564490639/1125899906842624), (-13583328024297/2251799813685248)), (2110555/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091477564490639/1125899906842624), (-13583328024297/2251799813685248)), (8051128396041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2116133307848079/2251799813685248), (-26336084938871/2251799813685248)), (4117521/2251799813685248), by norm_num⟩
  | 2 => ⟨((1988332426356607/2251799813685248), (-49498775334077/2251799813685248)), (7835211/2251799813685248), by norm_num⟩
  | 3 => ⟨((1754603444289051/2251799813685248), (-87414537885243/2251799813685248)), (7090701/1125899906842624), by norm_num⟩
  | 4 => ⟨((1363794386434107/2251799813685248), (-68113447883881/1125899906842624)), (23201351/2251799813685248), by norm_num⟩
  | 5 => ⟨((1635471634865359/4503599627370496), (-330021300473181/4503599627370496)), (241491/17592186044416), by norm_num⟩
  | 6 => ⟨((284866953324321/2251799813685248), (-239692921433339/4503599627370496)), (107922657/9007199254740992), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66638419/33554432), (-1489163435/33554432)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-387700977/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-702131802084201/9007199254740992), (-896395433925817/9007199254740992)), (206233605/9007199254740992), by norm_num⟩
  | 1 => ⟨((200705353/1073741824), (512471765/2147483648)), (119/2147483648), by norm_num⟩
  | 2 => ⟨((-481270417/2147483648), (-614426811/2147483648)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((192339343/1073741824), (245555191/1073741824)), (117/2147483648), by norm_num⟩
  | 4 => ⟨((-922419203/8589934592), (-1177631263/8589934592)), (283/8589934592), by norm_num⟩
  | 5 => ⟨((884745859/17179869184), (1129534575/17179869184)), (137/8589934592), by norm_num⟩
  | 6 => ⟨((-707175971/34359738368), (-451417603/17179869184)), (221/34359738368), by norm_num⟩
  | 7 => ⟨((484495405/68719476736), (309272039/34359738368)), (153/68719476736), by norm_num⟩
  | 8 => ⟨((-580884621/274877906944), (-92700245/34359738368)), (93/137438953472), by norm_num⟩
  | 9 => ⟨((619066883/1099511627776), (790348371/1099511627776)), (25/137438953472), by norm_num⟩
  | 10 => ⟨((-593783021/4398046511104), (-758069049/4398046511104)), (97/2199023255552), by norm_num⟩
  | 11 => ⟨((258878091/8796093022208), (661007341/17592186044416)), (43/4398046511104), by norm_num⟩
  | 12 => ⟨((-827683401/140737488355328), (-264171063/35184372088832)), (277/140737488355328), by norm_num⟩
  | 13 => ⟨((610676343/562949953421312), (779636361/562949953421312)), (103/281474976710656), by norm_num⟩
  | 14 => ⟨((-836764523/4503599627370496), (-1068277911/4503599627370496)), (285/4503599627370496), by norm_num⟩
  | 15 => ⟨((133764913/4503599627370496), (683098281/18014398509481984)), (23/2251799813685248), by norm_num⟩
  | 16 => ⟨((-641508505/144115188075855872), (-818999069/144115188075855872)), (223/144115188075855872), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-2911676859237/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778772649138767/633825300114114700748351602688), (-1722927387657/316912650057057350374175801344)), (92539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236218238064151/4951760157141521099596496896), (-3875873287095/39614081257132168796771975168)), (1627/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889520831867191/2475880078570760549798248448), (-4117245179997/2475880078570760549798248448)), (55331/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771186632432705/154742504910672534362390528), (-1029066593405/38685626227668133590597632)), (110691/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549549147150835/9671406556917033397649408), (-1928979972971/4835703278458516698824704)), (51901/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629392231904929/302231454903657293676544), (-3374675400899/604462909807314587353088)), (45429/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943892147654965/37778931862957161709568), (-5481898850389/75557863725914323419136)), (147699/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324383215124161/1180591620717411303424), (-4109719529839/4722366482869645213696)), (13853/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621437781952907/590295810358705651712), (-2824047636251/295147905179352825856)), (9529/36893488147419103232), by norm_num⟩
  | 8 => ⟨((911729901389971/36893488147419103232), (-881995882051/9223372036854775808)), (47675/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822637603936273/9223372036854775808), (-991532058909/1152921504606846976)), (13419/576460752303423488), by norm_num⟩
  | 6 => ⟨((796941416351555/576460752303423488), (-3962563628951/576460752303423488)), (1679/9007199254740992), by norm_num⟩
  | 5 => ⟨((1194486934278021/144115188075855872), (-6926471309037/144115188075855872)), (94141/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491489320943143/36028797018963968), (-10373690192765/36028797018963968)), (70723/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489059784936577/9007199254740992), (-12939113355833/9007199254740992)), (88609/2251799813685248), by norm_num⟩
  | 2 => ⟨((556878521938085/1125899906842624), (-1612146779025/281474976710656)), (177835/1125899906842624), by norm_num⟩
  | 1 => ⟨((276919734918783/281474976710656), (-19241123496303/1125899906842624)), (268299/562949953421312), by norm_num⟩
  | 0 => ⟨((1089432820325835/1125899906842624), (-38064956255723/1125899906842624)), (1085609/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089432820325835/1125899906842624), (-38064956255723/1125899906842624)), (4141269688132857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052859958424393/1125899906842624), (-36832059757021/562949953421312)), (543575/281474976710656), by norm_num⟩
  | 2 => ⟨((1959477361789715/2251799813685248), (-275541373926997/2251799813685248)), (8702023/2251799813685248), by norm_num⟩
  | 3 => ⟨((1671386799016263/2251799813685248), (-239771351416345/1125899906842624)), (17274347/2251799813685248), by norm_num⟩
  | 4 => ⟨((142306867849981/281474976710656), (-177969049070889/562949953421312)), (2062567/140737488355328), by norm_num⟩
  | 5 => ⟨((350524914849553/2251799813685248), (-1439628814950867/4503599627370496)), (54234761/2251799813685248), by norm_num⟩
  | 6 => ⟨((-702131802084201/9007199254740992), (-896395433925817/9007199254740992)), (206233605/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-387700977/8388608)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-17978733/8388608), (-1607077251/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-757796473548171/9007199254740992), (735906731137257/9007199254740992)), (48100997/2251799813685248), by norm_num⟩
  | 1 => ⟨((448954939/2147483648), (-871972813/4294967296)), (115/2147483648), by norm_num⟩
  | 2 => ⟨((-557805557/2147483648), (67711595/268435456)), (145/2147483648), by norm_num⟩
  | 3 => ⟨((462031579/2147483648), (-897370627/4294967296)), (243/4294967296), by norm_num⟩
  | 4 => ⟨((-574052671/4294967296), (557470559/4294967296)), (153/4294967296), by norm_num⟩
  | 5 => ⟨((71323365/1073741824), (-69263115/1073741824)), (77/4294967296), by norm_num⟩
  | 6 => ⟨((-945236821/34359738368), (917932667/34359738368)), (257/34359738368), by norm_num⟩
  | 7 => ⟨((167773233/17179869184), (-651707711/68719476736)), (23/8589934592), by norm_num⟩
  | 8 => ⟨((-208450411/68719476736), (202429103/68719476736)), (231/274877906944), by norm_num⟩
  | 9 => ⟨((115106625/137438953472), (-447126599/549755813888)), (129/549755813888), by norm_num⟩
  | 10 => ⟨((-915293497/4398046511104), (888854287/4398046511104)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((827061417/17592186044416), (-803170883/17592186044416)), (235/17592186044416), by norm_num⟩
  | 12 => ⟨((-685056805/70368744177664), (665268223/70368744177664)), (197/70368744177664), by norm_num⟩
  | 13 => ⟨((1047570591/562949953421312), (-1017310419/562949953421312)), (19/35184372088832), by norm_num⟩
  | 14 => ⟨((-743747179/2251799813685248), (22570727/70368744177664)), (109/1125899906842624), by norm_num⟩
  | 15 => ⟨((985675899/18014398509481984), (-239300905/4503599627370496)), (291/18014398509481984), by norm_num⟩
  | 16 => ⟨((-612328149/72057594037927936), (297320205/36028797018963968)), (91/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (772073596109/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889328084848187/316912650057057350374175801344), (3654421981297/633825300114114700748351602688)), (5785/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889614845760777/39614081257132168796771975168), (2055220392629/19807040628566084398385987584)), (104153/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889381553441239/2475880078570760549798248448), (4366386893257/2475880078570760549798248448)), (110689/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771047322002421/154742504910672534362390528), (4365311060695/154742504910672534362390528)), (865/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((1549418509665065/9671406556917033397649408), (2045668135561/4835703278458516698824704)), (12979/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258670122105553/604462909807314587353088), (3578776640457/604462909807314587353088)), (90885/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117974901661423/4722366482869645213696), (5813370206319/75557863725914323419136)), (147747/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648696701769273/2361183241434822606848), (4358154084245/4722366482869645213696)), (110863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621245938801039/590295810358705651712), (5989418316405/590295810358705651712)), (76261/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823219864457637/73786976294838206464), (1870552331587/18446744073709551616)), (190781/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911183744573583/4611686018427387904), (262850419911/288230376151711744)), (214805/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593612488591305/1152921504606846976), (8403377648615/1152921504606846976)), (107513/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194250126424983/144115188075855872), (1836036516953/36028797018963968)), (47099/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491133598729705/36028797018963968), (10998615076973/36028797018963968)), (283091/36028797018963968), by norm_num⟩
  | 3 => ⟨((372153561454377/2251799813685248), (857343434413/562949953421312)), (354735/9007199254740992), by norm_num⟩
  | 2 => ⟨((278327547251193/562949953421312), (6835700222501/1125899906842624)), (356045/2251799813685248), by norm_num⟩
  | 1 => ⟨((553502708016435/562949953421312), (10196048387363/562949953421312)), (537349/1125899906842624), by norm_num⟩
  | 0 => ⟨((1088073094611299/1125899906842624), (40325573697729/1125899906842624)), (8499/8796093022208), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088073094611299/1125899906842624), (40325573697729/1125899906842624)), (32421112094101307/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((131259104399257/140737488355328), (38970757079383/562949953421312)), (1090287/562949953421312), by norm_num⟩
  | 2 => ⟨((1947913971603871/2251799813685248), (145384623010637/1125899906842624)), (8738677/2251799813685248), by norm_num⟩
  | 3 => ⟨((823745979503029/1125899906842624), (251529231593023/1125899906842624)), (8687775/1125899906842624), by norm_num⟩
  | 4 => ⟨((1092975460184725/2251799813685248), (736108749962621/2251799813685248)), (33188561/2251799813685248), by norm_num⟩
  | 5 => ⟨((289874464340691/2251799813685248), (714582881521507/2251799813685248)), (107833163/4503599627370496), by norm_num⟩
  | 6 => ⟨((-757796473548171/9007199254740992), (735906731137257/9007199254740992)), (48100997/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-1607077251/33554432)), (1/16777216), by norm_num⟩, -8, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-579933/262144), (-1658843709/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((333360342211323/4503599627370496), (363110249654971/4503599627370496)), (57607571/4503599627370496), by norm_num⟩
  | 1 => ⟨((-815441509/4294967296), (-888213541/4294967296)), (143/4294967296), by norm_num⟩
  | 2 => ⟨((65361443/268435456), (71194461/268435456)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-894126887/4294967296), (-973920997/4294967296)), (81/2147483648), by norm_num⟩
  | 4 => ⟨((286673773/2147483648), (624514509/4294967296)), (105/4294967296), by norm_num⟩
  | 5 => ⟨((-73530371/1073741824), (-160184809/2147483648)), (55/4294967296), by norm_num⟩
  | 6 => ⟨((1005875615/34359738368), (1095642461/34359738368)), (191/34359738368), by norm_num⟩
  | 7 => ⟨((-737148575/68719476736), (-802933551/68719476736)), (71/34359738368), by norm_num⟩
  | 8 => ⟨((472687191/137438953472), (257435487/68719476736)), (23/34359738368), by norm_num⟩
  | 9 => ⟨((-538852759/549755813888), (-293470661/274877906944)), (107/549755813888), by norm_num⟩
  | 10 => ⟨((552852015/2199023255552), (602189907/2199023255552)), (7/137438953472), by norm_num⟩
  | 11 => ⟨((-515649971/8796093022208), (-140416965/2199023255552)), (53/4398046511104), by norm_num⟩
  | 12 => ⟨((881744041/70368744177664), (480216539/35184372088832)), (23/8796093022208), by norm_num⟩
  | 13 => ⟨((-173971447/70368744177664), (-757988371/281474976710656)), (147/281474976710656), by norm_num⟩
  | 14 => ⟨((1019949603/2251799813685248), (1110972449/2251799813685248)), (109/1125899906842624), by norm_num⟩
  | 15 => ⟨((-348815877/4503599627370496), (-94986269/1125899906842624)), (151/9007199254740992), by norm_num⟩
  | 16 => ⟨((223673765/18014398509481984), (974539879/72057594037927936)), (49/18014398509481984), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (269669090349/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778556040435729/633825300114114700748351602688), (1276267393823/633825300114114700748351602688)), (46163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944751288079333/19807040628566084398385987584), (717761958713/19807040628566084398385987584)), (103875/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889262756392033/2475880078570760549798248448), (190612500875/309485009821345068724781056)), (110377/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770929075094195/154742504910672534362390528), (381128244993/38685626227668133590597632)), (110387/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549308237341179/9671406556917033397649408), (357204958785/2417851639229258349412352)), (103499/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258574217556001/604462909807314587353088), (312451605351/151115727451828646838272)), (90573/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887443675301363/75557863725914323419136), (507541312473/18889465931478580854784)), (147201/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297278296098811/4722366482869645213696), (380487585625/1180591620717411303424)), (27605/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405272304485133/147573952589676412928), (2091587722999/590295810358705651712)), (151857/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227878286034147/9223372036854775808), (653211173845/18446744073709551616)), (94933/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113884556746011/576460752303423488), (91787407063/288230376151711744)), (213661/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796700945144865/576460752303423488), (2934382983345/1152921504606846976)), (106869/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194070323951989/144115188075855872), (641105696177/36028797018963968)), (46777/36028797018963968), by norm_num⟩
  | 4 => ⟨((93179550800349/2251799813685248), (3840318196509/36028797018963968)), (70209/9007199254740992), by norm_num⟩
  | 3 => ⟨((744151907481811/4503599627370496), (4789364262141/9007199254740992)), (43919/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113022976565733/2251799813685248), (9545705868787/4503599627370496)), (351811/2251799813685248), by norm_num⟩
  | 1 => ⟨((138329032909017/140737488355328), (14236273840867/2251799813685248)), (528871/1125899906842624), by norm_num⟩
  | 0 => ⟨((2175110360515133/2251799813685248), (14072516526183/1125899906842624)), (2124771/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2175110360515133/2251799813685248), (14072516526183/1125899906842624)), (8105358132369231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2100680934773337/2251799813685248), (54372997650313/2251799813685248)), (4157931/2251799813685248), by norm_num⟩
  | 2 => ⟨((244798846018951/281474976710656), (12681002862279/281474976710656)), (3979291/1125899906842624), by norm_num⟩
  | 3 => ⟨((1698642426464885/2251799813685248), (88229366697559/1125899906842624)), (7280131/1125899906842624), by norm_num⟩
  | 4 => ⟨((316885230099995/562949953421312), (66555714509687/562949953421312)), (3031127/281474976710656), by norm_num⟩
  | 5 => ⟨((341012856785141/1125899906842624), (149857178448597/1125899906842624)), (66066731/4503599627370496), by norm_num⟩
  | 6 => ⟨((333360342211323/4503599627370496), (363110249654971/4503599627370496)), (57607571/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1658843709/33554432)), (1/16777216), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-2386755/1048576), (-853385981/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((381566282307973/4503599627370496), (-522407320692677/9007199254740992)), (23460823/2251799813685248), by norm_num⟩
  | 1 => ⟨((-960326475/4294967296), (164349421/1073741824)), (15/536870912), by norm_num⟩
  | 2 => ⟨((1267178311/4294967296), (-54215943/268435456)), (5/134217728), by norm_num⟩
  | 3 => ⟨((-69669921/268435456), (381543951/2147483648)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((367725831/2147483648), (-125864545/1073741824)), (3/134217728), by norm_num⟩
  | 5 => ⟨((-776359639/8589934592), (33216375/536870912)), (103/8589934592), by norm_num⟩
  | 6 => ⟨((170738133/4294967296), (-233759781/8589934592)), (23/4294967296), by norm_num⟩
  | 7 => ⟨((-1029914791/68719476736), (705034815/68719476736)), (141/68719476736), by norm_num⟩
  | 8 => ⟨((169875261/34359738368), (-58144603/17179869184)), (95/137438953472), by norm_num⟩
  | 9 => ⟨((-398498269/274877906944), (272794561/274877906944)), (113/549755813888), by norm_num⟩
  | 10 => ⟨((420663911/1099511627776), (-143984097/549755813888)), (121/2199023255552), by norm_num⟩
  | 11 => ⟨((-807386311/8796093022208), (138175377/2199023255552)), (59/4398046511104), by norm_num⟩
  | 12 => ⟨((355123127/17592186044416), (-486203655/35184372088832)), (53/17592186044416), by norm_num⟩
  | 13 => ⟨((-576732487/140737488355328), (789611889/281474976710656)), (175/281474976710656), by norm_num⟩
  | 14 => ⟨((217432871/281474976710656), (-297690149/562949953421312)), (67/562949953421312), by norm_num⟩
  | 15 => ⟨((-1224144665/9007199254740992), (837996127/9007199254740992)), (191/9007199254740992), by norm_num⟩
  | 16 => ⟨((807646987/36028797018963968), (-552879955/36028797018963968)), (1/281474976710656), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (-781939272025/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889228973742819/316912650057057350374175801344), (-925076635605/633825300114114700748351602688)), (23073/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944696133236223/19807040628566084398385987584), (-1040505271437/39614081257132168796771975168)), (51917/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472286402424121/618970019642690137449562112), (-1105280231265/2475880078570760549798248448)), (55165/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885405996435099/77371252455336267181195264), (-552495826337/77371252455336267181195264)), (55169/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774599270611171/4835703278458516698824704), (-1035623163851/9671406556917033397649408)), (51725/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258478301878939/604462909807314587353088), (-905863875121/604462909807314587353088)), (90527/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471821985135819/18889465931478580854784), (-1471454558845/75557863725914323419136)), (147121/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648580803568479/2361183241434822606848), (-275772177419/1180591620717411303424)), (55177/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810464476317673/295147905179352825856), (-378982838007/147573952589676412928)), (151759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822826229394891/73786976294838206464), (-1893691570383/73786976294838206464)), (189731/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910964108145403/4611686018427387904), (-1064361619847/4611686018427387904)), (53373/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398294416555391/288230376151711744), (-66457047009/36028797018963968)), (213549/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149234331625671/18014398509481984), (-116152505727/9007199254740992)), (186919/144115188075855872), by norm_num⟩
  | 4 => ⟨((745290177168511/18014398509481984), (-1391476249551/18014398509481984)), (280505/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487940070684805/9007199254740992), (-1735233779121/4503599627370496)), (350853/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225323930612421/4503599627370496), (-6916327010425/4503599627370496)), (702377/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106097543374681/1125899906842624), (-10313183551767/2251799813685248)), (1055253/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173025431973545/2251799813685248), (-20382414931651/2251799813685248)), (2117301/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2173025431973545/2251799813685248), (-20382414931651/2251799813685248)), (8076862343795012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((65525697162191/70368744177664), (-19669379907723/1125899906842624)), (2062397/1125899906842624), by norm_num⟩
  | 2 => ⟨((487955926586185/562949953421312), (-73262630803671/2251799813685248)), (1956485/562949953421312), by norm_num⟩
  | 3 => ⟨((211178206453835/281474976710656), (-31751432503621/562949953421312)), (7038017/1125899906842624), by norm_num⟩
  | 4 => ⟨((630168934130645/1125899906842624), (-190573546446293/2251799813685248)), (2838635/281474976710656), by norm_num⟩
  | 5 => ⟨((1378571270976443/4503599627370496), (-213328960963035/2251799813685248)), (14632235/1125899906842624), by norm_num⟩
  | 6 => ⟨((381566282307973/4503599627370496), (-522407320692677/9007199254740992)), (23460823/2251799813685248), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-853385981/16777216)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-1751392099/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-612748698608665/18014398509481984), (-1631502374480935/18014398509481984)), (306103635/18014398509481984), by norm_num⟩
  | 1 => ⟨((395620879/4294967296), (1053378661/4294967296)), (25/536870912), by norm_num⟩
  | 2 => ⟨((-66960075/536870912), (-1426301147/4294967296)), (273/4294967296), by norm_num⟩
  | 3 => ⟨((483549985/4294967296), (1287498369/4294967296)), (249/4294967296), by norm_num⟩
  | 4 => ⟨((-5115147/67108864), (-435826277/2147483648)), (171/4294967296), by norm_num⟩
  | 5 => ⟨((88653279/2147483648), (472095775/4294967296)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((-320103373/17179869184), (-852306039/17179869184)), (43/4294967296), by norm_num⟩
  | 7 => ⟨((30959143/4294967296), (659453583/34359738368)), (67/17179869184), by norm_num⟩
  | 8 => ⟨((-167677827/68719476736), (-27903647/4294967296)), (183/137438953472), by norm_num⟩
  | 9 => ⟨((403626643/549755813888), (537347391/274877906944)), (111/274877906944), by norm_num⟩
  | 10 => ⟨((-437216485/2199023255552), (-145516371/274877906944)), (121/1099511627776), by norm_num⟩
  | 11 => ⟨((215273489/4398046511104), (286593191/2199023255552)), (15/549755813888), by norm_num⟩
  | 12 => ⟨((-194323805/17592186044416), (-1034811665/35184372088832)), (219/35184372088832), by norm_num⟩
  | 13 => ⟨((161919575/70368744177664), (107781613/17592186044416)), (23/17592186044416), by norm_num⟩
  | 14 => ⟨((-501127243/1125899906842624), (-667149757/562949953421312)), (287/1125899906842624), by norm_num⟩
  | 15 => ⟨((361887395/4503599627370496), (481780009/2251799813685248)), (209/4503599627370496), by norm_num⟩
  | 16 => ⟨((-61250577/4503599627370496), (-652342225/18014398509481984)), (285/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-2514131022631/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778361968770965/633825300114114700748351602688), (-46469708947/9903520314283042199192993792)), (92493/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889284072907035/39614081257132168796771975168), (-3345132527515/39614081257132168796771975168)), (52037/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944515182836063/1237940039285380274899124224), (-3553355830373/2475880078570760549798248448)), (13825/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885348212383563/77371252455336267181195264), (-3552402687433/154742504910672534362390528)), (110625/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549089852050681/9671406556917033397649408), (-1664682542737/4835703278458516698824704)), (103737/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258382855069767/604462909807314587353088), (-2912182331077/604462909807314587353088)), (22699/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471783048875385/18889465931478580854784), (-4730399235253/75557863725914323419136)), (18449/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648522117746799/2361183241434822606848), (-1773070087489/2361183241434822606848)), (110737/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620766653132071/590295810358705651712), (-4873247712321/590295810358705651712)), (38083/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227827748349815/9223372036854775808), (-6087519294225/73786976294838206464)), (190519/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910848282677661/4611686018427387904), (-6842907297695/9223372036854775808)), (107239/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592943672688005/1152921504606846976), (-1708993190437/288230376151711744)), (107329/576460752303423488), by norm_num⟩
  | 5 => ⟨((596833639997933/72057594037927936), (-746710270709/18014398509481984)), (47007/36028797018963968), by norm_num⟩
  | 4 => ⟨((745132027172783/18014398509481984), (-4472476808399/18014398509481984)), (282447/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487535562708853/9007199254740992), (-697124154371/562949953421312)), (353769/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224487666684269/4503599627370496), (-22226521363821/4503599627370496)), (709673/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210873097516767/2251799813685248), (-33136730241893/2251799813685248)), (267465/562949953421312), by norm_num⟩
  | 0 => ⟨((2170114225044279/2251799813685248), (-8183088875827/281474976710656)), (2161207/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170114225044279/2251799813685248), (-8183088875827/281474976710656)), (8244350441939543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044744318024449/1125899906842624), (-126179867082739/2251799813685248)), (2145639/1125899906842624), by norm_num⟩
  | 2 => ⟨((1931806448727465/2251799813685248), (-234169482353813/2251799813685248)), (8444845/2251799813685248), by norm_num⟩
  | 3 => ⟨((102058384212599/140737488355328), (-100446343710707/562949953421312)), (16245967/2251799813685248), by norm_num⟩
  | 4 => ⟨((556231159423725/1125899906842624), (-582724143167645/2251799813685248)), (29359615/2251799813685248), by norm_num⟩
  | 5 => ⟨((797588647416507/4503599627370496), (-575769344696539/2251799813685248)), (11051165/562949953421312), by norm_num⟩
  | 6 => ⟨((-612748698608665/18014398509481984), (-1631502374480935/18014398509481984)), (306103635/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-1751392099/33554432)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile010Terms1
