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
namespace Reinmann.XiBand97.Tile044Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨44,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (36127/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (36127/1280))
  have he : value ((69/80), (36127/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1463682213/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((117463784974385/2251799813685248), (414040687360049/9007199254740992)), (276789195/18014398509481984), by norm_num⟩
  | 1 => ⟨((-21641585/134217728), (-38141529/268435456)), (103/2147483648), by norm_num⟩
  | 2 => ⟨((33447529/134217728), (943176683/4294967296)), (5/67108864), by norm_num⟩
  | 3 => ⟨((-275700619/1073741824), (-971799723/4294967296)), (83/1073741824), by norm_num⟩
  | 4 => ⟨((426101159/2147483648), (375484275/2147483648)), (129/2147483648), by norm_num⟩
  | 5 => ⟨((-526838709/4294967296), (-232127567/2147483648)), (321/8589934592), by norm_num⟩
  | 6 => ⟨((1085653877/17179869184), (956688219/17179869184)), (333/17179869184), by norm_num⟩
  | 7 => ⟨((-958800635/34359738368), (-844903971/34359738368)), (37/4294967296), by norm_num⟩
  | 8 => ⟨((740923367/68719476736), (652908511/68719476736)), (115/34359738368), by norm_num⟩
  | 9 => ⟨((-1017878037/274877906944), (-896963523/274877906944)), (319/274877906944), by norm_num⟩
  | 10 => ⟨((629260845/549755813888), (277255233/274877906944)), (199/549755813888), by norm_num⟩
  | 11 => ⟨((-88412363/274877906944), (-155819581/549755813888)), (225/2199023255552), by norm_num⟩
  | 12 => ⟨((728763647/8796093022208), (642193253/8796093022208)), (117/4398046511104), by norm_num⟩
  | 13 => ⟨((-693119807/35184372088832), (-152695893/8796093022208)), (7/1099511627776), by norm_num⟩
  | 14 => ⟨((306066107/70368744177664), (539416557/140737488355328)), (199/140737488355328), by norm_num⟩
  | 15 => ⟨((-1009134219/1125899906842624), (-222314597/281474976710656)), (165/562949953421312), by norm_num⟩
  | 16 => ⟨((389909589/2251799813685248), (687183857/4503599627370496)), (257/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (940923198821/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888928586447293/316912650057057350374175801344), (1112446837831/633825300114114700748351602688)), (184619/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888716528639821/39614081257132168796771975168), (1251215141967/39614081257132168796771975168)), (207711/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888427804079055/2475880078570760549798248448), (664527364077/1237940039285380274899124224)), (220709/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770094373743843/154742504910672534362390528), (664324200827/77371252455336267181195264)), (27591/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548525971375793/9671406556917033397649408), (1245176326219/9671406556917033397649408)), (25869/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257890001277467/604462909807314587353088), (1089097928221/604462909807314587353088)), (181103/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943166161596799/37778931862957161709568), (442243937179/18889465931478580854784)), (36791/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296445218712493/4722366482869645213696), (1326024884883/4722366482869645213696)), (220779/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202493055715963/73786976294838206464), (1822136228973/590295810358705651712)), (303623/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821596386036049/73786976294838206464), (1137974823859/36893488147419103232)), (47451/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910272864174113/4611686018427387904), (1279039828207/4611686018427387904)), (427167/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795898267192747/576460752303423488), (2555128302511/1152921504606846976)), (213651/576460752303423488), by norm_num⟩
  | 5 => ⟨((596333843317809/72057594037927936), (558105369811/36028797018963968)), (374043/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488772948677581/36028797018963968), (417751481383/4503599627370496)), (561371/36028797018963968), by norm_num⟩
  | 3 => ⟨((185710766407727/1125899906842624), (1041488583225/2251799813685248)), (702251/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220831968115495/4503599627370496), (8297327653027/4503599627370496)), (351531/1125899906842624), by norm_num⟩
  | 1 => ⟨((1102748403005917/1125899906842624), (6179944730391/1125899906842624)), (1056631/1125899906842624), by norm_num⟩
  | 0 => ⟨((2159786757357341/2251799813685248), (12188733005853/1125899906842624)), (1060741/562949953421312), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2159786757357341/2251799813685248), (12188733005853/1125899906842624)), (4046405794383811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1035634817105221/1125899906842624), (11690676930967/562949953421312)), (2057761/562949953421312), by norm_num⟩
  | 2 => ⟨((952120859214165/1125899906842624), (43013671079131/1125899906842624)), (3871041/562949953421312), by norm_num⟩
  | 3 => ⟨((1607041530339999/2251799813685248), (72749297192263/1125899906842624)), (27371575/2251799813685248), by norm_num⟩
  | 4 => ⟨((142186964384153/281474976710656), (207675906500195/2251799813685248)), (1331429/70368744177664), by norm_num⟩
  | 5 => ⟨((1110904452578569/4503599627370496), (104907395556317/1125899906842624)), (101806595/4503599627370496), by norm_num⟩
  | 6 => ⟨((117463784974385/2251799813685248), (414040687360049/9007199254740992)), (276789195/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1463682213/16777216)), (1/8388608), by norm_num⟩, -14, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-1484731181/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1038631355993197/18014398509481984), (-611737541796751/18014398509481984)), (29375317/2251799813685248), by norm_num⟩
  | 1 => ⟨((-776439335/4294967296), (457310563/4294967296)), (177/4294967296), by norm_num⟩
  | 2 => ⟨((608630261/2147483648), (-44809207/268435456)), (35/536870912), by norm_num⟩
  | 3 => ⟨((-1272237775/4294967296), (374664025/2147483648)), (295/4294967296), by norm_num⟩
  | 4 => ⟨((498636773/2147483648), (-293689221/2147483648)), (233/4294967296), by norm_num⟩
  | 5 => ⟨((-625389087/4294967296), (736688683/8589934592)), (147/4294967296), by norm_num⟩
  | 6 => ⟨((1307269243/17179869184), (-769961035/17179869184)), (309/17179869184), by norm_num⟩
  | 7 => ⟨((-146390541/4294967296), (172443455/8589934592)), (279/34359738368), by norm_num⟩
  | 8 => ⟨((918013389/68719476736), (-16896733/2147483648)), (55/17179869184), by norm_num⟩
  | 9 => ⟨((-639650149/137438953472), (376743883/137438953472)), (309/274877906944), by norm_num⟩
  | 10 => ⟨((802247737/549755813888), (-236255653/274877906944)), (49/137438953472), by norm_num⟩
  | 11 => ⟨((-228676649/549755813888), (269373903/1099511627776)), (225/2199023255552), by norm_num⟩
  | 12 => ⟨((119502385/1099511627776), (-281540105/4398046511104)), (237/8796093022208), by norm_num⟩
  | 13 => ⟨((-922336091/35184372088832), (543241459/35184372088832)), (115/17592186044416), by norm_num⟩
  | 14 => ⟨((826279851/140737488355328), (-121666461/35184372088832)), (13/8796093022208), by norm_num⟩
  | 15 => ⟨((-690878851/562949953421312), (25432299/35184372088832)), (11/35184372088832), by norm_num⟩
  | 16 => ⟨((135390415/562949953421312), (-637942611/4503599627370496)), (139/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-693354559151/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777798432362059/633825300114114700748351602688), (-409848133807/316912650057057350374175801344)), (92281/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888650477509569/39614081257132168796771975168), (-460971864871/19807040628566084398385987584)), (207643/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888357666300291/2475880078570760549798248448), (-979295144619/2475880078570760549798248448)), (220633/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885012141332485/77371252455336267181195264), (-244747868983/38685626227668133590597632)), (110323/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548460310577231/9671406556917033397649408), (-458740996143/4835703278458516698824704)), (206871/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628916298815985/302231454903657293676544), (-200618593739/151115727451828646838272)), (90513/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886239135108457/75557863725914323419136), (-1303416733305/75557863725914323419136)), (294195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296375408809091/4722366482869645213696), (-977034254095/4722366482869645213696)), (110335/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809924294429301/295147905179352825856), (-1342564207599/590295810358705651712)), (303459/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910738381165563/36893488147419103232), (-838459725911/36893488147419103232)), (189691/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455102855672271/2305843009213693952), (-942384034987/4611686018427387904)), (426885/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591662566902387/1152921504606846976), (-941281342011/576460752303423488)), (213493/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192550844732777/144115188075855872), (-1644764730379/144115188075855872)), (186863/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488598443109149/36028797018963968), (-1231100224541/18014398509481984)), (560817/36028797018963968), by norm_num⟩
  | 3 => ⟨((92841832503349/562949953421312), (-3069113221755/9007199254740992)), (175355/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220402290018895/4503599627370496), (-6112391415679/4503599627370496)), (702023/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102431043565801/1125899906842624), (-4552134115907/1125899906842624)), (527277/562949953421312), by norm_num⟩
  | 0 => ⟨((2158556139396461/2251799813685248), (-17952866657909/2251799813685248)), (2115249/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158556139396461/2251799813685248), (-17952866657909/2251799813685248)), (8069034580710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((258628801791667/281474976710656), (-34418930411735/2251799813685248)), (511131/140737488355328), by norm_num⟩
  | 2 => ⟨((950284782567243/1125899906842624), (-3953160790421/140737488355328)), (15278633/2251799813685248), by norm_num⟩
  | 3 => ⟨((1602346716189795/2251799813685248), (-53384902431881/1125899906842624)), (26649339/2251799813685248), by norm_num⟩
  | 4 => ⟨((283785795713151/562949953421312), (-151951559079033/2251799813685248)), (40453709/2251799813685248), by norm_num⟩
  | 5 => ⟨((1123954946242903/4503599627370496), (-306398064986249/4503599627370496)), (92490917/4503599627370496), by norm_num⟩
  | 6 => ⟨((1038631355993197/18014398509481984), (-611737541796751/18014398509481984)), (29375317/2251799813685248), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-1484731181/16777216)), (1/8388608), by norm_num⟩, -14, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-376221043/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-47052908511001/4503599627370496), (-573302943116479/9007199254740992)), (197304237/9007199254740992), by norm_num⟩
  | 1 => ⟨((285218575/8589934592), (217197849/1073741824)), (75/1073741824), by norm_num⟩
  | 2 => ⟨((-56652499/1073741824), (-86283307/268435456)), (479/4294967296), by norm_num⟩
  | 3 => ⟨((240059589/4294967296), (1462469303/4294967296)), (255/2147483648), by norm_num⟩
  | 4 => ⟨((-95365287/2147483648), (-580975771/2147483648)), (407/4294967296), by norm_num⟩
  | 5 => ⟨((60615203/2147483648), (1477097819/8589934592)), (65/1073741824), by norm_num⟩
  | 6 => ⟨((-256851171/17179869184), (-391191365/4294967296)), (553/17179869184), by norm_num⟩
  | 7 => ⟨((116612407/17179869184), (11100243/268435456)), (63/4294967296), by norm_num⟩
  | 8 => ⟨((-185300253/68719476736), (-1128869433/68719476736)), (201/34359738368), by norm_num⟩
  | 9 => ⟨((130865373/137438953472), (1594492367/274877906944)), (285/137438953472), by norm_num⟩
  | 10 => ⟨((-5198715/17179869184), (-1013476515/549755813888)), (91/137438953472), by norm_num⟩
  | 11 => ⟨((48063407/549755813888), (1171230153/2199023255552)), (423/2199023255552), by norm_num⟩
  | 12 => ⟨((-101832063/4398046511104), (-620372079/4398046511104)), (225/4398046511104), by norm_num⟩
  | 13 => ⟨((49788889/8796093022208), (1213277453/35184372088832)), (221/17592186044416), by norm_num⟩
  | 14 => ⟨((-45209077/35184372088832), (-1101674587/140737488355328)), (403/140737488355328), by norm_num⟩
  | 15 => ⟨((153255339/562949953421312), (58353019/35184372088832)), (343/562949953421312), by norm_num⟩
  | 16 => ⟨((-243526859/4503599627370496), (-370898071/1125899906842624)), (547/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (-2258067135459/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444434610796403/158456325028528675187087900672), (-2669365810757/633825300114114700748351602688)), (184925/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944291408009521/19807040628566084398385987584), (-3002323048827/39614081257132168796771975168)), (52019/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888285541097817/2475880078570760549798248448), (-797269042509/618970019642690137449562112)), (3455/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1769951893571591/154742504910672534362390528), (-3188073018281/154742504910672534362390528)), (55291/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548392165663415/9671406556917033397649408), (-373469124205/1208925819614629174706176)), (51847/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628886345484941/302231454903657293676544), (-2613218844621/604462909807314587353088)), (181511/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886141262626993/75557863725914323419136), (-4244484627517/75557863725914323419136)), (73761/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296301546397965/4722366482869645213696), (-795404475287/1180591620717411303424)), (13835/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619746284809831/590295810358705651712), (-546486224911/73786976294838206464)), (304495/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821347769338935/73786976294838206464), (-2730306531279/36893488147419103232)), (190403/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113766548650415/576460752303423488), (-1534337998387/2305843009213693952)), (214333/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49734813072695/36028797018963968), (-6130062255141/1152921504606846976)), (214495/576460752303423488), by norm_num⟩
  | 5 => ⟨((149052341099951/18014398509481984), (-5355613668089/144115188075855872)), (375731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488396013319603/36028797018963968), (-4008532120359/18014398509481984)), (564325/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485208870841671/9007199254740992), (-9992763802963/9007199254740992)), (353343/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109929649258675/2251799813685248), (-4975013893287/1125899906842624)), (354305/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203992864989801/2251799813685248), (-29637197695767/2251799813685248)), (1067741/1125899906842624), by norm_num⟩
  | 0 => ⟨((134787607822395/140737488355328), (-58427605695037/2251799813685248)), (1077441/562949953421312), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((134787607822395/140737488355328), (-58427605695037/2251799813685248)), (4110111238719749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1031956124075381/1125899906842624), (-111914988599781/2251799813685248)), (8478777/2251799813685248), by norm_num⟩
  | 2 => ⟨((235767450195903/281474976710656), (-205153863428667/2251799813685248)), (16385431/2251799813685248), by norm_num⟩
  | 3 => ⟨((1561166524464345/2251799813685248), (-171839798491701/1125899906842624)), (3804373/281474976710656), by norm_num⟩
  | 4 => ⟨((64368656286379/140737488355328), (-119136052568055/562949953421312)), (51491223/2251799813685248), by norm_num⟩
  | 5 => ⟨((740382455039787/4503599627370496), (-871822023676613/4503599627370496)), (137789477/4503599627370496), by norm_num⟩
  | 6 => ⟨((-47052908511001/4503599627370496), (-573302943116479/9007199254740992)), (197304237/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-376221043/4194304)), (1/8388608), by norm_num⟩, -14, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-1524214359/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-542606660355143/9007199254740992), (-283967591921581/18014398509481984)), (392112635/18014398509481984), by norm_num⟩
  | 1 => ⟨((1665671789/8589934592), (6810251/134217728)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((-41887427/134217728), (-350741637/4294967296)), (61/536870912), by norm_num⟩
  | 3 => ⟨((359547803/1073741824), (376331259/4294967296)), (263/2147483648), by norm_num⟩
  | 4 => ⟨((-1157339731/4294967296), (-151420449/2147483648)), (425/4294967296), by norm_num⟩
  | 5 => ⟨((1490133153/8589934592), (194961449/4294967296)), (549/8589934592), by norm_num⟩
  | 6 => ⟨((-799425597/8589934592), (-209185565/8589934592)), (591/17179869184), by norm_num⟩
  | 7 => ⟨((1470429559/34359738368), (192383531/17179869184)), (545/34359738368), by norm_num⟩
  | 8 => ⟨((-295820635/17179869184), (-309629349/68719476736)), (55/8589934592), by norm_num⟩
  | 9 => ⟨((1692817583/274877906944), (442959301/274877906944)), (79/34359738368), by norm_num⟩
  | 10 => ⟨((-1089793919/549755813888), (-285166197/549755813888)), (51/68719476736), by norm_num⟩
  | 11 => ⟨((1275604109/2199023255552), (333787119/2199023255552)), (479/2199023255552), by norm_num⟩
  | 12 => ⟨((-684335205/4398046511104), (-358139763/8796093022208)), (129/2199023255552), by norm_num⟩
  | 13 => ⟨((677781553/17592186044416), (354709977/35184372088832)), (513/35184372088832), by norm_num⟩
  | 14 => ⟨((-311670665/35184372088832), (-326219249/140737488355328)), (237/70368744177664), by norm_num⟩
  | 15 => ⟨((535055557/281474976710656), (280015801/562949953421312)), (409/562949953421312), by norm_num⟩
  | 16 => ⟨((-861138699/2251799813685248), (-225334023/2251799813685248)), (331/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (-1879447903281/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444419364284001/158456325028528675187087900672), (-4443306448485/633825300114114700748351602688)), (185275/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944256926744599/19807040628566084398385987584), (-4997498900145/39614081257132168796771975168)), (52123/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888211790865403/2475880078570760549798248448), (-5308336485123/2475880078570760549798248448)), (221587/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884938803369735/77371252455336267181195264), (-2653321258837/77371252455336267181195264)), (221661/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548321952120767/9671406556917033397649408), (-1243294503329/2417851639229258349412352)), (207885/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257710685044665/604462909807314587353088), (-4349731968857/604462909807314587353088)), (90989/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886039437175895/75557863725914323419136), (-3532471445339/37778931862957161709568)), (73965/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324056061476931/1180591620717411303424), (-2647879115995/2361183241434822606848)), (222023/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619638485342409/590295810358705651712), (-7276877756607/590295810358705651712)), (152745/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821210756971763/73786976294838206464), (-9088916342669/73786976294838206464)), (382175/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910053767082705/4611686018427387904), (-10215163494535/9223372036854775808)), (430377/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591352901925661/1152921504606846976), (-10202838679953/1152921504606846976)), (107729/288230376151711744), by norm_num⟩
  | 5 => ⟨((298068352203405/36028797018963968), (-2228407847115/36028797018963968)), (377657/144115188075855872), by norm_num⟩
  | 4 => ⟨((744084689809753/18014398509481984), (-13342774574547/36028797018963968)), (141925/9007199254740992), by norm_num⟩
  | 3 => ⟨((742455253888965/4503599627370496), (-4157528563383/2251799813685248)), (711753/9007199254740992), by norm_num⟩
  | 2 => ⟨((69350551595283/140737488355328), (-16557729188971/2251799813685248)), (714953/2251799813685248), by norm_num⟩
  | 1 => ⟨((550729776730059/562949953421312), (-24656141854683/1125899906842624)), (540225/562949953421312), by norm_num⟩
  | 0 => ⟨((538503782770793/562949953421312), (-97187082980979/2251799813685248)), (4386279/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((538503782770793/562949953421312), (-97187082980979/2251799813685248)), (16732326516158293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((128517636972439/140737488355328), (-46483361001851/562949953421312)), (8770231/2251799813685248), by norm_num⟩
  | 2 => ⟨((116399257058595/140737488355328), (-42447337836611/281474976710656)), (8732903/1125899906842624), by norm_num⟩
  | 3 => ⟨((1489109186131717/2251799813685248), (-280854157398193/1125899906842624)), (17079283/1125899906842624), by norm_num⟩
  | 4 => ⟨((844626563050385/2251799813685248), (-742912408471121/2251799813685248)), (62219551/2251799813685248), by norm_num⟩
  | 5 => ⟨((8963673378545/281474976710656), (-557317351570005/2251799813685248)), (10966335/281474976710656), by norm_num⟩
  | 6 => ⟨((-542606660355143/9007199254740992), (-283967591921581/18014398509481984)), (392112635/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1524214359/16777216)), (1/8388608), by norm_num⟩, -14, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1542786301/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-357430983161385/9007199254740992), (407731847850603/9007199254740992)), (99632233/4503599627370496), by norm_num⟩
  | 1 => ⟨((555298161/4294967296), (-316722327/2147483648)), (311/4294967296), by norm_num⟩
  | 2 => ⟨((-226151877/1073741824), (1031911917/4294967296)), (509/4294967296), by norm_num⟩
  | 3 => ⟨((30701027/134217728), (-280172387/1073741824)), (555/4294967296), by norm_num⟩
  | 4 => ⟨((-400107639/2147483648), (228207171/1073741824)), (227/2147483648), by norm_num⟩
  | 5 => ⟨((521435725/4294967296), (-594816795/4294967296)), (149/2147483648), by norm_num⟩
  | 6 => ⟨((-566295977/8589934592), (161497545/2147483648)), (325/8589934592), by norm_num⟩
  | 7 => ⟨((527156275/17179869184), (-601342391/17179869184)), (19/1073741824), by norm_num⟩
  | 8 => ⟨((-858763017/68719476736), (979615781/68719476736)), (497/68719476736), by norm_num⟩
  | 9 => ⟨((621762847/137438953472), (-709262841/137438953472)), (181/68719476736), by norm_num⟩
  | 10 => ⟨((-101288169/68719476736), (924338723/549755813888)), (237/274877906944), by norm_num⟩
  | 11 => ⟨((960019295/2199023255552), (-1095121743/2199023255552)), (141/549755813888), by norm_num⟩
  | 12 => ⟨((-130326481/1099511627776), (594668727/4398046511104)), (77/1099511627776), by norm_num⟩
  | 13 => ⟨((32662789/1099511627776), (-596150191/17592186044416)), (155/8796093022208), by norm_num⟩
  | 14 => ⟨((-243242331/35184372088832), (554947107/70368744177664)), (145/35184372088832), by norm_num⟩
  | 15 => ⟨((211335199/140737488355328), (-482152333/281474976710656)), (253/281474976710656), by norm_num⟩
  | 16 => ⟨((-43034405/140737488355328), (49090589/140737488355328)), (207/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (2983697340611/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888814644716373/316912650057057350374175801344), (3526764591007/633825300114114700748351602688)), (185095/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944229946281245/19807040628566084398385987584), (3966639145365/39614081257132168796771975168)), (208277/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888154762146157/2475880078570760549798248448), (4213345162921/2475880078570760549798248448)), (110673/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769820920518643/154742504910672534362390528), (2105992802583/77371252455336267181195264)), (221405/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387067293099365/2417851639229258349412352), (3947292459835/9671406556917033397649408)), (51907/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628832433031387/302231454903657293676544), (3452437402773/604462909807314587353088)), (181737/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885965661766215/75557863725914323419136), (5607505376531/75557863725914323419136)), (147719/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296169509025721/4722366482869645213696), (2101631481605/2361183241434822606848)), (221681/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809782093576949/295147905179352825856), (1443910970829/147573952589676412928)), (19061/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455279832364781/18446744073709551616), (7213794615941/73786976294838206464)), (95367/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820006661639777/9223372036854775808), (8107604785267/9223372036854775808)), (214747/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591254503055781/1152921504606846976), (8097721338409/1152921504606846976)), (13435/36028797018963968), by norm_num⟩
  | 5 => ⟨((298047521234687/36028797018963968), (7074400005027/144115188075855872)), (188331/72057594037927936), by norm_num⟩
  | 4 => ⟨((372012481198761/9007199254740992), (10589419432159/36028797018963968)), (565957/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484770825171891/9007199254740992), (1649753709329/1125899906842624)), (44321/562949953421312), by norm_num⟩
  | 2 => ⟨((2218967020825615/4503599627370496), (13140055380275/2251799813685248)), (177919/562949953421312), by norm_num⟩
  | 1 => ⟨((2202614396251299/2251799813685248), (39131291686379/2251799813685248)), (2147769/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153687047105645/2251799813685248), (38556528276179/1125899906842624)), (2173375/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153687047105645/2251799813685248), (38556528276179/1125899906842624)), (8290767673972701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((514302097951423/562949953421312), (147506354739181/2251799813685248)), (2153107/562949953421312), by norm_num⟩
  | 2 => ⟨((934885112130983/1125899906842624), (33689863211851/281474976710656)), (8432343/1125899906842624), by norm_num⟩
  | 3 => ⟨((1520295112471411/2251799813685248), (447587233715137/2251799813685248)), (8011023/562949953421312), by norm_num⟩
  | 4 => ⟨((234363961262273/562949953421312), (302187023769261/1125899906842624)), (56007647/2251799813685248), by norm_num⟩
  | 5 => ⟨((456128887619133/4503599627370496), (503218785273565/2251799813685248)), (153395991/4503599627370496), by norm_num⟩
  | 6 => ⟨((-357430983161385/9007199254740992), (407731847850603/9007199254740992)), (99632233/4503599627370496), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1542786301/16777216)), (1/8388608), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-390164311/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((355439786369419/18014398509481984), (987699099254719/18014398509481984)), (150984877/9007199254740992), by norm_num⟩
  | 1 => ⟨((-279300583/4294967296), (-776122833/4294967296)), (477/8589934592), by norm_num⟩
  | 2 => ⟨((460264579/4294967296), (1278987123/4294967296)), (395/4294967296), by norm_num⟩
  | 3 => ⟨((-505652323/4294967296), (-702555485/2147483648)), (109/1073741824), by norm_num⟩
  | 4 => ⟨((104159223/1073741824), (578877067/2147483648)), (361/4294967296), by norm_num⟩
  | 5 => ⟨((-549266891/8589934592), (-1526307503/8589934592)), (239/4294967296), by norm_num⟩
  | 6 => ⟨((150857839/4294967296), (419205045/4294967296)), (33/1073741824), by norm_num⟩
  | 7 => ⟨((-568231803/34359738368), (-789503681/17179869184)), (499/34359738368), by norm_num⟩
  | 8 => ⟨((468199831/68719476736), (1301037669/68719476736)), (413/68719476736), by norm_num⟩
  | 9 => ⟨((-21432087/8589934592), (-952890647/137438953472)), (19/8589934592), by norm_num⟩
  | 10 => ⟨((28254665/34359738368), (1256228849/549755813888)), (403/549755813888), by norm_num⟩
  | 11 => ⟨((-541805187/2199023255552), (-1505572855/2199023255552)), (485/2199023255552), by norm_num⟩
  | 12 => ⟨((148808459/2199023255552), (206755105/1099511627776)), (67/1099511627776), by norm_num⟩
  | 13 => ⟨((-301814403/17592186044416), (-838684427/17592186044416)), (273/17592186044416), by norm_num⟩
  | 14 => ⟨((284208867/70368744177664), (789762015/70368744177664)), (259/70368744177664), by norm_num⟩
  | 15 => ⟨((-249788283/281474976710656), (-173528451/70368744177664)), (457/562949953421312), by norm_num⟩
  | 16 => ⟨((102907679/562949953421312), (285960733/562949953421312)), (189/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (399041715315/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777583935957675/633825300114114700748351602688), (1886586119301/633825300114114700748351602688)), (46193/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236051142784947/4951760157141521099596496896), (2121890123755/39614081257132168796771975168)), (207893/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944050603056439/1237940039285380274899124224), (70432960739/77371252455336267181195264)), (110457/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769767775907815/154742504910672534362390528), (563279979175/38685626227668133590597632)), (220945/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774109893047405/4835703278458516698824704), (2111519486569/9671406556917033397649408)), (207169/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257622089405543/604462909807314587353088), (1846799473621/604462909807314587353088)), (90653/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235737120874119/9444732965739290427392), (2999587260835/75557863725914323419136)), (73671/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324029675550913/1180591620717411303424), (2248412057683/4722366482869645213696)), (55267/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404873871700869/147573952589676412928), (1544745311853/295147905179352825856)), (304057/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821035189700567/73786976294838206464), (3858751837789/73786976294838206464)), (95051/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909957193160053/4611686018427387904), (4336821630351/9223372036854775808)), (427913/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795582599078081/576460752303423488), (2165742479231/576460752303423488)), (214071/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192115275312391/144115188075855872), (3784053908383/144115188075855872)), (374883/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487944350821491/36028797018963968), (1416027696719/9007199254740992)), (281421/18014398509481984), by norm_num⟩
  | 3 => ⟨((185581303122385/1125899906842624), (882404692115/1125899906842624)), (704461/9007199254740992), by norm_num⟩
  | 2 => ⟨((277345088595623/562949953421312), (7027979288571/2251799813685248)), (1411653/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202390404731335/2251799813685248), (20928297029659/2251799813685248)), (1062169/1125899906842624), by norm_num⟩
  | 0 => ⟨((2153576528830511/2251799813685248), (41237918816329/2251799813685248)), (1069071/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153576528830511/2251799813685248), (41237918816329/2251799813685248)), (4078182222606468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1029441265472413/1125899906842624), (78878249763527/2251799813685248)), (2084033/562949953421312), by norm_num⟩
  | 2 => ⟨((1879729926354663/2251799813685248), (72120554199641/1125899906842624)), (15827923/2251799813685248), by norm_num⟩
  | 3 => ⟨((779949238234557/1125899906842624), (240815659030511/2251799813685248)), (28453025/2251799813685248), by norm_num⟩
  | 4 => ⟨((131855142096813/281474976710656), (333642428912739/2251799813685248)), (45506501/2251799813685248), by norm_num⟩
  | 5 => ⟨((889397492064013/4503599627370496), (312585298969843/2251799813685248)), (112239161/4503599627370496), by norm_num⟩
  | 6 => ⟨((355439786369419/18014398509481984), (987699099254719/18014398509481984)), (150984877/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-390164311/4194304)), (1/8388608), by norm_num⟩, -15, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨44,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile044Terms3
