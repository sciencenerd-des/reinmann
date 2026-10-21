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
namespace Reinmann.XiBand58.Tile008Terms1
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
  | 0 => ⟨((15/16), (2991/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2991/160))
  have he : value ((15/16), (2991/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-69118709/33554432), (-1378227053/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-558460036535645/4503599627370496), (66459520773811/2251799813685248)), (197432477/9007199254740992), by norm_num⟩
  | 1 => ⟨((1170217627/4294967296), (-278523431/4294967296)), (209/4294967296), by norm_num⟩
  | 2 => ⟨((-642807733/2147483648), (19124329/268435456)), (29/536870912), by norm_num⟩
  | 3 => ⟨((235398825/1073741824), (-56027261/1073741824)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((-129306021/1073741824), (123104475/4294967296)), (191/8589934592), by norm_num⟩
  | 5 => ⟨((113645747/2147483648), (-108195271/8589934592)), (85/8589934592), by norm_num⟩
  | 6 => ⟨((-1331761219/68719476736), (79243103/17179869184)), (63/17179869184), by norm_num⟩
  | 7 => ⟨((836050995/137438953472), (-99494225/68719476736)), (319/274877906944), by norm_num⟩
  | 8 => ⟨((-918495897/549755813888), (218611157/549755813888)), (177/549755813888), by norm_num⟩
  | 9 => ⟨((896951893/2199023255552), (-106741735/1099511627776)), (175/2199023255552), by norm_num⟩
  | 10 => ⟨((-394160949/4398046511104), (187628451/8796093022208)), (155/8796093022208), by norm_num⟩
  | 11 => ⟨((629861909/35184372088832), (-74956699/17592186044416)), (125/35184372088832), by norm_num⟩
  | 12 => ⟨((-922632045/281474976710656), (109797801/140737488355328)), (185/281474976710656), by norm_num⟩
  | 13 => ⟨((623763017/1125899906842624), (-148461801/1125899906842624)), (253/2251799813685248), by norm_num⟩
  | 14 => ⟨((-783169961/9007199254740992), (186402239/9007199254740992)), (5/281474976710656), by norm_num⟩
  | 15 => ⟨((917760153/72057594037927936), (-218436043/72057594037927936)), (189/72057594037927936), by norm_num⟩
  | 16 => ⟨((-504131291/288230376151711744), (239976521/576460752303423488)), (105/288230376151711744), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (946975937219/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778781022821907/633825300114114700748351602688), (4482896062063/633825300114114700748351602688)), (46321/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944877536831205/19807040628566084398385987584), (5042321029977/39614081257132168796771975168)), (52125/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889530247490993/2475880078570760549798248448), (5356337079501/2475880078570760549798248448)), (110799/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442798920222035/38685626227668133590597632), (669383367865/19342813113834066795298816)), (27709/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774778620103309/4835703278458516698824704), (5019025885513/9671406556917033397649408)), (25987/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258791155638055/604462909807314587353088), (274393652553/37778931862957161709568)), (45497/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943897219812199/37778931862957161709568), (3565852774763/37778931862957161709568)), (73969/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297539830649661/4722366482869645213696), (5346566272849/4722366482869645213696)), (55509/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621446330125577/590295810358705651712), (7347933338151/590295810358705651712)), (76377/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227933617029111/9223372036854775808), (2294881223953/18446744073709551616)), (47775/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911322874256587/4611686018427387904), (10319553692989/9223372036854775808)), (215203/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796944159377325/576460752303423488), (10310291748615/1152921504606846976)), (215475/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74655546884451/9007199254740992), (4505544743177/72057594037927936)), (188845/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491486091943485/36028797018963968), (6747906204067/18014398509481984)), (283877/36028797018963968), by norm_num⟩
  | 3 => ⟨((744522683655333/4503599627370496), (16833349382879/9007199254740992)), (88979/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113727126173157/2251799813685248), (16778769528367/2251799813685248)), (178761/1125899906842624), by norm_num⟩
  | 1 => ⟨((276898891116049/281474976710656), (97780706259/4398046511104)), (270155/562949953421312), by norm_num⟩
  | 0 => ⟨((1089113581127889/1125899906842624), (12379873057261/281474976710656)), (548391/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1089113581127889/1125899906842624), (12379873057261/281474976710656)), (2091945650340843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1051351194979759/1125899906842624), (23950775370633/281474976710656)), (2218373/1125899906842624), by norm_num⟩
  | 2 => ⟨((486793317181131/562949953421312), (178919466311859/1125899906842624)), (2260251/562949953421312), by norm_num⟩
  | 3 => ⟨((813445985400133/1125899906842624), (618859989133309/2251799813685248)), (9254653/1125899906842624), by norm_num⟩
  | 4 => ⟨((251331155721101/562949953421312), (27944822771645/70368744177664)), (36919189/2251799813685248), by norm_num⟩
  | 5 => ⟨((46856421579487/1125899906842624), (1596937318849741/4503599627370496)), (31144055/1125899906842624), by norm_num⟩
  | 6 => ⟨((-558460036535645/4503599627370496), (66459520773811/2251799813685248)), (197432477/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-1378227053/33554432)), (1/16777216), by norm_num⟩, -7, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-9054133/4194304), (-45134853/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((153711706122055/2251799813685248), (838954407661239/9007199254740992)), (32275335/2251799813685248), by norm_num⟩
  | 1 => ⟨((-675076071/4294967296), (-921136815/4294967296)), (9/268435456), by norm_num⟩
  | 2 => ⟨((777210049/4294967296), (530248975/2147483648)), (21/536870912), by norm_num⟩
  | 3 => ⟨((-298265379/2147483648), (-813962257/4294967296)), (131/4294967296), by norm_num⟩
  | 4 => ⟨((85847677/1073741824), (117138585/1073741824)), (153/8589934592), by norm_num⟩
  | 5 => ⟨((-158137265/4294967296), (-863108991/17179869184)), (143/17179869184), by norm_num⟩
  | 6 => ⟨((485499345/34359738368), (82807579/4294967296)), (7/2147483648), by norm_num⟩
  | 7 => ⟨((-638802031/137438953472), (-871641129/137438953472)), (75/68719476736), by norm_num⟩
  | 8 => ⟨((735448017/549755813888), (1003513935/549755813888)), (175/549755813888), by norm_num⟩
  | 9 => ⟨((-752636285/2199023255552), (-256741803/549755813888)), (91/1099511627776), by norm_num⟩
  | 10 => ⟨((173300909/2199023255552), (945871757/8796093022208)), (85/4398046511104), by norm_num⟩
  | 11 => ⟨((-580421949/35184372088832), (-395990947/17592186044416)), (145/35184372088832), by norm_num⟩
  | 12 => ⟨((445490309/140737488355328), (75983571/17592186044416)), (113/140737488355328), by norm_num⟩
  | 13 => ⟨((-157812207/281474976710656), (-861334833/1125899906842624)), (81/562949953421312), by norm_num⟩
  | 14 => ⟨((830573795/9007199254740992), (1133312427/9007199254740992)), (27/1125899906842624), by norm_num⟩
  | 15 => ⟨((-509991157/36028797018963968), (-695879547/36028797018963968)), (67/18014398509481984), by norm_num⟩
  | 16 => ⟨((293574509/144115188075855872), (100145117/36028797018963968)), (39/72057594037927936), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581163853822105/10141204801825835211973625643008), (1222301824869/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889319199322441/316912650057057350374175801344), (723164998957/316912650057057350374175801344)), (92343/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889595197417993/39614081257132168796771975168), (1626814428311/39614081257132168796771975168)), (103895/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889361126264721/2475880078570760549798248448), (1728109721275/2475880078570760549798248448)), (110399/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771027399750559/154742504910672534362390528), (1727681690565/154742504910672534362390528)), (110411/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549400368686093/9671406556917033397649408), (1619246943001/9671406556917033397649408)), (103523/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9833240503805/4722366482869645213696), (708193295779/302231454903657293676544)), (90595/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887574506624639/75557863725914323419136), (143798524433/4722366482869645213696)), (147241/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648688170473211/2361183241434822606848), (862418643289/2361183241434822606848)), (27613/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405305975476557/147573952589676412928), (148152578959/36893488147419103232)), (4747/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1823194451852203/73786976294838206464), (1480618836303/36893488147419103232)), (189931/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822341829096249/9223372036854775808), (3328900049709/9223372036854775808)), (213743/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796795241642143/576460752303423488), (831446829271/288230376151711744)), (106915/576460752303423488), by norm_num⟩
  | 5 => ⟨((597117487104629/72057594037927936), (2906565763203/144115188075855872)), (2925/2251799813685248), by norm_num⟩
  | 4 => ⟨((745559526198307/18014398509481984), (136026924029/1125899906842624)), (280997/36028797018963968), by norm_num⟩
  | 3 => ⟨((186076291253207/1125899906842624), (5428870257403/9007199254740992)), (43949/1125899906842624), by norm_num⟩
  | 2 => ⟨((2226655142804385/4503599627370496), (10821202985485/4503599627370496)), (22007/140737488355328), by norm_num⟩
  | 1 => ⟨((1107084377350959/1125899906842624), (16140749088991/2251799813685248)), (529473/1125899906842624), by norm_num⟩
  | 0 => ⟨((544220214769183/562949953421312), (7979750603007/562949953421312)), (1064191/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((544220214769183/562949953421312), (7979750603007/562949953421312)), (4059566502097701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052001031154253/1125899906842624), (61714069758139/2251799813685248)), (2087739/1125899906842624), by norm_num⟩
  | 2 => ⟨((1964213703594601/2251799813685248), (14415860732317/281474976710656)), (4015855/1125899906842624), by norm_num⟩
  | 3 => ⟨((426862454581899/562949953421312), (201196081658341/2251799813685248)), (7417297/1125899906842624), by norm_num⟩
  | 4 => ⟨((1276714298207203/2251799813685248), (152558949062857/1125899906842624)), (25147873/2251799813685248), by norm_num⟩
  | 5 => ⟨((682521802404271/2251799813685248), (345988467366023/2251799813685248)), (70662971/4503599627370496), by norm_num⟩
  | 6 => ⟨((153711706122055/2251799813685248), (838954407661239/9007199254740992)), (32275335/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9054133/4194304), (-45134853/1048576)), (1/16777216), by norm_num⟩, -7, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-75431263/33554432), (-188012423/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((632526760193363/9007199254740992), (-710452343389459/9007199254740992)), (112208439/9007199254740992), by norm_num⟩
  | 1 => ⟨((-723234619/4294967296), (812335165/4294967296)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((867120437/4294967296), (-486973663/2147483648)), (79/2147483648), by norm_num⟩
  | 3 => ⟨((-693087999/4294967296), (778474563/4294967296)), (1/33554432), by norm_num⟩
  | 4 => ⟨((415488109/4294967296), (-933350237/8589934592)), (39/2147483648), by norm_num⟩
  | 5 => ⟨((-398518789/8589934592), (55951903/1073741824)), (19/2147483648), by norm_num⟩
  | 6 => ⟨((19908465/1073741824), (-357778143/17179869184)), (31/8589934592), by norm_num⟩
  | 7 => ⟨((-872931001/137438953472), (980473735/137438953472)), (43/34359738368), by norm_num⟩
  | 8 => ⟨((32706205/17179869184), (-293884167/137438953472)), (105/274877906944), by norm_num⟩
  | 9 => ⟨((-557696387/1099511627776), (626403071/1099511627776)), (57/549755813888), by norm_num⟩
  | 10 => ⟨((133729753/1099511627776), (-600819585/4398046511104)), (111/4398046511104), by norm_num⟩
  | 11 => ⟨((-932858015/35184372088832), (1047783595/35184372088832)), (49/8796093022208), by norm_num⟩
  | 12 => ⟨((745631941/140737488355328), (-13085809/2199023255552)), (159/140737488355328), by norm_num⟩
  | 13 => ⟨((-550137633/562949953421312), (617913099/562949953421312)), (119/562949953421312), by norm_num⟩
  | 14 => ⟨((753812817/4503599627370496), (-423340257/2251799813685248)), (165/4503599627370496), by norm_num⟩
  | 15 => ⟨((-964034235/36028797018963968), (1082800641/36028797018963968)), (213/36028797018963968), by norm_num⟩
  | 16 => ⟨((144478321/36028797018963968), (-649110635/144115188075855872)), (65/72057594037927936), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790523730590695/5070602400912917605986812821504), (-549283714325/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222312612320177/79228162514264337593543950336), (-324931341591/158456325028528675187087900672)), (92329/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889440551843613/39614081257132168796771975168), (-1461904709727/39614081257132168796771975168)), (51939/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889196868161051/2475880078570760549798248448), (-1552917615637/2475880078570760549798248448)), (110379/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442715800259859/38685626227668133590597632), (-776258557849/77371252455336267181195264)), (55195/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549246495473765/9671406556917033397649408), (-1455059404215/9671406556917033397649408)), (51751/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258520208477211/604462909807314587353088), (-636375871915/302231454903657293676544)), (5661/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((471838984692227/18889465931478580854784), (-2067424601625/75557863725914323419136)), (147207/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648606259192281/2361183241434822606848), (-387467856247/1180591620717411303424)), (13803/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620998813681873/590295810358705651712), (-266242645747/73786976294838206464)), (18983/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455728335767885/18446744073709551616), (-1330364742081/36893488147419103232)), (189875/73786976294838206464), by norm_num⟩
  | 7 => ⟨((3558644389081/18014398509481984), (-186936819017/576460752303423488)), (26709/1152921504606846976), by norm_num⟩
  | 6 => ⟨((12447461037353/9007199254740992), (-1494038652341/576460752303423488)), (213751/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596979711082737/72057594037927936), (-163205969823/9007199254740992)), (187121/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490706691975389/36028797018963968), (-3910408141669/36028797018963968)), (280859/36028797018963968), by norm_num⟩
  | 3 => ⟨((744048284586893/4503599627370496), (-2438297085921/4503599627370496)), (351385/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225632675341003/4503599627370496), (-9719022101533/4503599627370496)), (703707/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106323818747429/1125899906842624), (-14493403107455/2251799813685248)), (528957/1125899906842624), by norm_num⟩
  | 0 => ⟨((2173888651973677/2251799813685248), (-7161998558307/562949953421312)), (265661/281474976710656), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2173888651973677/2251799813685248), (-7161998558307/562949953421312)), (1013416291356944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((65572147206571/70368744177664), (-13828393888953/562949953421312)), (2078793/1125899906842624), by norm_num⟩
  | 2 => ⟨((1953921403955305/2251799813685248), (-51543195224717/1125899906842624)), (7952635/2251799813685248), by norm_num⟩
  | 3 => ⟨((422682116967141/562949953421312), (-22362412450199/281474976710656)), (14529385/2251799813685248), by norm_num⟩
  | 4 => ⟨((313810954184839/562949953421312), (-67161862453293/562949953421312)), (1507935/140737488355328), by norm_num⟩
  | 5 => ⟨((1335345689287295/4503599627370496), (-599019589949955/4503599627370496)), (65311071/4503599627370496), by norm_num⟩
  | 6 => ⟨((632526760193363/9007199254740992), (-710452343389459/9007199254740992)), (112208439/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75431263/33554432), (-188012423/4194304)), (1/16777216), by norm_num⟩, -7, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-19542101/8388608), (-1558677981/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-343139234766957/4503599627370496), (-545570549426247/9007199254740992)), (19995109/1125899906842624), by norm_num⟩
  | 1 => ⟨((813168493/4294967296), (323222133/2147483648)), (3/67108864), by norm_num⟩
  | 2 => ⟨((-505161949/2147483648), (-803176827/4294967296)), (241/4294967296), by norm_num⟩
  | 3 => ⟨((209213381/1073741824), (332636573/2147483648)), (201/4294967296), by norm_num⟩
  | 4 => ⟨((-1039751443/8589934592), (-51660677/536870912)), (63/2147483648), by norm_num⟩
  | 5 => ⟨((516737055/8589934592), (821580543/17179869184)), (253/17179869184), by norm_num⟩
  | 6 => ⟨((-26750903/1073741824), (-680516985/34359738368)), (53/8589934592), by norm_num⟩
  | 7 => ⟨((151939421/17179869184), (483148909/68719476736)), (19/8589934592), by norm_num⟩
  | 8 => ⟨((-755110555/274877906944), (-37518123/17179869184)), (191/274877906944), by norm_num⟩
  | 9 => ⟨((104243291/137438953472), (662962015/1099511627776)), (213/1099511627776), by norm_num⟩
  | 10 => ⟨((-414455755/2199023255552), (-5148121/34359738368)), (107/2199023255552), by norm_num⟩
  | 11 => ⟨((749006445/17592186044416), (595437387/17592186044416)), (49/4398046511104), by norm_num⟩
  | 12 => ⟨((-310201849/35184372088832), (-493202107/70368744177664)), (165/70368744177664), by norm_num⟩
  | 13 => ⟨((59294049/35184372088832), (754191505/562949953421312)), (255/562949953421312), by norm_num⟩
  | 14 => ⟨((-673555093/2251799813685248), (-535455853/2251799813685248)), (183/2251799813685248), by norm_num⟩
  | 15 => ⟨((446325741/9007199254740992), (44351927/1125899906842624)), (245/18014398509481984), by norm_num⟩
  | 16 => ⟨((-554538901/72057594037927936), (-440841593/72057594037927936)), (307/144115188075855872), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790470601517375/5070602400912917605986812821504), (-3217355084615/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889184168205661/316912650057057350374175801344), (-3805970197493/633825300114114700748351602688)), (92575/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944645533025103/19807040628566084398385987584), (-4280832773973/39614081257132168796771975168)), (104171/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889037571456413/2475880078570760549798248448), (-2273651130037/1237940039285380274899124224)), (110709/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885351689144897/77371252455336267181195264), (-4546084603499/154742504910672534362390528)), (110741/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774548051570175/4835703278458516698824704), (-2130330423129/4835703278458516698824704)), (103853/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629194028574615/302231454903657293676544), (-3726785097477/604462909807314587353088)), (90905/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235892518442481/9444732965739290427392), (-6053601834207/75557863725914323419136)), (73891/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297049761303035/4722366482869645213696), (-2269040557053/2361183241434822606848)), (27723/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810386769932129/295147905179352825856), (-6236417408263/590295810358705651712)), (152565/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822629529817475/73786976294838206464), (-3895178926293/36893488147419103232)), (23855/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821703588746769/9223372036854775808), (-4378527956409/4611686018427387904)), (214879/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199118608945915/144115188075855872), (-2187047656817/288230376151711744)), (215109/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149208722676179/18014398509481984), (-7644700990335/144115188075855872)), (188479/144115188075855872), by norm_num⟩
  | 4 => ⟨((745131861831373/18014398509481984), (-11447138967155/36028797018963968)), (283237/36028797018963968), by norm_num⟩
  | 3 => ⟨((371882008080351/2251799813685248), (-892132486617/562949953421312)), (88739/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112225683028307/2251799813685248), (-7110999949395/1125899906842624)), (356321/2251799813685248), by norm_num⟩
  | 1 => ⟨((552691483811685/562949953421312), (-21203001251915/1125899906842624)), (537905/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084845688234463/1125899906842624), (-41887815863833/1125899906842624)), (544777/562949953421312), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1084845688234463/1125899906842624), (-41887815863833/1125899906842624)), (2078159334422874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2087460121492525/2251799813685248), (-161441762818407/2251799813685248)), (4361443/2251799813685248), by norm_num⟩
  | 2 => ⟨((961769845106913/1125899906842624), (-299319006759617/2251799813685248)), (8711661/2251799813685248), by norm_num⟩
  | 3 => ⟨((1603345488385849/2251799813685248), (-511370492206623/2251799813685248)), (17199391/2251799813685248), by norm_num⟩
  | 4 => ⟨((512749170861773/1125899906842624), (-45513791156645/140737488355328)), (32304673/2251799813685248), by norm_num⟩
  | 5 => ⟨((463044288603211/4503599627370496), (-1326563885774341/4503599627370496)), (3144891/140737488355328), by norm_num⟩
  | 6 => ⟨((-343139234766957/4503599627370496), (-545570549426247/9007199254740992)), (19995109/1125899906842624), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19542101/8388608), (-1558677981/33554432)), (1/16777216), by norm_num⟩, -7, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-40343165/16777216), (-1608885423/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-276055891110855/4503599627370496), (149307062181565/2251799813685248)), (74310027/4503599627370496), by norm_num⟩
  | 1 => ⟨((675267583/4294967296), (-730447871/4294967296)), (23/536870912), by norm_num⟩
  | 2 => ⟨((-866013577/4294967296), (936780899/4294967296)), (119/2147483648), by norm_num⟩
  | 3 => ⟨((740426989/4294967296), (-800931855/4294967296)), (103/2147483648), by norm_num⟩
  | 4 => ⟨((-949578865/8589934592), (128396853/1073741824)), (267/8589934592), by norm_num⟩
  | 5 => ⟨((121781085/2147483648), (-526930281/8589934592)), (69/4294967296), by norm_num⟩
  | 6 => ⟨((-832966175/34359738368), (901032991/34359738368)), (239/34359738368), by norm_num⟩
  | 7 => ⟨((610433159/68719476736), (-330157713/34359738368)), (177/68719476736), by norm_num⟩
  | 8 => ⟨((-391432535/137438953472), (423418907/137438953472)), (229/274877906944), by norm_num⟩
  | 9 => ⟨((892448559/1099511627776), (-60336003/68719476736)), (33/137438953472), by norm_num⟩
  | 10 => ⟨((-915634143/4398046511104), (495228135/2199023255552)), (273/4398046511104), by norm_num⟩
  | 11 => ⟨((854020075/17592186044416), (-115475917/2199023255552)), (257/17592186044416), by norm_num⟩
  | 12 => ⟨((-182543187/17592186044416), (394919839/35184372088832)), (111/35184372088832), by norm_num⟩
  | 13 => ⟨((288131711/140737488355328), (-623353469/281474976710656)), (177/281474976710656), by norm_num⟩
  | 14 => ⟨((-422310427/1125899906842624), (456820023/1125899906842624)), (131/1125899906842624), by norm_num⟩
  | 15 => ⟨((288854629/4503599627370496), (-624917453/9007199254740992)), (181/9007199254740992), by norm_num⟩
  | 16 => ⟨((-740897495/72057594037927936), (400720405/36028797018963968)), (117/36028797018963968), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395210863750315/2535301200456458802993406410752), (754524901547/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778253643996645/633825300114114700748351602688), (3569818588805/633825300114114700748351602688)), (11569/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889162117121597/39614081257132168796771975168), (2007597235901/19807040628566084398385987584)), (6509/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944450332549471/1237940039285380274899124224), (4265096396779/2475880078570760549798248448)), (55339/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442641646621799/38685626227668133590597632), (4263917980615/154742504910672534362390528)), (27677/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548967982480555/9671406556917033397649408), (3996171359509/9671406556917033397649408)), (25955/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258276073160285/604462909807314587353088), (1747699275885/302231454903657293676544)), (45437/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943479200697089/37778931862957161709568), (5677677058435/75557863725914323419136)), (9233/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1296913650908799/4722366482869645213696), (4256206168045/4722366482869645213696)), (433/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1620586711530787/590295810358705651712), (2924475510675/295147905179352825856)), (152499/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822396479123563/73786976294838206464), (7306192593235/73786976294838206464)), (95375/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821442072454859/9223372036854775808), (8212600987187/9223372036854775808)), (107383/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592688186316455/1152921504606846976), (4102012497157/576460752303423488)), (214981/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193442615179961/144115188075855872), (3584441137281/72057594037927936)), (2943/2251799813685248), by norm_num⟩
  | 4 => ⟨((744962418580461/18014398509481984), (10734065208799/36028797018963968)), (141507/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487107675428329/9007199254740992), (13383926868903/9007199254740992)), (88655/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223620371050011/4503599627370496), (13333539308133/2251799813685248)), (711803/4503599627370496), by norm_num⟩
  | 1 => ⟨((552385904405303/562949953421312), (39749340716877/2251799813685248)), (1074129/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083671354852417/1125899906842624), (78497534383929/2251799813685248)), (1087031/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1083671354852417/1125899906842624), (78497534383929/2251799813685248)), (4146694187644576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2083316878301361/2251799813685248), (151106735015117/2251799813685248)), (4336617/2251799813685248), by norm_num⟩
  | 2 => ⟨((1917300083164441/2251799813685248), (279601418890611/2251799813685248)), (8606307/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597771983810827/2251799813685248), (238067265319881/1125899906842624)), (1049561/140737488355328), by norm_num⟩
  | 4 => ⟨((516513769751201/1125899906842624), (675685652834383/2251799813685248)), (15466323/1125899906842624), by norm_num⟩
  | 5 => ⟨((542317120921041/4503599627370496), (1239900426640931/4503599627370496)), (93889379/4503599627370496), by norm_num⟩
  | 6 => ⟨((-276055891110855/4503599627370496), (149307062181565/2251799813685248)), (74310027/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40343165/16777216), (-1608885423/33554432)), (1/16777216), by norm_num⟩, -8, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-83017565/33554432), (-1655370253/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((905251825857871/18014398509481984), (1217901210200675/18014398509481984)), (188613125/18014398509481984), by norm_num⟩
  | 1 => ⟨((-569584719/4294967296), (-766303805/4294967296)), (15/536870912), by norm_num⟩
  | 2 => ⟨((187895841/1073741824), (252789959/1073741824)), (161/4294967296), by norm_num⟩
  | 3 => ⟨((-661157195/4294967296), (-889502925/4294967296)), (9/268435456), by norm_num⟩
  | 4 => ⟨((872415871/8589934592), (1173724607/8589934592)), (193/8589934592), by norm_num⟩
  | 5 => ⟨((-115117775/2147483648), (-619505305/8589934592)), (13/1073741824), by norm_num⟩
  | 6 => ⟨((405069877/17179869184), (544970005/17179869184)), (185/34359738368), by norm_num⟩
  | 7 => ⟨((-152714661/17179869184), (-205458155/17179869184)), (71/34359738368), by norm_num⟩
  | 8 => ⟨((806045491/274877906944), (1084431699/274877906944)), (95/137438953472), by norm_num⟩
  | 9 => ⟨((-472711169/549755813888), (-635972761/549755813888)), (113/549755813888), by norm_num⟩
  | 10 => ⟨((249502375/1099511627776), (335673715/1099511627776)), (121/2199023255552), by norm_num⟩
  | 11 => ⟨((-239436753/4398046511104), (-322131701/4398046511104)), (59/4398046511104), by norm_num⟩
  | 12 => ⟨((105314553/8796093022208), (566749351/35184372088832)), (105/35184372088832), by norm_num⟩
  | 13 => ⟨((-342069099/140737488355328), (-920420941/281474976710656)), (173/281474976710656), by norm_num⟩
  | 14 => ⟨((515851407/1125899906842624), (347006233/562949953421312)), (33/281474976710656), by norm_num⟩
  | 15 => ⟨((-726059433/9007199254740992), (-122102579/1125899906842624)), (47/2251799813685248), by norm_num⟩
  | 16 => ⟨((479028117/36028797018963968), (161117853/9007199254740992)), (125/36028797018963968), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395188238617879/2535301200456458802993406410752), (1213518883939/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778152330699239/633825300114114700748351602688), (1435189638011/633825300114114700748351602688)), (46171/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236131060346245/4951760157141521099596496896), (403560522117/9903520314283042199192993792)), (51947/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888780380449243/2475880078570760549798248448), (214337433721/309485009821345068724781056)), (110397/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770446809693573/154742504910672534362390528), (1714212840307/154742504910672534362390528)), (55205/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193607028868903/1208925819614629174706176), (803278840167/4835703278458516698824704)), (103521/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258178829356525/604462909807314587353088), (1405221322539/604462909807314587353088)), (45297/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886801389520011/75557863725914323419136), (71328636875/2361183241434822606848)), (73619/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296796774233549/4722366482869645213696), (213880061837/590295810358705651712)), (55225/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810213719007867/295147905179352825856), (1175652740099/295147905179352825856)), (75951/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822199532108321/73786976294838206464), (734267627293/18446744073709551616)), (23741/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821223451414373/9223372036854775808), (3301372347805/9223372036854775808)), (106869/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592473238439523/1152921504606846976), (1648917964657/576460752303423488)), (213825/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596629329052993/72057594037927936), (2881632843833/144115188075855872)), (46799/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489657121251583/36028797018963968), (1078628563225/9007199254740992)), (280989/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486787359029851/9007199254740992), (5379283896793/9007199254740992)), (351581/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223022500329521/4503599627370496), (10717100236695/4503599627370496)), (88025/562949953421312), by norm_num⟩
  | 1 => ⟨((552188234359061/562949953421312), (3993090679153/562949953421312)), (132363/281474976710656), by norm_num⟩
  | 0 => ⟨((541545299402377/562949953421312), (31533854818795/2251799813685248)), (2128287/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((541545299402377/562949953421312), (31533854818795/2251799813685248)), (8118770607955168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083376403339989/2251799813685248), (60669730036819/2251799813685248)), (2077169/1125899906842624), by norm_num⟩
  | 2 => ⟨((1925915614476249/2251799813685248), (28065968206307/562949953421312)), (494443/140737488355328), by norm_num⟩
  | 3 => ⟨((1641596981435049/2251799813685248), (192033718363123/2251799813685248)), (14321183/2251799813685248), by norm_num⟩
  | 4 => ⟨((1180372999551115/2251799813685248), (34998889608523/281474976710656)), (11661677/1125899906842624), by norm_num⟩
  | 5 => ⟨((1167852830036689/4503599627370496), (293537598197493/2251799813685248)), (30251881/2251799813685248), by norm_num⟩
  | 6 => ⟨((905251825857871/18014398509481984), (1217901210200675/18014398509481984)), (188613125/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-83017565/33554432), (-1655370253/33554432)), (1/16777216), by norm_num⟩, -8, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-85187893/33554432), (-1698646595/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1332192088986255/18014398509481984), (-498600251224499/18014398509481984)), (121409459/18014398509481984), by norm_num⟩
  | 1 => ⟨((-860129131/4294967296), (321920993/4294967296)), (5/268435456), by norm_num⟩
  | 2 => ⟨((1164636433/4294967296), (-435889105/4294967296)), (55/2147483648), by norm_num⟩
  | 3 => ⟨((-1051297975/4294967296), (393469859/4294967296)), (51/2147483648), by norm_num⟩
  | 4 => ⟨((711741923/4294967296), (-532768065/8589934592)), (35/2147483648), by norm_num⟩
  | 5 => ⟨((-770973143/8589934592), (288552533/8589934592)), (77/8589934592), by norm_num⟩
  | 6 => ⟨((347972329/8589934592), (-520943163/34359738368)), (71/17179869184), by norm_num⟩
  | 7 => ⟨((-269236153/17179869184), (403068639/68719476736)), (7/4294967296), by norm_num⟩
  | 8 => ⟨((364552509/68719476736), (-272882527/137438953472)), (77/137438953472), by norm_num⟩
  | 9 => ⟨((-438767331/274877906944), (164217685/274877906944)), (95/549755813888), by norm_num⟩
  | 10 => ⟨((950563167/2199023255552), (-88941947/549755813888)), (13/274877906944), by norm_num⟩
  | 11 => ⟨((-936062827/8796093022208), (175170369/4398046511104)), (13/1099511627776), by norm_num⟩
  | 12 => ⟨((105621047/4398046511104), (-316246769/35184372088832)), (3/1099511627776), by norm_num⟩
  | 13 => ⟨((-1408133403/281474976710656), (527022847/281474976710656)), (81/140737488355328), by norm_num⟩
  | 14 => ⟨((1089513127/1125899906842624), (-407772665/1125899906842624)), (127/1125899906842624), by norm_num⟩
  | 15 => ⟨((-786788331/4503599627370496), (294471693/4503599627370496)), (47/2251799813685248), by norm_num⟩
  | 16 => ⟨((1065331149/36028797018963968), (-24920129/2251799813685248)), (129/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580668700488663/10141204801825835211973625643008), (-466505599375/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889026816211099/316912650057057350374175801344), (-137915547549/158456325028528675187087900672)), (92255/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888937523487945/39614081257132168796771975168), (-620483934031/39614081257132168796771975168)), (51895/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888662585653171/2475880078570760549798248448), (-659093536753/2475880078570760549798248448)), (110281/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770329126669291/154742504910672534362390528), (-658901656183/154742504910672534362390528)), (55143/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548746021797425/9671406556917033397649408), (-154379127031/2417851639229258349412352)), (51699/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258082514942769/604462909807314587353088), (-540123238479/604462909807314587353088)), (45239/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886645100782943/75557863725914323419136), (-219329625333/18889465931478580854784)), (36759/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648339875955571/2361183241434822606848), (-657655022639/4722366482869645213696)), (55143/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620266847606369/590295810358705651712), (-225933374025/147573952589676412928)), (151655/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821999266427355/73786976294838206464), (-564427122535/36893488147419103232)), (47397/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820998801012017/9223372036854775808), (-1268844664749/9223372036854775808)), (106657/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398062349300249/288230376151711744), (-1267450709801/1152921504606846976)), (53337/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193063705345037/144115188075855872), (-553726613329/72057594037927936)), (93359/72057594037927936), by norm_num⟩
  | 4 => ⟨((744683251899449/18014398509481984), (-829026340553/18014398509481984)), (280153/36028797018963968), by norm_num⟩
  | 3 => ⟨((743213623271401/4503599627370496), (-16149256607/70368744177664)), (350327/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111155854483529/2251799813685248), (-2058936331873/2251799813685248)), (87633/562949953421312), by norm_num⟩
  | 1 => ⟨((2207710179698485/2251799813685248), (-6136126940371/2251799813685248)), (526315/1125899906842624), by norm_num⟩
  | 0 => ⟨((270523559464047/281474976710656), (-12110485159953/2251799813685248)), (2109453/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((270523559464047/281474976710656), (-12110485159953/2251799813685248)), (8046924599654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079920722122463/2251799813685248), (-5819649743989/562949953421312)), (4077451/2251799813685248), by norm_num⟩
  | 2 => ⟨((960460226272307/1125899906842624), (-43003503329037/2251799813685248)), (3808373/1125899906842624), by norm_num⟩
  | 3 => ⟨((1637839234771847/2251799813685248), (-18342285263055/562949953421312)), (3321501/562949953421312), by norm_num⟩
  | 4 => ⟨((1188886468428091/2251799813685248), (-53364804946925/1125899906842624)), (10096423/1125899906842624), by norm_num⟩
  | 5 => ⟨((1245279279856359/4503599627370496), (-112700416983997/2251799813685248)), (46473361/4503599627370496), by norm_num⟩
  | 6 => ⟨((1332192088986255/18014398509481984), (-498600251224499/18014398509481984)), (121409459/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-85187893/33554432), (-1698646595/33554432)), (1/16777216), by norm_num⟩, -8, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand58.Tile008Terms1
