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
namespace Reinmann.XiBand97.Tile018Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27177/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27177/1280))
  have he : value ((69/80), (27177/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-550536877/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-1178984851189287/18014398509481984), (-211405353395525/9007199254740992)), (222297457/9007199254740992), by norm_num⟩
  | 1 => ⟨((868866975/4294967296), (311595403/4294967296)), (329/4294967296), by norm_num⟩
  | 2 => ⟨((-1342852353/4294967296), (-481577309/4294967296)), (511/4294967296), by norm_num⟩
  | 3 => ⟨((21618821/67108864), (496191969/4294967296)), (33/268435456), by norm_num⟩
  | 4 => ⟨((-133649387/536870912), (-191718805/2147483648)), (205/2147483648), by norm_num⟩
  | 5 => ⟨((1321970973/8589934592), (118522193/2147483648)), (509/8589934592), by norm_num⟩
  | 6 => ⟨((-1362089467/17179869184), (-244238087/8589934592)), (527/17179869184), by norm_num⟩
  | 7 => ⟨((1202936105/34359738368), (431400169/34359738368)), (467/34359738368), by norm_num⟩
  | 8 => ⟨((-464790821/34359738368), (-333369059/68719476736)), (363/68719476736), by norm_num⟩
  | 9 => ⟨((638528071/137438953472), (457981295/274877906944)), (125/68719476736), by norm_num⟩
  | 10 => ⟨((-394743475/274877906944), (-283127925/549755813888)), (155/274877906944), by norm_num⟩
  | 11 => ⟨((13865555/34359738368), (318240159/2199023255552)), (351/2199023255552), by norm_num⟩
  | 12 => ⟨((-457162871/4398046511104), (-327897947/8796093022208)), (363/8796093022208), by norm_num⟩
  | 13 => ⟨((869606057/35184372088832), (155930227/17592186044416)), (347/35184372088832), by norm_num⟩
  | 14 => ⟨((-1535993851/281474976710656), (-275421115/140737488355328)), (615/281474976710656), by norm_num⟩
  | 15 => ⟨((39565185/35184372088832), (454047125/1125899906842624)), (509/1125899906842624), by norm_num⟩
  | 16 => ⟨((-244595333/1125899906842624), (-350869735/4503599627370496)), (395/4503599627370496), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-3643739436567/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888923941519231/316912650057057350374175801344), (-2153983672189/316912650057057350374175801344)), (5789/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((944352784747593/19807040628566084398385987584), (-2422662170653/19807040628566084398385987584)), (52115/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118025967454527/154742504910672534362390528), (-2573377415977/1237940039285380274899124224)), (221551/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885040641992387/77371252455336267181195264), (-643147200939/19342813113834066795298816)), (110811/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548512887630181/9671406556917033397649408), (-2410964321251/4835703278458516698824704)), (207847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257877741652449/604462909807314587353088), (-4217512687891/604462909807314587353088)), (90971/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943155440808249/37778931862957161709568), (-6850318770365/75557863725914323419136)), (295797/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296427809393167/4722366482869645213696), (-2567496595345/2361183241434822606848)), (55493/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619918352668943/590295810358705651712), (-7056155524519/590295810358705651712)), (305413/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455390135512633/18446744073709551616), (-4406753828107/36893488147419103232)), (191035/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56890655446183/288230376151711744), (-9906007390297/9223372036854775808)), (430245/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795873127994199/576460752303423488), (-77301014251/9007199254740992)), (215383/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192617495546765/144115188075855872), (-8644812800205/144115188075855872)), (94377/36028797018963968), by norm_num⟩
  | 4 => ⟨((372171327605513/9007199254740992), (-3235361569839/9007199254740992)), (567439/36028797018963968), by norm_num⟩
  | 3 => ⟨((742777532722609/4503599627370496), (-16131769762591/9007199254740992)), (11115/140737488355328), by norm_num⟩
  | 2 => ⟨((1110252835380933/2251799813685248), (-2008042715129/281474976710656)), (714459/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102424149852907/1125899906842624), (-5982098613579/281474976710656)), (269865/281474976710656), by norm_num⟩
  | 0 => ⟨((1078930794244089/1125899906842624), (-47187029554131/1125899906842624)), (2190143/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1078930794244089/1125899906842624), (-47187029554131/1125899906842624)), (8354732517722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((515971728902737/562949953421312), (-11304632624411/140737488355328)), (8762269/2251799813685248), by norm_num⟩
  | 2 => ⟨((1877126788418431/2251799813685248), (-331560320309315/2251799813685248)), (272965/35184372088832), by norm_num⟩
  | 3 => ⟨((1515975227037493/2251799813685248), (-552785159183965/2251799813685248)), (34270573/2251799813685248), by norm_num⟩
  | 4 => ⟨((442448179600005/1125899906842624), (-744301160435217/2251799813685248)), (62969723/2251799813685248), by norm_num⟩
  | 5 => ⟨((25430474293067/562949953421312), (-584980408129235/2251799813685248)), (45559165/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1178984851189287/18014398509481984), (-211405353395525/9007199254740992)), (222297457/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-550536877/8388608)), (1/8388608), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-558454055/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-995219403738457/18014398509481984), (680085474126805/18014398509481984)), (27561693/1125899906842624), by norm_num⟩
  | 1 => ⟨((743986293/4294967296), (-127101187/1073741824)), (83/1073741824), by norm_num⟩
  | 2 => ⟨((-1166382359/4294967296), (797050073/4294967296)), (261/2147483648), by norm_num⟩
  | 3 => ⟨((1219061713/4294967296), (-833048631/4294967296)), (137/1073741824), by norm_num⟩
  | 4 => ⟨((-955590237/4294967296), (653004791/4294967296)), (431/4294967296), by norm_num⟩
  | 5 => ⟨((149812383/1073741824), (-409498549/4294967296)), (271/4294967296), by norm_num⟩
  | 6 => ⟨((-1252628961/17179869184), (106998361/2147483648)), (569/17179869184), by norm_num⟩
  | 7 => ⟨((280543633/8589934592), (-766840553/34359738368)), (1/67108864), by norm_num⟩
  | 8 => ⟨((-439821469/34359738368), (300553015/34359738368)), (101/17179869184), by norm_num⟩
  | 9 => ⟨((612914521/137438953472), (-418836551/137438953472)), (565/274877906944), by norm_num⟩
  | 10 => ⟨((-384357987/274877906944), (525303833/549755813888)), (89/137438953472), by norm_num⟩
  | 11 => ⟨((109559295/274877906944), (-299470387/1099511627776)), (51/274877906944), by norm_num⟩
  | 12 => ⟨((-916060095/8796093022208), (625991777/8796093022208)), (429/8796093022208), by norm_num⟩
  | 13 => ⟨((883784963/35184372088832), (-603936491/35184372088832)), (13/1099511627776), by norm_num⟩
  | 14 => ⟨((-791743611/140737488355328), (541039821/140737488355328)), (187/70368744177664), by norm_num⟩
  | 15 => ⟨((662002003/562949953421312), (-226190297/281474976710656)), (315/562949953421312), by norm_num⟩
  | 16 => ⟨((-1037851725/4503599627370496), (11081537/70368744177664)), (31/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (827851138611/2535301200456458802993406410752)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777790572056675/633825300114114700748351602688), (978700550107/158456325028528675187087900672)), (185171/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472160301418415/9903520314283042199192993792), (4403108186851/39614081257132168796771975168)), (13023/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472086809774703/618970019642690137449562112), (292313149483/154742504910672534362390528)), (27681/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442503302087871/38685626227668133590597632), (1168889308959/38685626227668133590597632)), (27689/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548449241422433/9671406556917033397649408), (34232745185/75557863725914323419136)), (207737/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257822225777889/604462909807314587353088), (958131111289/151115727451828646838272)), (181839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471555248828783/18889465931478580854784), (3112480075735/37778931862957161709568)), (4619/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((648180340243875/2361183241434822606848), (2333095316419/2361183241434822606848)), (221825/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202478314290079/73786976294838206464), (1602975935675/147573952589676412928)), (305193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821446438977539/73786976294838206464), (8008720662077/73786976294838206464)), (381767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910186781080577/4611686018427387904), (2250336966257/2305843009213693952)), (214933/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397905008445345/288230376151711744), (8990777915001/1152921504606846976)), (430341/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596254193240129/72057594037927936), (1963762843125/36028797018963968)), (188541/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488524309353061/36028797018963968), (2939712042723/9007199254740992)), (141673/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485358455121223/9007199254740992), (14657101503419/9007199254740992)), (710239/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110063149817167/2251799813685248), (29190094135303/4503599627370496)), (1426111/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204313610184737/2251799813685248), (43475803907075/2251799813685248)), (1076647/1125899906842624), by norm_num⟩
  | 0 => ⟨((2156928143753859/2251799813685248), (85719863683535/2251799813685248)), (2181677/1125899906842624), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156928143753859/2251799813685248), (85719863683535/2251799813685248)), (8322437290671920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2062790437257231/2251799813685248), (164216717075903/2251799813685248)), (8691241/2251799813685248), by norm_num⟩
  | 2 => ⟨((938835066993147/1125899906842624), (300865708899377/2251799813685248)), (17191099/2251799813685248), by norm_num⟩
  | 3 => ⟨((1525501928011411/2251799813685248), (501755575702289/2251799813685248)), (33263549/2251799813685248), by norm_num⟩
  | 4 => ⟨((460830812314005/1125899906842624), (169959401691137/562949953421312)), (59893229/2251799813685248), by norm_num⟩
  | 5 => ⟨((343974607677739/4503599627370496), (1113030082560285/4503599627370496)), (170386305/4503599627370496), by norm_num⟩
  | 6 => ⟨((-995219403738457/18014398509481984), (680085474126805/18014398509481984)), (27561693/1125899906842624), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-558454055/8388608)), (1/8388608), by norm_num⟩, -11, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1132068457/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-78608382604667/18014398509481984), (1159288316044743/18014398509481984)), (385121689/18014398509481984), by norm_num⟩
  | 1 => ⟨((3722633/268435456), (-878400963/4294967296)), (585/8589934592), by norm_num⟩
  | 2 => ⟨((-94645825/4294967296), (348950693/1073741824)), (467/4294967296), by norm_num⟩
  | 3 => ⟨((12532897/536870912), (-184830681/536870912)), (497/4294967296), by norm_num⟩
  | 4 => ⟨((-79660443/4294967296), (1174803707/4294967296)), (397/4294967296), by norm_num⟩
  | 5 => ⟨((50633035/4294967296), (-186679471/1073741824)), (507/8589934592), by norm_num⟩
  | 6 => ⟨((-107276341/17179869184), (1582073087/17179869184)), (539/17179869184), by norm_num⟩
  | 7 => ⟨((12176071/4294967296), (-1436546695/34359738368)), (491/34359738368), by norm_num⟩
  | 8 => ⟨((-38696209/34359738368), (1141355681/68719476736)), (49/8589934592), by norm_num⟩
  | 9 => ⟨((54657171/137438953472), (-1612128797/274877906944)), (139/68719476736), by norm_num⟩
  | 10 => ⟨((-69481373/549755813888), (1024686419/549755813888)), (355/549755813888), by norm_num⟩
  | 11 => ⟨((80296561/2199023255552), (-1184184945/2199023255552)), (103/549755813888), by norm_num⟩
  | 12 => ⟨((-10632783/1099511627776), (1254467833/8796093022208)), (219/4398046511104), by norm_num⟩
  | 13 => ⟨((83179217/35184372088832), (-1226697323/35184372088832)), (215/17592186044416), by norm_num⟩
  | 14 => ⟨((-9441001/17592186044416), (278465009/35184372088832)), (49/17592186044416), by norm_num⟩
  | 15 => ⟨((128017107/1125899906842624), (-943975241/562949953421312)), (667/1125899906842624), by norm_num⟩
  | 16 => ⟨((-50855657/2251799813685248), (1500002065/4503599627370496)), (133/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (1067164684661/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777738850649283/633825300114114700748351602688), (1261544831395/316912650057057350374175801344)), (184897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944291648305011/19807040628566084398385987584), (2837802132141/39614081257132168796771975168)), (104021/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888286081573467/2475880078570760549798248448), (1507160827135/1237940039285380274899124224)), (221081/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769952467585981/154742504910672534362390528), (753343392207/38685626227668133590597632)), (221123/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774196369703429/4835703278458516698824704), (2824030752337/9671406556917033397649408)), (207347/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314443307141655/151115727451828646838272), (77188136211/18889465931478580854784)), (181473/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886142202846121/75557863725914323419136), (4011896692367/75557863725914323419136)), (294977/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648151154893563/2361183241434822606848), (3007272816875/4722366482869645213696)), (221305/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809873714475603/295147905179352825856), (4132321023519/590295810358705651712)), (304413/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227668667625405/9223372036854775808), (645173193111/9223372036854775808)), (190347/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113766671293381/576460752303423488), (5801041836685/9223372036854775808)), (428525/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591516222750433/1152921504606846976), (90533637575/18014398509481984)), (428831/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596210464646335/72057594037927936), (5062143289361/144115188075855872)), (93893/36028797018963968), by norm_num⟩
  | 4 => ⟨((744199927676073/18014398509481984), (473609902605/2251799813685248)), (35253/2251799813685248), by norm_num⟩
  | 3 => ⟨((371303654066655/2251799813685248), (9445203873157/9007199254740992)), (706269/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219873600561375/4503599627370496), (9404821779601/2251799813685248)), (88511/281474976710656), by norm_num⟩
  | 1 => ⟨((1102010642591057/1125899906842624), (28013317382401/2251799813685248)), (133337/140737488355328), by norm_num⟩
  | 0 => ⟨((1078343035429551/1125899906842624), (27613302163205/1125899906842624)), (4303479/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1078343035429551/1125899906842624), (27613302163205/1125899906842624)), (16416469582564543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((516058843481853/562949953421312), (52893888509871/1125899906842624)), (2113625/562949953421312), by norm_num⟩
  | 2 => ⟨((1887324352448189/2251799813685248), (24244036939491/281474976710656)), (4073733/562949953421312), by norm_num⟩
  | 3 => ⟨((782568614001295/1125899906842624), (162559250745015/1125899906842624)), (7530479/562949953421312), by norm_num⟩
  | 4 => ⟨((1040924014747317/2251799813685248), (451954092101713/2251799813685248)), (25285607/1125899906842624), by norm_num⟩
  | 5 => ⟨((780940026521461/4503599627370496), (835686840673577/4503599627370496)), (134109009/4503599627370496), by norm_num⟩
  | 6 => ⟨((-78608382604667/18014398509481984), (1159288316044743/18014398509481984)), (385121689/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1132068457/16777216)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-573304919/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((803936554176711/18014398509481984), (782311678020511/18014398509481984)), (255929947/18014398509481984), by norm_num⟩
  | 1 => ⟨((-616972909/4294967296), (-300188559/2147483648)), (99/2147483648), by norm_num⟩
  | 2 => ⟨((992979591/4294967296), (3774491/16777216)), (321/4294967296), by norm_num⟩
  | 3 => ⟨((-66589125/268435456), (-259191847/1073741824)), (347/4294967296), by norm_num⟩
  | 4 => ⟨((857368499/4294967296), (417153185/2147483648)), (281/4294967296), by norm_num⟩
  | 5 => ⟨((-551952547/4294967296), (-537105721/4294967296)), (91/2147483648), by norm_num⟩
  | 6 => ⟨((592222237/8589934592), (576292207/8589934592)), (197/8589934592), by norm_num⟩
  | 7 => ⟨((-544654241/17179869184), (-265001865/8589934592)), (183/17179869184), by norm_num⟩
  | 8 => ⟨((876587185/68719476736), (853008097/68719476736)), (37/8589934592), by norm_num⟩
  | 9 => ⟨((-156756961/34359738368), (-610161587/137438953472)), (213/137438953472), by norm_num⟩
  | 10 => ⟨((201832477/137438953472), (785613753/549755813888)), (69/137438953472), by norm_num⟩
  | 11 => ⟨((-236244975/549755813888), (-459780567/1099511627776)), (325/2199023255552), by norm_num⟩
  | 12 => ⟨((1013924319/8796093022208), (986651035/8796093022208)), (351/8796093022208), by norm_num⟩
  | 13 => ⟨((-1004214301/35184372088832), (-977202205/35184372088832)), (175/17592186044416), by norm_num⟩
  | 14 => ⟨((923554611/140737488355328), (449356079/70368744177664)), (81/35184372088832), by norm_num⟩
  | 15 => ⟨((-99093587/70368744177664), (-771424757/562949953421312)), (35/70368744177664), by norm_num⟩
  | 16 => ⟨((637939903/2251799813685248), (620780125/2251799813685248)), (227/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (1005311759599/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777687292129941/633825300114114700748351602688), (148544561157/79228162514264337593543950336)), (92317/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888525452550257/39614081257132168796771975168), (1336581946921/39614081257132168796771975168)), (207729/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236028104394941/309485009821345068724781056), (354929090323/618970019642690137449562112)), (110365/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((55309108137745/4835703278458516698824704), (1419264397607/154742504910672534362390528)), (220749/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774167899580869/4835703278458516698824704), (1330080359793/9671406556917033397649408)), (103487/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628861829803597/302231454903657293676544), (1163340525229/604462909807314587353088)), (181123/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886062128590819/75557863725914323419136), (944764611213/37778931862957161709568)), (73591/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296242669499905/4722366482869645213696), (1416360651257/4722366482869645213696)), (220807/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619666097676819/590295810358705651712), (486554775579/147573952589676412928)), (151833/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910624343248975/36893488147419103232), (607715060399/18446744073709551616)), (189833/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227519361246655/1152921504606846976), (1366044521977/4611686018427387904)), (53405/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795703050077089/576460752303423488), (2728806913279/1152921504606846976)), (427385/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596163255423023/72057594037927936), (2384018841949/144115188075855872)), (374127/144115188075855872), by norm_num⟩
  | 4 => ⟨((744131046036533/18014398509481984), (446083350479/4503599627370496)), (140379/9007199254740992), by norm_num⟩
  | 3 => ⟨((742524572548031/4503599627370496), (4447980047545/9007199254740992)), (702471/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109781369185277/2251799813685248), (8857515842809/4503599627370496)), (351669/1125899906842624), by norm_num⟩
  | 1 => ⟨((275450597349129/281474976710656), (206102630637/35184372088832)), (2114371/2251799813685248), by norm_num⟩
  | 0 => ⟨((1078024869345621/1125899906842624), (26000736970993/2251799813685248)), (4246321/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1078024869345621/1125899906842624), (26000736970993/2251799813685248)), (16198429116255950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258008860797717/281474976710656), (24895144679999/1125899906842624)), (514349/140737488355328), by norm_num⟩
  | 2 => ⟨((472722922039607/562949953421312), (22819676524509/562949953421312)), (15450929/2251799813685248), by norm_num⟩
  | 3 => ⟨((1584128194913469/2251799813685248), (38324487287385/562949953421312)), (27201685/2251799813685248), by norm_num⟩
  | 4 => ⟨((551994422771951/1125899906842624), (53922111991111/562949953421312)), (41976129/2251799813685248), by norm_num⟩
  | 5 => ⟨((260296198928433/1125899906842624), (211490949788937/2251799813685248)), (98401191/4503599627370496), by norm_num⟩
  | 6 => ⟨((803936554176711/18014398509481984), (782311678020511/18014398509481984)), (255929947/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-573304919/8388608)), (1/8388608), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-290145205/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((270606100199629/4503599627370496), (-66076368374457/18014398509481984)), (71720567/9007199254740992), by norm_num⟩
  | 1 => ⟨((-840817259/4294967296), (102655023/8589934592)), (225/8589934592), by norm_num⟩
  | 2 => ⟨((1369731901/4294967296), (-41807497/2147483648)), (185/4294967296), by norm_num⟩
  | 3 => ⟨((-743786461/2147483648), (45404287/2147483648)), (203/4294967296), by norm_num⟩
  | 4 => ⟨((1211664047/4294967296), (-73965775/4294967296)), (167/4294967296), by norm_num⟩
  | 5 => ⟨((-1579087375/8589934592), (48197527/4294967296)), (219/8589934592), by norm_num⟩
  | 6 => ⟨((1714939703/17179869184), (-104688131/17179869184)), (15/1073741824), by norm_num⟩
  | 7 => ⟨((-798205587/17179869184), (48726291/17179869184)), (225/34359738368), by norm_num⟩
  | 8 => ⟨((650157715/34359738368), (-9922185/8589934592)), (185/68719476736), by norm_num⟩
  | 9 => ⟨((-941456267/137438953472), (114941997/274877906944)), (135/137438953472), by norm_num⟩
  | 10 => ⟨((613471081/274877906944), (-74898425/549755813888)), (89/274877906944), by norm_num⟩
  | 11 => ⟨((-1453634913/2199023255552), (22184209/549755813888)), (53/549755813888), by norm_num⟩
  | 12 => ⟨((1578694293/8796093022208), (-96371059/8796093022208)), (29/1099511627776), by norm_num⟩
  | 13 => ⟨((-1582627203/35184372088832), (96611143/35184372088832)), (235/35184372088832), by norm_num⟩
  | 14 => ⟨((1473243489/140737488355328), (-89933837/140737488355328)), (221/140737488355328), by norm_num⟩
  | 15 => ⟨((-639995935/281474976710656), (78136833/562949953421312)), (97/281474976710656), by norm_num⟩
  | 16 => ⟨((521292135/1125899906842624), (-3977771/140737488355328)), (5/70368744177664), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-79419099397/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27775561856773/9903520314283042199192993792), (-46937144695/316912650057057350374175801344)), (92209/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944233878784209/19807040628566084398385987584), (-105583126375/39614081257132168796771975168)), (207473/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472040901778519/618970019642690137449562112), (-56074969083/1237940039285380274899124224)), (110221/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769830314254471/154742504910672534362390528), (-7007113003/9671406556917033397649408)), (220443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548278561588337/9671406556917033397649408), (-52534161633/4835703278458516698824704)), (51667/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257673663602673/604462909807314587353088), (-45948214811/302231454903657293676544)), (45209/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942990523906743/37778931862957161709568), (-74629912599/37778931862957161709568)), (293861/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648091000575217/2361183241434822606848), (-111882019433/4722366482869645213696)), (220399/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202447863691877/73786976294838206464), (-153735720075/590295810358705651712)), (151527/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455286261767633/18446744073709551616), (-96008347029/36893488147419103232)), (378825/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113752423137415/576460752303423488), (-26976084447/1152921504606846976)), (426189/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795645286185453/576460752303423488), (-215546357643/1152921504606846976)), (213101/576460752303423488), by norm_num⟩
  | 5 => ⟨((149028261041331/18014398509481984), (-188308385909/144115188075855872)), (186471/72057594037927936), by norm_num⟩
  | 4 => ⟨((744056391330575/18014398509481984), (-281874299713/36028797018963968)), (559445/36028797018963968), by norm_num⟩
  | 3 => ⟨((371216204118623/2251799813685248), (-175657899977/4503599627370496)), (699363/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109600483865899/2251799813685248), (-174890001919/1125899906842624)), (1398903/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203079207536723/2251799813685248), (-260423659221/562949953421312)), (1049411/1125899906842624), by norm_num⟩
  | 0 => ⟨((269383268594595/281474976710656), (-2053008570025/2251799813685248)), (4199651/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((269383268594595/281474976710656), (-2053008570025/2251799813685248)), (16020397194869231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062486133291011/2251799813685248), (-1964814654251/1125899906842624)), (2011535/562949953421312), by norm_num⟩
  | 2 => ⟨((944540802912109/1125899906842624), (-7198513747539/2251799813685248)), (14767451/2251799813685248), by norm_num⟩
  | 3 => ⟨((1584766759982529/2251799813685248), (-6038982607203/1125899906842624)), (6217965/562949953421312), by norm_num⟩
  | 4 => ⟨((1115258910245577/2251799813685248), (-17000408014681/2251799813685248)), (17637669/1125899906842624), by norm_num⟩
  | 5 => ⟨((1104461786924459/4503599627370496), (-16839735398285/2251799813685248)), (70949169/4503599627370496), by norm_num⟩
  | 6 => ⟨((270606100199629/4503599627370496), (-66076368374457/18014398509481984)), (71720567/9007199254740992), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-290145205/4194304)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-1174024467/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((683058933506701/18014398509481984), (-49816751926419/1125899906842624)), (252684033/18014398509481984), by norm_num⟩
  | 1 => ⟨((-134185005/1073741824), (313163543/2147483648)), (25/536870912), by norm_num⟩
  | 2 => ⟨((884503773/4294967296), (-516067975/2147483648)), (83/1073741824), by norm_num⟩
  | 3 => ⟨((-485863357/2147483648), (566958619/2147483648)), (367/4294967296), by norm_num⟩
  | 4 => ⟨((400331591/2147483648), (-934301559/4294967296)), (19/268435456), by norm_num⟩
  | 5 => ⟨((-263885523/2147483648), (38491319/268435456)), (101/2147483648), by norm_num⟩
  | 6 => ⟨((579815757/8589934592), (-676592577/8589934592)), (223/8589934592), by norm_num⟩
  | 7 => ⟨((-136498439/4294967296), (39820335/1073741824)), (53/4294967296), by norm_num⟩
  | 8 => ⟨((899753175/68719476736), (-1049930625/68719476736)), (351/68719476736), by norm_num⟩
  | 9 => ⟨((-658986597/137438953472), (768977791/137438953472)), (259/137438953472), by norm_num⟩
  | 10 => ⟨((3393613/2147483648), (-1013770141/549755813888)), (343/549755813888), by norm_num⟩
  | 11 => ⟨((-32537585/68719476736), (75936841/137438953472)), (207/1099511627776), by norm_num⟩
  | 12 => ⟨((142984763/1099511627776), (-667401173/4398046511104)), (229/4398046511104), by norm_num⟩
  | 13 => ⟨((-580005481/17592186044416), (338406983/8796093022208)), (117/8796093022208), by norm_num⟩
  | 14 => ⟨((546172413/70368744177664), (-318666917/35184372088832)), (111/35184372088832), by norm_num⟩
  | 15 => ⟨((-960050759/562949953421312), (1120292451/562949953421312)), (393/562949953421312), by norm_num⟩
  | 16 => ⟨((791042671/2251799813685248), (-461537645/1125899906842624)), (163/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-1123206770039/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777584900182843/633825300114114700748351602688), (-663785959003/316912650057057350374175801344)), (92331/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888410279266797/39614081257132168796771975168), (-1493153821267/39614081257132168796771975168)), (103881/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236012810595517/309485009821345068724781056), (-1586016157075/2475880078570760549798248448)), (110383/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442442283470981/38685626227668133590597632), (-1585499185541/154742504910672534362390528)), (55197/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548221143406711/9671406556917033397649408), (-1485856435443/9671406556917033397649408)), (51753/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628811680590059/302231454903657293676544), (-649787795153/302231454903657293676544)), (181159/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29467174862323/1180591620717411303424), (-2110781904499/75557863725914323419136)), (73607/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296120508041931/4722366482869645213696), (-24721673513/73786976294838206464)), (55215/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619498193251459/590295810358705651712), (-2174046903587/590295810358705651712)), (2373/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1821038907317197/73786976294838206464), (-169710618207/4611686018427387904)), (189887/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56872469616343/288230376151711744), (-190736534473/576460752303423488)), (427375/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591170412019655/1152921504606846976), (-3048030734919/1152921504606846976)), (427537/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192120479547301/144115188075855872), (-665702474145/36028797018963968)), (187139/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487953436609005/36028797018963968), (-498224493403/4503599627370496)), (280891/18014398509481984), by norm_num⟩
  | 3 => ⟨((742332005257421/4503599627370496), (-4967545764873/9007199254740992)), (351435/4503599627370496), by norm_num⟩
  | 2 => ⟨((277349315256439/562949953421312), (-9891129316199/4503599627370496)), (1407673/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202457581466289/2251799813685248), (-14727260563907/2251799813685248)), (2116371/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153775822542939/2251799813685248), (-29019609016327/2251799813685248)), (4252345/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153775822542939/2251799813685248), (-29019609016327/2251799813685248)), (16221408852584075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029822484191601/1125899906842624), (-55512689804095/2251799813685248)), (1030509/281474976710656), by norm_num⟩
  | 2 => ⟨((941259456389999/1125899906842624), (-12693893962237/281474976710656)), (15487623/2251799813685248), by norm_num⟩
  | 3 => ⟨((1569218009117897/2251799813685248), (-84897406298747/1125899906842624)), (13646209/1125899906842624), by norm_num⟩
  | 4 => ⟨((1080742109917895/2251799813685248), (-29581346015249/281474976710656)), (42154605/2251799813685248), by norm_num⟩
  | 5 => ⟨((123456791689353/562949953421312), (-227159136349055/2251799813685248)), (98648517/4503599627370496), by norm_num⟩
  | 6 => ⟨((683058933506701/18014398509481984), (-49816751926419/1125899906842624)), (252684033/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-1174024467/16777216)), (1/8388608), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile018Terms3
