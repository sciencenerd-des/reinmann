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
namespace Reinmann.XiBand58.Tile005Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (2697/160)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (2697/160))
  have he : value ((15/16), (2697/160))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-784090717/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((186713381942827/562949953421312), (908070803949463/2251799813685248)), (17281979/1125899906842624), by norm_num⟩
  | 1 => ⟨((-123424391/536870912), (-600268095/2147483648)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((684410149/8589934592), (832148275/8589934592)), (37/8589934592), by norm_num⟩
  | 3 => ⟨((-632529287/34359738368), (-192267077/8589934592)), (9/8589934592), by norm_num⟩
  | 4 => ⟨((109608973/34359738368), (1066155059/274877906944)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((-121560241/274877906944), (-591201899/1099511627776)), (31/1099511627776), by norm_num⟩
  | 6 => ⟨((449382071/8796093022208), (1092773145/17592186044416)), (59/17592186044416), by norm_num⟩
  | 7 => ⟨((-355986189/70368744177664), (-432830071/70368744177664)), (49/140737488355328), by norm_num⟩
  | 8 => ⟨((246750823/562949953421312), (600029887/1125899906842624)), (9/281474976710656), by norm_num⟩
  | 9 => ⟨((-608123155/18014398509481984), (-739393821/18014398509481984)), (23/9007199254740992), by norm_num⟩
  | 10 => ⟨((674430161/288230376151711744), (205003497/72057594037927936)), (53/288230376151711744), by norm_num⟩
  | 11 => ⟨((-679969985/4611686018427387904), (-826749649/4611686018427387904)), (55/4611686018427387904), by norm_num⟩
  | 12 => ⟨((78553213/9223372036854775808), (382039459/36893488147419103232)), (53/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-536112621/1180591620717411303424), (-651838951/1180591620717411303424)), (47/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((849382747/37778931862957161709568), (1032732185/37778931862957161709568)), (77/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-627997073/604462909807314587353088), (-763557763/604462909807314587353088)), (59/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((870588801/19342813113834066795298816), (1058515821/19342813113834066795298816)), (21/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (574782894185/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890483550509281/316912650057057350374175801344), (1363650355829/633825300114114700748351602688)), (5771/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946107332859571/19807040628566084398385987584), (767007998345/19807040628566084398385987584)), (6493/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892143921723395/2475880078570760549798248448), (407445944467/618970019642690137449562112)), (13799/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110863109809361/9671406556917033397649408), (814831017587/77371252455336267181195264)), (1725/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((776004181487147/4835703278458516698824704), (190959851419/1208925819614629174706176)), (12939/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157617039246975/75557863725914323419136), (167073702365/75557863725914323419136)), (22647/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945640559680301/37778931862957161709568), (135732226767/4722366482869645213696)), (18403/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300155537054917/4722366482869645213696), (1628574543473/4722366482869645213696)), (27609/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812522028124621/295147905179352825856), (2238945230841/590295810358705651712)), (37971/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456991946207083/18446744073709551616), (2798164428079/73786976294838206464)), (47475/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228463659010349/1152921504606846976), (1573612009195/4611686018427387904)), (53425/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598954731741289/1152921504606846976), (3146335409993/1152921504606846976)), (26723/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198925099461565/144115188075855872), (2752043930837/144115188075855872)), (11697/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498147060225581/36028797018963968), (4126067119551/36028797018963968)), (17557/9007199254740992), by norm_num⟩
  | 3 => ⟨((748691392139315/4503599627370496), (5154086781425/9007199254740992)), (43933/4503599627370496), by norm_num⟩
  | 2 => ⟨((280520302865925/562949953421312), (5148842588633/2251799813685248)), (87987/2251799813685248), by norm_num⟩
  | 1 => ⟨((560083934425513/562949953421312), (3855079301911/562949953421312)), (132281/1125899906842624), by norm_num⟩
  | 0 => ⟨((278604984885805/281474976710656), (15367927372627/1125899906842624)), (66443/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278604984885805/281474976710656), (15367927372627/1125899906842624)), (253459931493663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1102847261033965/1125899906842624), (15211232001551/562949953421312)), (533381/1125899906842624), by norm_num⟩
  | 2 => ⟨((1079444582478305/1125899906842624), (14899784117495/281474976710656)), (536873/562949953421312), by norm_num⟩
  | 3 => ⟨((257937793251849/281474976710656), (7142504918945/70368744177664)), (2172563/1125899906842624), by norm_num⟩
  | 4 => ⟨((466937842442115/562949953421312), (104723878682941/562949953421312)), (2211409/562949953421312), by norm_num⟩
  | 5 => ⟨((1471277200963769/2251799813685248), (43431517905985/140737488355328)), (17965049/2251799813685248), by norm_num⟩
  | 6 => ⟨((186713381942827/562949953421312), (908070803949463/2251799813685248)), (17281979/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-784090717/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-77672149/4194304)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1520580259359263/4503599627370496), (261329707014797/2251799813685248)), (32787173/2251799813685248), by norm_num⟩
  | 1 => ⟨((-199142475/536870912), (-547599845/4294967296)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((875121481/4294967296), (37599995/536870912)), (41/4294967296), by norm_num⟩
  | 3 => ⟨((-320473071/4294967296), (-220308355/8589934592)), (63/17179869184), by norm_num⟩
  | 4 => ⟨((176037827/8589934592), (121016733/17179869184)), (9/8589934592), by norm_num⟩
  | 5 => ⟨((-4834933/1073741824), (-13295047/8589934592)), (33/137438953472), by norm_num⟩
  | 6 => ⟨((453266501/549755813888), (311596843/1099511627776)), (25/549755813888), by norm_num⟩
  | 7 => ⟨((-1138203767/8796093022208), (-391227567/8796093022208)), (65/8796093022208), by norm_num⟩
  | 8 => ⟨((625222323/35184372088832), (429807413/70368744177664)), (37/35184372088832), by norm_num⟩
  | 9 => ⟨((-610557269/281474976710656), (-419725961/562949953421312)), (75/562949953421312), by norm_num⟩
  | 10 => ⟨((536612575/2251799813685248), (368892879/4503599627370496)), (17/1125899906842624), by norm_num⟩
  | 11 => ⟨((-428748487/18014398509481984), (-18421375/2251799813685248)), (7/4503599627370496), by norm_num⟩
  | 12 => ⟨((628037809/288230376151711744), (431742911/576460752303423488)), (21/144115188075855872), by norm_num⟩
  | 13 => ⟨((-424596957/2305843009213693952), (-145944021/2305843009213693952)), (59/4611686018427387904), by norm_num⟩
  | 14 => ⟨((66638205/4611686018427387904), (183241023/36893488147419103232)), (77/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-624721501/590295810358705651712), (-429463125/1180591620717411303424)), (93/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((343163359/4722366482869645213696), (471813467/18889465931478580854784)), (105/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (215629461647/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780380769956505/633825300114114700748351602688), (511252442687/633825300114114700748351602688)), (23063/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118222196547755/2475880078570760549798248448), (287553020625/19807040628566084398385987584)), (51893/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945721651933293/1237940039285380274899124224), (76373242291/309485009821345068724781056)), (27569/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773109277624411/154742504910672534362390528), (610913690367/154742504910672534362390528)), (55141/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193918976346681/1208925819614629174706176), (572654832945/9671406556917033397649408)), (51697/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260361977940895/604462909807314587353088), (62624530025/75557863725914323419136)), (45237/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890348099138029/75557863725914323419136), (406987516665/37778931862957161709568)), (73513/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324864003296989/1180591620717411303424), (610355428051/4722366482869645213696)), (55139/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406020650735419/147573952589676412928), (839034264627/590295810358705651712)), (37911/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826766556028021/73786976294838206464), (1048486248947/73786976294838206464)), (94785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826358697661765/9223372036854775808), (294781407201/2305843009213693952)), (53323/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798802583427793/576460752303423488), (589299550145/576460752303423488)), (106661/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299436341327649/36028797018963968), (515341087373/72057594037927936)), (46673/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496379727739653/36028797018963968), (1544839952115/36028797018963968)), (140053/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495177585576669/9007199254740992), (1928980870019/9007199254740992)), (175127/9007199254740992), by norm_num⟩
  | 2 => ⟨((279970489085647/562949953421312), (3851761413473/4503599627370496)), (87609/1125899906842624), by norm_num⟩
  | 1 => ⟨((2233767642834165/2251799813685248), (5762165371423/2251799813685248)), (263055/1125899906842624), by norm_num⟩
  | 0 => ⟨((2215822087139765/2251799813685248), (11462567948003/2251799813685248)), (263513/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2215822087139765/2251799813685248), (11462567948003/2251799813685248)), (1005222322704124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1090180419581191/1125899906842624), (11279426830113/1125899906842624)), (2085155/2251799813685248), by norm_num⟩
  | 2 => ⟨((1055481144057607/1125899906842624), (21843167762171/1125899906842624)), (2039893/1125899906842624), by norm_num⟩
  | 3 => ⟨((123630363888879/140737488355328), (81907997538119/2251799813685248)), (3903769/1125899906842624), by norm_num⟩
  | 4 => ⟨((1734663346304559/2251799813685248), (1124246866829/17592186044416)), (14285001/2251799813685248), by norm_num⟩
  | 5 => ⟨((331773350927887/562949953421312), (55427728741677/562949953421312)), (23834563/2251799813685248), by norm_num⟩
  | 6 => ⟨((1520580259359263/4503599627370496), (261329707014797/2251799813685248)), (32787173/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-77672149/4194304)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-784090717/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-59242031955819/1125899906842624), (602358947961603/2251799813685248)), (102651291/4503599627370496), by norm_num⟩
  | 1 => ⟨((313289241/4294967296), (-1592725397/4294967296)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((-108577777/2147483648), (551996559/2147483648)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((200694347/8589934592), (-510153145/4294967296)), (93/8589934592), by norm_num⟩
  | 4 => ⟨((-139110721/17179869184), (1414444857/34359738368)), (131/34359738368), by norm_num⟩
  | 5 => ⟨((308557453/137438953472), (-196083693/17179869184)), (147/137438953472), by norm_num⟩
  | 6 => ⟨((-142583819/274877906944), (45304953/17179869184)), (69/274877906944), by norm_num⟩
  | 7 => ⟨((3529699/34359738368), (-1148452587/2199023255552)), (7/137438953472), by norm_num⟩
  | 8 => ⟨((-313164917/17592186044416), (1592093345/17592186044416)), (79/8796093022208), by norm_num⟩
  | 9 => ⟨((192950559/70368744177664), (-490468895/35184372088832)), (99/70368744177664), by norm_num⟩
  | 10 => ⟨((-106994509/281474976710656), (543947411/281474976710656)), (7/35184372088832), by norm_num⟩
  | 11 => ⟨((215746741/4503599627370496), (-548415439/2251799813685248)), (57/2251799813685248), by norm_num⟩
  | 12 => ⟨((-199392327/36028797018963968), (506843487/18014398509481984)), (107/36028797018963968), by norm_num⟩
  | 13 => ⟨((42525609/72057594037927936), (-1729561275/576460752303423488)), (185/576460752303423488), by norm_num⟩
  | 14 => ⟨((-269499483/4611686018427387904), (1370103453/4611686018427387904)), (37/1152921504606846976), by norm_num⟩
  | 15 => ⟨((199256327/36893488147419103232), (-1012995569/36893488147419103232)), (111/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-276227923/590295810358705651712), (1404310045/590295810358705651712)), (39/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (574782894185/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222495069615899/79228162514264337593543950336), (2724382675939/633825300114114700748351602688)), (23117/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945541114695447/19807040628566084398385987584), (3064570035951/39614081257132168796771975168)), (26011/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945470304233765/1237940039285380274899124224), (3255673068145/2475880078570760549798248448)), (13821/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772606331684451/154742504910672534362390528), (3255186417203/154742504910672534362390528)), (55295/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550880032877843/9671406556917033397649408), (3051220239631/9671406556917033397649408)), (51851/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259948906343489/604462909807314587353088), (2669300728289/604462909807314587353088)), (22691/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889676359450549/75557863725914323419136), (4336644439279/75557863725914323419136)), (73767/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298951772666735/4722366482869645213696), (1625817668383/2361183241434822606848)), (3459/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623388564672007/590295810358705651712), (2234810390003/295147905179352825856)), (38065/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456474486955835/18446744073709551616), (5584959578335/73786976294838206464)), (95211/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825380056988395/9223372036854775808), (6280238743215/9223372036854775808)), (107177/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798312353985279/576460752303423488), (6276688535569/1152921504606846976)), (107259/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196885421516543/144115188075855872), (1372027386415/36028797018963968)), (11743/18014398509481984), by norm_num⟩
  | 4 => ⟨((186885716943643/4503599627370496), (8224181128303/36028797018963968)), (35275/9007199254740992), by norm_num⟩
  | 3 => ⟨((373388244884249/2251799813685248), (10266261814321/9007199254740992)), (88349/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118246712702395/2251799813685248), (10245326922123/2251799813685248)), (5537/70368744177664), by norm_num⟩
  | 1 => ⟨((1114404488117609/1125899906842624), (7657847643245/562949953421312)), (266991/1125899906842624), by norm_num⟩
  | 0 => ⟨((1102847261033965/1125899906842624), (30422464003101/1125899906842624)), (538853/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1102847261033965/1125899906842624), (30422464003101/1125899906842624)), (2055561069968795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1079444582478305/1125899906842624), (29799568234989/562949953421312)), (1084761/1125899906842624), by norm_num⟩
  | 2 => ⟨((257937793251849/281474976710656), (28570019675779/281474976710656)), (1097425/562949953421312), by norm_num⟩
  | 3 => ⟨((933875684884231/1125899906842624), (209447757365875/1125899906842624)), (2234095/562949953421312), by norm_num⟩
  | 4 => ⟨((735638600481889/1125899906842624), (347452143247869/1125899906842624)), (9074673/1125899906842624), by norm_num⟩
  | 5 => ⟨((746853527771333/2251799813685248), (7094303155855/17592186044416)), (17459269/1125899906842624), by norm_num⟩
  | 6 => ⟨((-59242031955819/1125899906842624), (602358947961603/2251799813685248)), (102651291/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-784090717/33554432)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-1820602265/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-205592973526431/2251799813685248), (-907202004996087/4503599627370496)), (21811665/1125899906842624), by norm_num⟩
  | 1 => ⟨((315560461/2147483648), (348111463/1073741824)), (17/536870912), by norm_num⟩
  | 2 => ⟨((-253937485/2147483648), (-1120527573/4294967296)), (111/4294967296), by norm_num⟩
  | 3 => ⟨((544928821/8589934592), (1202279705/8589934592)), (121/8589934592), by norm_num⟩
  | 4 => ⟨((-54814319/2147483648), (-967497269/17179869184)), (99/17179869184), by norm_num⟩
  | 5 => ⟨((141152389/17179869184), (311425357/17179869184)), (129/68719476736), by norm_num⟩
  | 6 => ⟨((-151450671/68719476736), (-1336586071/274877906944)), (141/274877906944), by norm_num⟩
  | 7 => ⟨((278571945/549755813888), (307307471/274877906944)), (33/274877906944), by norm_num⟩
  | 8 => ⟨((-224172125/2199023255552), (-989184589/4398046511104)), (27/1099511627776), by norm_num⟩
  | 9 => ⟨((320703215/17592186044416), (1415138827/35184372088832)), (39/8796093022208), by norm_num⟩
  | 10 => ⟨((-206460765/70368744177664), (-14234863/2199023255552)), (51/70368744177664), by norm_num⟩
  | 11 => ⟨((483324775/1125899906842624), (533181165/562949953421312)), (121/1125899906842624), by norm_num⟩
  | 12 => ⟨((-259293739/4503599627370496), (-572081321/4503599627370496)), (33/2251799813685248), by norm_num⟩
  | 13 => ⟨((513621137/72057594037927936), (1133205375/72057594037927936)), (133/72057594037927936), by norm_num⟩
  | 14 => ⟨((-472366475/576460752303423488), (-130273121/72057594037927936)), (31/144115188075855872), by norm_num⟩
  | 15 => ⟨((405463741/4611686018427387904), (447288533/2305843009213693952)), (109/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-652568717/73786976294838206464), (-719883123/36893488147419103232)), (177/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (-2600464329245/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779636600682147/633825300114114700748351602688), (-3080387903655/633825300114114700748351602688)), (11563/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890717761929625/39614081257132168796771975168), (-1732482238961/19807040628566084398385987584)), (52043/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945276667907827/1237940039285380274899124224), (-3680956890103/2475880078570760549798248448)), (55307/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443054757468255/38685626227668133590597632), (-920079517633/38685626227668133590597632)), (6915/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550516906500819/9671406556917033397649408), (-3449619511455/9671406556917033397649408)), (51875/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629815569947321/302231454903657293676544), (-3017738467169/604462909807314587353088)), (45405/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944579965609511/37778931862957161709568), (-1225638195529/18889465931478580854784)), (4613/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298564401087023/4722366482869645213696), (-1837900773017/2361183241434822606848)), (27689/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622855847078149/590295810358705651712), (-5052418731543/590295810358705651712)), (76181/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825231928739775/73786976294838206464), (-6312811342583/73786976294838206464)), (95279/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912315309160011/4611686018427387904), (-1774546126657/2305843009213693952)), (107263/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595875061316171/1152921504606846976), (-3546762729127/576460752303423488)), (26839/288230376151711744), by norm_num⟩
  | 5 => ⟨((598114624050643/72057594037927936), (-6201595093383/144115188075855872)), (94041/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494101013715291/36028797018963968), (-9291917648459/36028797018963968)), (70635/18014398509481984), by norm_num⟩
  | 3 => ⟨((373080319263779/2251799813685248), (-11596575683543/9007199254740992)), (176953/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117013825513667/2251799813685248), (-11569113378941/2251799813685248)), (177503/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112552249945807/1125899906842624), (-8642541834541/562949953421312)), (133815/562949953421312), by norm_num⟩
  | 0 => ⟨((8586964689561/8796093022208), (-34296239498227/1125899906842624)), (135195/281474976710656), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((8586964689561/8796093022208), (-34296239498227/1125899906842624)), (515727997899913699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1071954772825015/1125899906842624), (-8370210410817/140737488355328)), (1088793/1125899906842624), by norm_num⟩
  | 2 => ⟨((508305916448465/562949953421312), (-63753354591433/562949953421312)), (1101381/562949953421312), by norm_num⟩
  | 3 => ⟨((903492088166235/1125899906842624), (-230259952134747/1125899906842624)), (4476813/1125899906842624), by norm_num⟩
  | 4 => ⟨((338963660616315/562949953421312), (-739099608094591/2251799813685248)), (4508035/562949953421312), by norm_num⟩
  | 5 => ⟨((573795935569619/2251799813685248), (-445026964115105/1125899906842624)), (33552281/2251799813685248), by norm_num⟩
  | 6 => ⟨((-205592973526431/2251799813685248), (-907202004996087/4503599627370496)), (21811665/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-1820602265/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-112727759/67108864), (-2026845101/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((587120553660963/9007199254740992), (393273095373047/2251799813685248)), (58982921/4503599627370496), by norm_num⟩
  | 1 => ⟨((-501622587/4294967296), (-672007363/2147483648)), (103/4294967296), by norm_num⟩
  | 2 => ⟨((224696755/2147483648), (301018889/1073741824)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-536803385/8589934592), (-1438275853/8589934592)), (57/4294967296), by norm_num⟩
  | 4 => ⟨((240455637/8589934592), (644261095/8589934592)), (13/2147483648), by norm_num⟩
  | 5 => ⟨((-86167733/8589934592), (-461744367/17179869184)), (19/8589934592), by norm_num⟩
  | 6 => ⟨((102927901/34359738368), (1103113123/137438953472)), (23/34359738368), by norm_num⟩
  | 7 => ⟨((-210768047/274877906944), (-1129436219/549755813888)), (3/17179869184), by norm_num⟩
  | 8 => ⟨((94411411/549755813888), (252959755/549755813888)), (11/274877906944), by norm_num⟩
  | 9 => ⟨((-75183351/2199023255552), (-402882699/4398046511104)), (71/8796093022208), by norm_num⟩
  | 10 => ⟨((107768385/17592186044416), (577495113/35184372088832)), (13/8796093022208), by norm_num⟩
  | 11 => ⟨((-140432745/140737488355328), (-752532609/281474976710656)), (137/562949953421312), by norm_num⟩
  | 12 => ⟨((335495601/2251799813685248), (112363119/281474976710656)), (83/2251799813685248), by norm_num⟩
  | 13 => ⟨((-184962283/9007199254740992), (-247787917/4503599627370496)), (93/18014398509481984), by norm_num⟩
  | 14 => ⟨((378751911/144115188075855872), (507401539/72057594037927936)), (97/144115188075855872), by norm_num⟩
  | 15 => ⟨((-361937239/1152921504606846976), (-969750947/1152921504606846976)), (47/576460752303423488), by norm_num⟩
  | 16 => ⟨((162126119/4611686018427387904), (868780221/9223372036854775808)), (43/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790893836630535/5070602400912917605986812821504), (98801544479/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779376092418153/633825300114114700748351602688), (936021480117/316912650057057350374175801344)), (46193/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890424918419237/39614081257132168796771975168), (2105734722515/39614081257132168796771975168)), (51973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945121238217957/1237940039285380274899124224), (2236959519991/2475880078570760549798248448)), (13807/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771908493062783/154742504910672534362390528), (1118264019669/77371252455336267181195264)), (13809/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550226120834409/9671406556917033397649408), (2096286686167/9671406556917033397649408)), (51791/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259377044875761/604462909807314587353088), (1833792609333/604462909807314587353088)), (22663/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29511682321247/1180591620717411303424), (372381752641/9444732965739290427392)), (73669/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649127882646889/2361183241434822606848), (1116769575421/2361183241434822606848)), (27633/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811216192100701/295147905179352825856), (1534947900431/295147905179352825856)), (19003/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456175991520011/18446744073709551616), (1917769858779/36893488147419103232)), (95047/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824038536748411/9223372036854775808), (4312467126925/9223372036854775808)), (106973/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797642661329497/576460752303423488), (4309325168177/1152921504606846976)), (53515/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195715858966469/144115188075855872), (470890921931/18014398509481984)), (93715/144115188075855872), by norm_num⟩
  | 4 => ⟨((373334046357055/9007199254740992), (1410908289605/9007199254740992)), (70349/18014398509481984), by norm_num⟩
  | 3 => ⟨((745687209258783/4503599627370496), (7042204479435/9007199254740992)), (176095/9007199254740992), by norm_num⟩
  | 2 => ⟨((558040345969593/1125899906842624), (1755931932901/562949953421312)), (352859/4503599627370496), by norm_num⟩
  | 1 => ⟨((1111186721238117/1125899906842624), (327796877679/35184372088832)), (132741/562949953421312), by norm_num⟩
  | 0 => ⟨((548268133221863/562949953421312), (20795235393867/1125899906842624)), (133581/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((548268133221863/562949953421312), (20795235393867/1125899906842624)), (509571076513194949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2135108697507455/2251799813685248), (81011569998457/2251799813685248)), (265129/281474976710656), by norm_num⟩
  | 2 => ⟨((505387540228149/562949953421312), (76813447914521/1125899906842624)), (2087425/1125899906842624), by norm_num⟩
  | 3 => ⟨((902181402909469/1125899906842624), (137918332747101/1125899906842624)), (8065583/2251799813685248), by norm_num⟩
  | 4 => ⟨((1412043490574813/2251799813685248), (221027382928999/1125899906842624)), (7450939/1125899906842624), by norm_num⟩
  | 5 => ⟨((798674194893737/2251799813685248), (277200731083553/1125899906842624)), (24539967/2251799813685248), by norm_num⟩
  | 6 => ⟨((587120553660963/9007199254740992), (393273095373047/2251799813685248)), (58982921/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-112727759/67108864), (-2026845101/67108864)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-3825815/2097152), (-1100610467/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((268694231296997/9007199254740992), (-1428092267125235/9007199254740992)), (218955885/9007199254740992), by norm_num⟩
  | 1 => ⟨((-62329153/1073741824), (82818843/268435456)), (205/4294967296), by norm_num⟩
  | 2 => ⟨((242573863/4294967296), (-1289264217/4294967296)), (201/4294967296), by norm_num⟩
  | 3 => ⟨((-78671157/2147483648), (1672528217/8589934592)), (263/8589934592), by norm_num⟩
  | 4 => ⟨((153087003/8589934592), (-50852963/536870912)), (129/8589934592), by norm_num⟩
  | 5 => ⟨((-119157421/17179869184), (1266627799/34359738368)), (203/34359738368), by norm_num⟩
  | 6 => ⟨((309159513/137438953472), (-1643162593/137438953472)), (265/137438953472), by norm_num⟩
  | 7 => ⟨((-171884753/274877906944), (913556219/274877906944)), (149/274877906944), by norm_num⟩
  | 8 => ⟨((334472285/2199023255552), (-888849159/1099511627776)), (73/549755813888), by norm_num⟩
  | 9 => ⟨((-144634003/4398046511104), (1537440533/8796093022208)), (127/4398046511104), by norm_num⟩
  | 10 => ⟨((225155819/35184372088832), (-1196688455/35184372088832)), (25/4398046511104), by norm_num⟩
  | 11 => ⟨((-318642177/281474976710656), (1693562335/281474976710656)), (285/281474976710656), by norm_num⟩
  | 12 => ⟨((206683015/1125899906842624), (-137313339/140737488355328)), (93/562949953421312), by norm_num⟩
  | 13 => ⟨((-30937429/1125899906842624), (657721649/4503599627370496)), (225/9007199254740992), by norm_num⟩
  | 14 => ⟨((275206661/72057594037927936), (-5713693/281474976710656)), (63/18014398509481984), by norm_num⟩
  | 15 => ⟨((-35701829/72057594037927936), (1518023093/576460752303423488)), (263/576460752303423488), by norm_num⟩
  | 16 => ⟨((138945103/2305843009213693952), (-92310517/288230376151711744)), (129/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790799712358623/5070602400912917605986812821504), (-901942261029/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889576312716277/316912650057057350374175801344), (-266960688369/79228162514264337593543950336)), (92411/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945086762554803/19807040628566084398385987584), (-2402258361875/39614081257132168796771975168)), (103975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889975377105303/2475880078570760549798248448), (-637981048987/618970019642690137449562112)), (110489/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885820700288763/77371252455336267181195264), (-2551389592825/154742504910672534362390528)), (110507/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549975728922475/9671406556917033397649408), (-2391359855795/9671406556917033397649408)), (103619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629578979634053/302231454903657293676544), (-522968032673/151115727451828646838272)), (90685/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888391668210873/75557863725914323419136), (-3398228000693/75557863725914323419136)), (73699/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297988777122437/4722366482869645213696), (-1273870060957/2361183241434822606848)), (27645/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622065295201239/590295810358705651712), (-3501630564659/590295810358705651712)), (4753/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1824245134587851/73786976294838206464), (-1093692764227/18446744073709551616)), (190195/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911761196244143/4611686018427387904), (-4918501742731/9223372036854775808)), (26759/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594769230236029/1152921504606846976), (-4914609571625/1152921504606846976)), (107101/576460752303423488), by norm_num⟩
  | 5 => ⟨((597632168464915/72057594037927936), (-2147954024435/72057594037927936)), (187571/144115188075855872), by norm_num⟩
  | 4 => ⟨((373164755332255/9007199254740992), (-6435119831571/36028797018963968)), (281647/36028797018963968), by norm_num⟩
  | 3 => ⟨((93158010903651/562949953421312), (-1003577472275/1125899906842624)), (176283/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115234770242805/2251799813685248), (-16011475106273/4503599627370496)), (176665/1125899906842624), by norm_num⟩
  | 1 => ⟨((2219837329388267/2251799813685248), (-1493941611963/140737488355328)), (1063817/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188007154474491/2251799813685248), (-47351127369841/2251799813685248)), (1071495/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2188007154474491/2251799813685248), (-47351127369841/2251799813685248)), (4087429050925826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2125026012386561/2251799813685248), (-46009687374513/1125899906842624)), (4254687/2251799813685248), by norm_num⟩
  | 2 => ⟨((1000814539684553/1125899906842624), (-43419393632777/562949953421312)), (8378041/2251799813685248), by norm_num⟩
  | 3 => ⟨((1765856381777289/2251799813685248), (-308764643733427/2251799813685248)), (16186883/2251799813685248), by norm_num⟩
  | 4 => ⟨((1342443114824009/2251799813685248), (-484265087233971/2251799813685248)), (466039/35184372088832), by norm_num⟩
  | 5 => ⟨((696172382774601/2251799813685248), (-577403309260387/2251799813685248)), (48391785/2251799813685248), by norm_num⟩
  | 6 => ⟨((268694231296997/9007199254740992), (-1428092267125235/9007199254740992)), (218955885/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3825815/2097152), (-1100610467/33554432)), (1/16777216), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-1176136075/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1128830043411563/9007199254740992), (152003732547081/2251799813685248)), (114860759/4503599627370496), by norm_num⟩
  | 1 => ⟨((1119297069/4294967296), (-602880241/4294967296)), (231/4294967296), by norm_num⟩
  | 2 => ⟨((-1163756411/4294967296), (626827109/4294967296)), (243/4294967296), by norm_num⟩
  | 3 => ⟨((806654475/4294967296), (-434483443/4294967296)), (171/4294967296), by norm_num⟩
  | 4 => ⟨((-838695413/8589934592), (112935365/2147483648)), (45/2147483648), by norm_num⟩
  | 5 => ⟨((697607233/17179869184), (-375747983/17179869184)), (151/17179869184), by norm_num⟩
  | 6 => ⟨((-967088973/68719476736), (260448655/34359738368)), (53/17179869184), by norm_num⟩
  | 7 => ⟨((574572853/137438953472), (-77369679/34359738368)), (255/274877906944), by norm_num⟩
  | 8 => ⟨((-1194790659/1099511627776), (321771449/549755813888)), (67/274877906944), by norm_num⟩
  | 9 => ⟨((276055259/1099511627776), (-594759927/4398046511104)), (125/2199023255552), by norm_num⟩
  | 10 => ⟨((-918465237/17592186044416), (61838425/2199023255552)), (105/8796093022208), by norm_num⟩
  | 11 => ⟨((1389014377/140737488355328), (-374078225/70368744177664)), (5/2199023255552), by norm_num⟩
  | 12 => ⟨((-962791399/562949953421312), (259291267/281474976710656)), (7/17592186044416), by norm_num⟩
  | 13 => ⟨((1232042111/4503599627370496), (-5184433/35184372088832)), (289/4503599627370496), by norm_num⟩
  | 14 => ⟨((-365994221/9007199254740992), (394266527/18014398509481984)), (173/18014398509481984), by norm_num⟩
  | 15 => ⟨((101475145/18014398509481984), (-437255571/144115188075855872)), (97/72057594037927936), by norm_num⟩
  | 16 => ⟨((-13188227/18014398509481984), (454623699/1152921504606846976)), (51/288230376151711744), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (3448697384521/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778953105719345/633825300114114700748351602688), (510274622913/79228162514264337593543950336)), (46301/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118121795900297/2475880078570760549798248448), (4591665353615/39614081257132168796771975168)), (104203/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889736105308381/2475880078570760549798248448), (4877671745863/2475880078570760549798248448)), (110745/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221425205439265/19342813113834066795298816), (4876577504015/154742504910672534362390528)), (110779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549750441413951/9671406556917033397649408), (1142657228579/2417851639229258349412352)), (103891/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258960317812195/604462909807314587353088), (3998137957305/604462909807314587353088)), (90941/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944034768115879/37778931862957161709568), (3247397556685/37778931862957161709568)), (147845/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297746334899057/4722366482869645213696), (4869189976843/4722366482869645213696)), (110943/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621730568375327/590295810358705651712), (6692038997377/590295810358705651712)), (152641/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455956168879135/18446744073709551616), (8360403986571/73786976294838206464)), (190945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911523280393701/4611686018427387904), (9399069682547/9223372036854775808)), (107505/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594289885841277/1152921504606846976), (2347772824545/288230376151711744)), (26907/144115188075855872), by norm_num⟩
  | 5 => ⟨((597420483772691/72057594037927936), (8208232810951/144115188075855872)), (188627/144115188075855872), by norm_num⟩
  | 4 => ⟨((746008051502307/18014398509481984), (12294414105899/36028797018963968)), (283495/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489710813172869/9007199254740992), (7668325792225/4503599627370496)), (355341/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114396936832167/2251799813685248), (15289643445297/2251799813685248)), (356803/2251799813685248), by norm_num⟩
  | 1 => ⟨((277152769085859/281474976710656), (22817088719803/1125899906842624)), (538867/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091187094226723/1125899906842624), (45165540100643/1125899906842624)), (1092431/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1091187094226723/1125899906842624), (45165540100643/1125899906842624)), (4167293552878951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1055732700012137/1125899906842624), (5471629201015/70368744177664)), (2205147/1125899906842624), by norm_num⟩
  | 2 => ⟨((245782776351319/281474976710656), (164180217719059/1125899906842624)), (2239185/562949953421312), by norm_num⟩
  | 3 => ⟨((1669050012021107/2251799813685248), (573445926945543/2251799813685248)), (18254145/2251799813685248), by norm_num⟩
  | 4 => ⟨((1091077322489131/2251799813685248), (425042193113751/1125899906842624)), (4544681/281474976710656), by norm_num⟩
  | 5 => ⟨((415495424681345/4503599627370496), (823792408524077/2251799813685248)), (31341901/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1128830043411563/9007199254740992), (152003732547081/2251799813685248)), (114860759/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-1176136075/33554432)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile005Terms0
