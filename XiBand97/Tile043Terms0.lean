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
namespace Reinmann.XiBand97.Tile043Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35769/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35769/1280))
  have he : value ((69/80), (35769/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-649938377/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1074710578187583/2251799813685248), (-615505403358601/2251799813685248)), (14472869/562949953421312), by norm_num⟩
  | 1 => ⟨((-710423095/2147483648), (203435819/1073741824)), (5/268435456), by norm_num⟩
  | 2 => ⟨((984855531/8589934592), (-564043857/8589934592)), (29/4294967296), by norm_num⟩
  | 3 => ⟨((-910199779/34359738368), (130321803/8589934592)), (7/4294967296), by norm_num⟩
  | 4 => ⟨((1261804821/274877906944), (-722657523/274877906944)), (5/17179869184), by norm_num⟩
  | 5 => ⟨((-699693163/1099511627776), (100181605/274877906944)), (23/549755813888), by norm_num⟩
  | 6 => ⟨((646653791/8796093022208), (-370349851/8796093022208)), (87/17592186044416), by norm_num⟩
  | 7 => ⟨((-256129287/35184372088832), (293379377/70368744177664)), (71/140737488355328), by norm_num⟩
  | 8 => ⟨((710141173/1125899906842624), (-12709693/35184372088832)), (51/1125899906842624), by norm_num⟩
  | 9 => ⟨((-875079737/18014398509481984), (250586677/9007199254740992)), (65/18014398509481984), by norm_num⟩
  | 10 => ⟨((242623621/72057594037927936), (-138954759/72057594037927936)), (37/144115188075855872), by norm_num⟩
  | 11 => ⟨((-244616551/1152921504606846976), (560384579/4611686018427387904)), (77/4611686018427387904), by norm_num⟩
  | 12 => ⟨((904294787/73786976294838206464), (-517905321/73786976294838206464)), (73/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-771457701/1180591620717411303424), (27614201/73786976294838206464)), (1/18446744073709551616), by norm_num⟩
  | 14 => ⟨((1222248527/37778931862957161709568), (-350001473/18889465931478580854784)), (13/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((-903677995/604462909807314587353088), (517552073/604462909807314587353088)), (79/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1252763709/19342813113834066795298816), (-22421235/604462909807314587353088)), (7/1208925819614629174706176), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-677510622719/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781048079781503/633825300114114700748351602688), (-803752765701/633825300114114700748351602688)), (46141/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236538225109387/4951760157141521099596496896), (-904172935747/39614081257132168796771975168)), (25955/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892240794542609/2475880078570760549798248448), (-120078136811/309485009821345068724781056)), (55157/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886953338344573/77371252455336267181195264), (-960559117697/154742504910672534362390528)), (55161/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388024818767859/2417851639229258349412352), (-112556759663/1208925819614629174706176)), (51717/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630507955944851/302231454903657293676544), (-393913613753/302231454903657293676544)), (45255/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891410559373155/75557863725914323419136), (-1280087837175/75557863725914323419136)), (73547/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300252698764761/4722366482869645213696), (-239987726945/1180591620717411303424)), (27583/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625177786313373/590295810358705651712), (-1319745693305/590295810358705651712)), (37931/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914067573195239/36893488147419103232), (-1649401946959/73786976294838206464)), (94841/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827897827298009/9223372036854775808), (-1855192018229/9223372036854775808)), (26679/2305843009213693952), by norm_num⟩
  | 6 => ⟨((24986619196331/18014398509481984), (-927355322449/576460752303423488)), (26685/288230376151711744), by norm_num⟩
  | 5 => ⟨((599545384099327/72057594037927936), (-811165197747/72057594037927936)), (93425/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498396330629885/36028797018963968), (-2432413071133/36028797018963968)), (140191/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497695713406597/9007199254740992), (-3038622634955/9007199254740992)), (175333/9007199254740992), by norm_num⟩
  | 2 => ⟨((2244792297954347/4503599627370496), (-6071566996451/4503599627370496)), (350949/4503599627370496), by norm_num⟩
  | 1 => ⟨((1120645284548787/1125899906842624), (-9093164743331/2251799813685248)), (16473/70368744177664), by norm_num⟩
  | 0 => ⟨((2230789478992901/2251799813685248), (-18129646057687/2251799813685248)), (528563/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((2230789478992901/2251799813685248), (-18129646057687/2251799813685248)), (2016307835105514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2209829215402355/2251799813685248), (-35920976134343/2251799813685248)), (2111549/2251799813685248), by norm_num⟩
  | 2 => ⟨((542016969609021/562949953421312), (-17625728100921/562949953421312)), (2105877/1125899906842624), by norm_num⟩
  | 3 => ⟨((2085242052296073/2251799813685248), (-135762600911189/2251799813685248)), (4187011/1125899906842624), by norm_num⟩
  | 4 => ⟨((961409381629645/1125899906842624), (-251441431719269/2251799813685248)), (8259501/1125899906842624), by norm_num⟩
  | 5 => ⟨((806912137720095/1125899906842624), (-214706609278621/1125899906842624)), (31900357/2251799813685248), by norm_num⟩
  | 6 => ⟨((1074710578187583/2251799813685248), (-615505403358601/2251799813685248)), (14472869/562949953421312), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-649938377/33554432)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-257531989/8388608)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((164695290734621/562949953421312), (572827156186725/2251799813685248)), (70122077/2251799813685248), by norm_num⟩
  | 1 => ⟨((-86277137/268435456), (-150040377/536870912)), (19/536870912), by norm_num⟩
  | 2 => ⟨((94785123/536870912), (82418101/536870912)), (43/2147483648), by norm_num⟩
  | 3 => ⟨((-555371205/8589934592), (-482909539/8589934592)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((610137631/34359738368), (265265177/17179869184)), (73/34359738368), by norm_num⟩
  | 5 => ⟨((-1072487519/274877906944), (-466277733/137438953472)), (131/274877906944), by norm_num⟩
  | 6 => ⟨((785498645/1099511627776), (683011263/1099511627776)), (49/549755813888), by norm_num⟩
  | 7 => ⟨((-986238245/8796093022208), (-857559505/8796093022208)), (125/8796093022208), by norm_num⟩
  | 8 => ⟨((67718341/4398046511104), (942125411/70368744177664)), (35/17592186044416), by norm_num⟩
  | 9 => ⟨((-66129957/35184372088832), (-920027159/562949953421312)), (139/562949953421312), by norm_num⟩
  | 10 => ⟨((232483787/1125899906842624), (404301257/2251799813685248)), (125/4503599627370496), by norm_num⟩
  | 11 => ⟨((-743009587/36028797018963968), (-323032967/18014398509481984)), (51/18014398509481984), by norm_num⟩
  | 12 => ⟨((1088372617/576460752303423488), (473183983/288230376151711744)), (19/72057594037927936), by norm_num⟩
  | 13 => ⟨((-735815097/4611686018427387904), (-159952535/1152921504606846976)), (105/4611686018427387904), by norm_num⟩
  | 14 => ⟨((923857723/73786976294838206464), (803318037/73786976294838206464)), (67/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-135328193/147573952589676412928), (-941370739/1180591620717411303424)), (5/36893488147419103232), by norm_num⟩
  | 16 => ⟨((594692863/9444732965739290427392), (517100731/9444732965739290427392)), (45/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (116538328899/1267650600228229401496703205376)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((27820429761461/9903520314283042199192993792), (1105388714313/633825300114114700748351602688)), (4327/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1891697678109853/39614081257132168796771975168), (1243456404905/39614081257132168796771975168)), (77891/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945797346178349/1237940039285380274899124224), (1321044613583/2475880078570760549798248448)), (82765/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886630303145825/77371252455336267181195264), (1320900836217/154742504910672534362390528)), (20693/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551493617852783/9671406556917033397649408), (1238191788465/9671406556917033397649408)), (38803/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260485995606665/604462909807314587353088), (1083265089625/604462909807314587353088)), (67913/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945274754382989/37778931862957161709568), (220002431709/9444732965739290427392)), (110371/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162450870781517/590295810358705651712), (1319764105837/4722366482869645213696)), (82791/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624289994220031/590295810358705651712), (907134344415/295147905179352825856)), (1779/9223372036854775808), by norm_num⟩
  | 8 => ⟨((456756385367717/18446744073709551616), (2267225566817/73786976294838206464)), (35587/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913324853853887/4611686018427387904), (2549789836915/9223372036854775808)), (80091/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597895741477809/1152921504606846976), (637185380713/288230376151711744)), (160231/1152921504606846976), by norm_num⟩
  | 5 => ⟨((9359368192675/1125899906842624), (139310621929/9007199254740992)), (140259/144115188075855872), by norm_num⟩
  | 4 => ⟨((187094924363023/4503599627370496), (3341098341919/36028797018963968)), (210499/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495650460569645/9007199254740992), (260765722269/562949953421312)), (263321/9007199254740992), by norm_num⟩
  | 2 => ⟨((560176136241285/1125899906842624), (4166074800465/2251799813685248)), (263615/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117582914542093/1125899906842624), (6233688853455/1125899906842624)), (792319/2251799813685248), by norm_num⟩
  | 0 => ⟨((554641900798215/562949953421312), (12405795488359/1125899906842624)), (795273/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554641900798215/562949953421312), (12405795488359/1125899906842624)), (3033725742820357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((546388111964959/562949953421312), (24445419877059/1125899906842624)), (3169197/2251799813685248), by norm_num⟩
  | 2 => ⟨((1060096274792923/1125899906842624), (47452483943349/1125899906842624)), (6289539/2251799813685248), by norm_num⟩
  | 3 => ⟨((1992277229585395/2251799813685248), (178716424621027/2251799813685248)), (12374051/2251799813685248), by norm_num⟩
  | 4 => ⟨((1748480915206911/2251799813685248), (316238291842363/2251799813685248)), (11930007/1125899906842624), by norm_num⟩
  | 5 => ⟨((1313251220487387/2251799813685248), (245553185759919/1125899906842624)), (43755427/2251799813685248), by norm_num⟩
  | 6 => ⟨((164695290734621/562949953421312), (572827156186725/2251799813685248)), (70122077/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-257531989/8388608)), (3/67108864), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-649938377/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((689364943178003/4503599627370496), (-1175042583982703/4503599627370496)), (175453679/4503599627370496), by norm_num⟩
  | 1 => ⟨((-227847751/1073741824), (776746229/2147483648)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((631728105/4294967296), (-1076798917/4294967296)), (83/2147483648), by norm_num⟩
  | 3 => ⟨((-145960185/2147483648), (995173511/8589934592)), (155/8589934592), by norm_num⟩
  | 4 => ⟨((404687563/17179869184), (-689801713/17179869184)), (109/17179869184), by norm_num⟩
  | 5 => ⟨((-448812869/68719476736), (191253645/17179869184)), (123/68719476736), by norm_num⟩
  | 6 => ⟨((207395583/137438953472), (-707023599/274877906944)), (115/274877906944), by norm_num⟩
  | 7 => ⟨((-164292187/549755813888), (1120163233/2199023255552)), (23/274877906944), by norm_num⟩
  | 8 => ⟨((455514665/8796093022208), (-776437987/8796093022208)), (129/8796093022208), by norm_num⟩
  | 9 => ⟨((-561313255/70368744177664), (478387379/35184372088832)), (161/70368744177664), by norm_num⟩
  | 10 => ⟨((19453635/17592186044416), (-530548581/281474976710656)), (181/562949953421312), by norm_num⟩
  | 11 => ⟨((-627629719/4503599627370496), (267453275/1125899906842624)), (185/4503599627370496), by norm_num⟩
  | 12 => ⟨((580053027/36028797018963968), (-988717245/36028797018963968)), (173/36028797018963968), by norm_num⟩
  | 13 => ⟨((-247422843/144115188075855872), (105434857/36028797018963968)), (75/144115188075855872), by norm_num⟩
  | 14 => ⟨((784002039/4611686018427387904), (-1336354265/4611686018427387904)), (15/288230376151711744), by norm_num⟩
  | 15 => ⟨((-289828695/18446744073709551616), (494021435/18446744073709551616)), (45/9223372036854775808), by norm_num⟩
  | 16 => ⟨((200893943/147573952589676412928), (-342429565/147573952589676412928)), (127/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-677510622719/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890061821316135/316912650057057350374175801344), (-401480833461/158456325028528675187087900672)), (46179/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891265832167871/39614081257132168796771975168), (-1806470119937/39614081257132168796771975168)), (103913/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891135852689919/2475880078570760549798248448), (-1919140160893/2475880078570760549798248448)), (110419/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772801762872459/154742504910672534362390528), (-1918876560997/154742504910672534362390528)), (3451/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1551063448178279/9671406556917033397649408), (-899333369723/4835703278458516698824704)), (12943/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315027398298157/151115727451828646838272), (-1573553403719/604462909807314587353088)), (11327/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944968923740957/37778931862957161709568), (-159781211587/4722366482869645213696)), (36819/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324787053472701/1180591620717411303424), (-958457673559/2361183241434822606848)), (6905/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811829599703109/295147905179352825856), (-1317506293729/295147905179352825856)), (151947/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826237032618443/73786976294838206464), (-3292647013131/73786976294838206464)), (94995/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825762614390801/9223372036854775808), (-925672534319/2305843009213693952)), (26727/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1597008622429823/1152921504606846976), (-3700768680257/1152921504606846976)), (213913/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197222871017093/144115188075855872), (-3236011964591/144115188075855872)), (93641/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495594952650861/36028797018963968), (-1212424801583/9007199254740992)), (281141/36028797018963968), by norm_num⟩
  | 3 => ⟨((373548703190031/2251799813685248), (-1513642970499/2251799813685248)), (175903/4503599627370496), by norm_num⟩
  | 2 => ⟨((559448243718583/1125899906842624), (-12086510058649/4503599627370496)), (704755/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230797824456001/2251799813685248), (-4518315035739/562949953421312)), (1059993/2251799813685248), by norm_num⟩
  | 0 => ⟨((552457303850589/562949953421312), (-35920976134343/2251799813685248)), (2131457/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552457303850589/562949953421312), (-35920976134343/2251799813685248)), (8130863198287200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1084033939218043/1125899906842624), (-17625728100921/562949953421312)), (4251463/2251799813685248), by norm_num⟩
  | 2 => ⟨((2085242052296077/2251799813685248), (-135762600911189/2251799813685248)), (4226487/1125899906842624), by norm_num⟩
  | 3 => ⟨((1922818763259297/2251799813685248), (-251441431719269/2251799813685248)), (8337373/1125899906842624), by norm_num⟩
  | 4 => ⟨((806912137720101/1125899906842624), (-429413218557243/2251799813685248)), (1006285/70368744177664), by norm_num⟩
  | 5 => ⟨((67169411136725/140737488355328), (-615505403358607/2251799813685248)), (7304661/281474976710656), by norm_num⟩
  | 6 => ⟨((689364943178003/4503599627370496), (-1175042583982703/4503599627370496)), (175453679/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-649938377/16777216)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-754555089/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((153525040900487/1125899906842624), (-117650200226933/562949953421312)), (70879723/2251799813685248), by norm_num⟩
  | 1 => ⟨((-471284907/2147483648), (361157785/1073741824)), (55/1073741824), by norm_num⟩
  | 2 => ⟨((758503797/4294967296), (-1162522063/4294967296)), (179/4294967296), by norm_num⟩
  | 3 => ⟨((-813843179/8589934592), (1247338055/8589934592)), (97/4294967296), by norm_num⟩
  | 4 => ⟨((327457517/8589934592), (-501878289/8589934592)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((-210809017/17179869184), (1292387113/68719476736)), (103/34359738368), by norm_num⟩
  | 6 => ⟨((452378699/137438953472), (-693338939/137438953472)), (7/8589934592), by norm_num⟩
  | 7 => ⟨((-832086205/1099511627776), (1275298257/1099511627776)), (13/68719476736), by norm_num⟩
  | 8 => ⟨((334797771/2199023255552), (-513128341/2199023255552)), (85/2199023255552), by norm_num⟩
  | 9 => ⟨((-239482767/8796093022208), (367043647/8796093022208)), (123/17592186044416), by norm_num⟩
  | 10 => ⟨((616692231/140737488355328), (-472587169/70368744177664)), (5/4398046511104), by norm_num⟩
  | 11 => ⟨((-721838441/1125899906842624), (553163423/562949953421312)), (95/562949953421312), by norm_num⟩
  | 12 => ⟨((774502769/9007199254740992), (-1187042913/9007199254740992)), (103/4503599627370496), by norm_num⟩
  | 13 => ⟨((-191771403/18014398509481984), (293918749/18014398509481984)), (103/36028797018963968), by norm_num⟩
  | 14 => ⟨((705472381/576460752303423488), (-540621689/288230376151711744)), (191/576460752303423488), by norm_num⟩
  | 15 => ⟨((-605554131/4611686018427387904), (116012939/576460752303423488)), (83/2305843009213693952), by norm_num⟩
  | 16 => ⟨((60912611/4611686018427387904), (-373431245/18446744073709551616)), (17/4611686018427387904), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-1293090722713/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889913344565941/316912650057057350374175801344), (-766019695501/316912650057057350374175801344)), (92351/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890931805777761/39614081257132168796771975168), (-861665556661/19807040628566084398385987584)), (3247/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1890781005609239/2475880078570760549798248448), (-1830779841579/2475880078570760549798248448)), (55205/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886223489369483/77371252455336267181195264), (-915243997033/77371252455336267181195264)), (55211/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550730904925927/9671406556917033397649408), (-1715772461169/9671406556917033397649408)), (51767/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157477335588745/75557863725914323419136), (-187623866475/75557863725914323419136)), (45303/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472366311636361/18889465931478580854784), (-1219264598977/37778931862957161709568)), (147259/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649396936423653/2361183241434822606848), (-457097149065/1180591620717411303424)), (110467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623172158628553/590295810358705651712), (-2513208573851/590295810358705651712)), (151927/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912814249407351/36893488147419103232), (-3140272527087/73786976294838206464)), (94981/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825078381108549/9223372036854775808), (-3531104777987/9223372036854775808)), (213781/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596324848041959/1152921504606846976), (-3528978553775/1152921504606846976)), (213873/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598312542228955/72057594037927936), (-771366416993/36028797018963968)), (187243/144115188075855872), by norm_num⟩
  | 4 => ⟨((747349652153655/18014398509481984), (-577927619533/4503599627370496)), (17567/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493077056175151/9007199254740992), (-5770923557569/9007199254740992)), (351703/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235562868146369/4503599627370496), (-11516821447643/4503599627370496)), (352249/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113733081318499/1125899906842624), (-17212780759425/2251799813685248)), (1059483/2251799813685248), by norm_num⟩
  | 0 => ⟨((275402472221019/281474976710656), (-8544107895611/562949953421312)), (1064967/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((275402472221019/281474976710656), (-8544107895611/562949953421312)), (4062526707175826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1077584546188123/1125899906842624), (-33439113698455/1125899906842624)), (1058155/562949953421312), by norm_num⟩
  | 2 => ⟨((2060698775811653/2251799813685248), (-64008304718191/1125899906842624)), (522087/140737488355328), by norm_num⟩
  | 3 => ⟨((939268927600003/1125899906842624), (-117152363520883/1125899906842624)), (16238743/2251799813685248), by norm_num⟩
  | 4 => ⟨((771384238330635/1125899906842624), (-195465998675931/1125899906842624)), (30473321/2251799813685248), by norm_num⟩
  | 5 => ⟨((494561446468249/1125899906842624), (-267838001569789/1125899906842624)), (52337047/2251799813685248), by norm_num⟩
  | 6 => ⟨((153525040900487/1125899906842624), (-117650200226933/562949953421312)), (70879723/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-754555089/16777216)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1680066333/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((235495466315111/1125899906842624), (186641847583745/4503599627370496)), (35227247/4503599627370496), by norm_num⟩
  | 1 => ⟨((-804808105/2147483648), (-79731297/1073741824)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((1442022543/4294967296), (285718613/4294967296)), (57/4294967296), by norm_num⟩
  | 3 => ⟨((-1722505031/8589934592), (-341292687/8589934592)), (35/4294967296), by norm_num⟩
  | 4 => ⟨((771578675/8589934592), (152878601/8589934592)), (65/17179869184), by norm_num⟩
  | 5 => ⟨((-552993359/17179869184), (-219137345/34359738368)), (3/2147483648), by norm_num⟩
  | 6 => ⟨((1321108117/137438953472), (130880471/68719476736)), (59/137438953472), by norm_num⟩
  | 7 => ⟨((-1352633131/549755813888), (-268007227/549755813888)), (31/274877906944), by norm_num⟩
  | 8 => ⟨((1211796611/2199023255552), (240102243/2199023255552)), (29/1099511627776), by norm_num⟩
  | 9 => ⟨((-964999135/8796093022208), (-95601215/4398046511104)), (3/549755813888), by norm_num⟩
  | 10 => ⟨((1383237071/70368744177664), (68517753/17592186044416)), (71/70368744177664), by norm_num⟩
  | 11 => ⟨((-901246589/281474976710656), (-89285333/140737488355328)), (3/17592186044416), by norm_num⟩
  | 12 => ⟨((269136185/562949953421312), (53325947/562949953421312)), (59/2251799813685248), by norm_num⟩
  | 13 => ⟨((-593510533/9007199254740992), (-235193281/18014398509481984)), (67/18014398509481984), by norm_num⟩
  | 14 => ⟨((303836605/36028797018963968), (240805593/144115188075855872)), (71/144115188075855872), by norm_num⟩
  | 15 => ⟨((-1161391177/1152921504606846976), (-230115041/1152921504606846976)), (69/1152921504606846976), by norm_num⟩
  | 16 => ⟨((260116705/2305843009213693952), (103077701/4611686018427387904)), (63/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (254796008473/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779585234838065/633825300114114700748351602688), (75450299463/158456325028528675187087900672)), (46115/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890660275538853/39614081257132168796771975168), (339480012869/39614081257132168796771975168)), (51881/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472623159238779/618970019642690137449562112), (180320323925/1237940039285380274899124224)), (13781/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772158758776163/154742504910672534362390528), (360576690565/154742504910672534362390528)), (27563/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387615214159681/2417851639229258349412352), (337972708769/9671406556917033397649408)), (25841/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259582550322903/604462909807314587353088), (295658199515/604462909807314587353088)), (45223/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889081824026665/75557863725914323419136), (30019828823/4722366482869645213696)), (36745/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((2536145634181/9223372036854775808), (360126585141/4722366482869645213696)), (3445/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811388765065003/295147905179352825856), (247496582465/295147905179352825856)), (4737/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1825135843052903/73786976294838206464), (618470246867/73786976294838206464)), (47373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824525008716129/9223372036854775808), (173851579557/2305843009213693952)), (26649/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595772556245127/1152921504606846976), (21716898003/36028797018963968)), (106605/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598071521661735/72057594037927936), (151887445725/36028797018963968)), (93291/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493978667279405/36028797018963968), (227569749465/9007199254740992)), (34989/9007199254740992), by norm_num⟩
  | 3 => ⟨((746090247375327/4503599627370496), (284005291049/2251799813685248)), (174981/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233782416655861/4503599627370496), (2266568969459/4503599627370496)), (350071/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112413523876049/1125899906842624), (3386202867435/2251799813685248)), (525383/2251799813685248), by norm_num⟩
  | 0 => ⟨((2198067102998487/2251799813685248), (6717999804007/2251799813685248)), (1051885/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2198067102998487/2251799813685248), (6717999804007/2251799813685248)), (4012622841841887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((536399131530229/562949953421312), (6557694106463/1125899906842624)), (2059847/2251799813685248), by norm_num⟩
  | 2 => ⟨((1022162896434457/1125899906842624), (12496817531185/1125899906842624)), (1974695/1125899906842624), by norm_num⟩
  | 3 => ⟨((1855690386063583/2251799813685248), (5672699289811/281474976710656)), (7258683/2251799813685248), by norm_num⟩
  | 4 => ⟨((1528345148138897/2251799813685248), (74797224663797/2251799813685248)), (12256223/2251799813685248), by norm_num⟩
  | 5 => ⟨((258709083824893/562949953421312), (50766491192697/1125899906842624)), (4362837/562949953421312), by norm_num⟩
  | 6 => ⟨((235495466315111/1125899906842624), (186641847583745/4503599627370496)), (35227247/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1680066333/33554432)), (1/33554432), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-912303851/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-474943737857287/4503599627370496), (693740204440611/4503599627370496)), (75330295/2251799813685248), by norm_num⟩
  | 1 => ⟨((13771621/67108864), (-643709233/2147483648)), (71/1073741824), by norm_num⟩
  | 2 => ⟨((-428773393/2147483648), (626300165/2147483648)), (279/4294967296), by norm_num⟩
  | 3 => ⟨((556236331/4294967296), (-812482565/4294967296)), (183/4294967296), by norm_num⟩
  | 4 => ⟨((-541192961/8589934592), (790509035/8589934592)), (45/2147483648), by norm_num⟩
  | 5 => ⟨((210622575/8589934592), (-1230607643/34359738368)), (283/34359738368), by norm_num⟩
  | 6 => ⟨((-273235071/34359738368), (798217301/68719476736)), (185/68719476736), by norm_num⟩
  | 7 => ⟨((151911685/68719476736), (-55473541/17179869184)), (13/17179869184), by norm_num⟩
  | 8 => ⟨((-591212979/1099511627776), (215893053/274877906944)), (51/274877906944), by norm_num⟩
  | 9 => ⟨((511309927/4398046511104), (-746859525/4398046511104)), (89/2199023255552), by norm_num⟩
  | 10 => ⟨((-795970541/35184372088832), (145332153/4398046511104)), (279/35184372088832), by norm_num⟩
  | 11 => ⟨((140807923/35184372088832), (-822700543/140737488355328)), (199/140737488355328), by norm_num⟩
  | 12 => ⟨((-730665511/1125899906842624), (533633779/562949953421312)), (65/281474976710656), by norm_num⟩
  | 13 => ⟨((218739913/2251799813685248), (-639017469/4503599627370496)), (157/4503599627370496), by norm_num⟩
  | 14 => ⟨((-486455105/36028797018963968), (88819327/4503599627370496)), (11/2251799813685248), by norm_num⟩
  | 15 => ⟨((504852227/288230376151711744), (-737426901/288230376151711744)), (23/36028797018963968), by norm_num⟩
  | 16 => ⟨((-61399817/288230376151711744), (717483245/2305843009213693952)), (181/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (2828127246995/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889687085447103/316912650057057350374175801344), (3349130441179/633825300114114700748351602688)), (46265/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472605629731979/9903520314283042199192993792), (3767202408317/39614081257132168796771975168)), (104117/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890239623027679/2475880078570760549798248448), (4001965795055/2475880078570760549798248448)), (13831/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771905297910143/154742504910672534362390528), (4001193232911/154742504910672534362390528)), (27669/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550222762462543/9671406556917033397649408), (937574475753/2417851639229258349412352)), (25947/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((39355429487331/18889465931478580854784), (410086252301/75557863725914323419136)), (22711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888741624351685/75557863725914323419136), (5329582792909/75557863725914323419136)), (36919/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298250637911699/4722366482869645213696), (3995841144289/4722366482869645213696)), (55403/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202803046158939/73786976294838206464), (5492094827541/590295810358705651712)), (38109/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228086562714207/9223372036854775808), (1715459789341/18446744073709551616)), (95331/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228002956734117/1152921504606846976), (7715061114899/9223372036854775808)), (1677/72057594037927936), by norm_num⟩
  | 6 => ⟨((1595267961521727/1152921504606846976), (7709428004751/1152921504606846976)), (214857/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195697884828167/144115188075855872), (3369707374317/72057594037927936)), (188227/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493303670176457/36028797018963968), (10096458854057/36028797018963968)), (70699/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491324082389107/9007199254740992), (3149606728905/2251799813685248)), (354291/9007199254740992), by norm_num⟩
  | 2 => ⟨((558007936332725/1125899906842624), (6282617567079/1125899906842624)), (11109/70368744177664), by norm_num⟩
  | 1 => ⟨((1111053476442985/1125899906842624), (4691243050183/281474976710656)), (536229/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096126862405755/1125899906842624), (37199018232023/1125899906842624)), (1084479/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096126862405755/1125899906842624), (37199018232023/1125899906842624)), (4136959080222701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1065912097724161/1125899906842624), (72430671485865/1125899906842624)), (2183265/1125899906842624), by norm_num⟩
  | 2 => ⟨((502230434086405/562949953421312), (137143148363115/1125899906842624)), (1103697/281474976710656), by norm_num⟩
  | 3 => ⟨((879415111885187/1125899906842624), (489403809456117/2251799813685248)), (2238183/281474976710656), by norm_num⟩
  | 4 => ⟨((158427030790719/281474976710656), (764524631779807/2251799813685248)), (17877111/1125899906842624), by norm_num⟩
  | 5 => ⟨((453790795541491/2251799813685248), (53788692335407/140737488355328)), (64526577/2251799813685248), by norm_num⟩
  | 6 => ⟨((-474943737857287/4503599627370496), (693740204440611/4503599627370496)), (75330295/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-912303851/16777216)), (1/16777216), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-487453783/8388608)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((15652090083227/9007199254740992), (-749240022363791/4503599627370496)), (358844231/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3879977/1073741824), (742912687/2147483648)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((16136371/4294967296), (-1544843503/4294967296)), (375/4294967296), by norm_num⟩
  | 3 => ⟨((-699055/268435456), (1070803919/4294967296)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((363411/268435456), (-278334269/2147483648)), (137/4294967296), by norm_num⟩
  | 5 => ⟨((-19345713/34359738368), (1852095493/34359738368)), (459/34359738368), by norm_num⟩
  | 6 => ⟨((6704713/34359738368), (-1283774769/68719476736)), (5/1073741824), by norm_num⟩
  | 7 => ⟨((-15933781/274877906944), (762724167/137438953472)), (383/274877906944), by norm_num⟩
  | 8 => ⟨((16566683/1099511627776), (-793020159/549755813888)), (25/68719476736), by norm_num⟩
  | 9 => ⟨((-7655433/2199023255552), (366453125/1099511627776)), (93/1099511627776), by norm_num⟩
  | 10 => ⟨((3183805/4398046511104), (-609614281/8796093022208)), (311/17592186044416), by norm_num⟩
  | 11 => ⟨((-9629871/70368744177664), (921932553/70368744177664)), (473/140737488355328), by norm_num⟩
  | 12 => ⟨((3337459/140737488355328), (-319517475/140737488355328)), (165/281474976710656), by norm_num⟩
  | 13 => ⟨((-8541601/2251799813685248), (817745121/2251799813685248)), (425/4503599627370496), by norm_num⟩
  | 14 => ⟨((10149577/18014398509481984), (-1943375057/36028797018963968)), (127/9007199254740992), by norm_num⟩
  | 15 => ⟨((-11256241/144115188075855872), (1077635953/144115188075855872)), (71/36028797018963968), by norm_num⟩
  | 16 => ⟨((2925837/288230376151711744), (-280110121/288230376151711744)), (297/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-1016265953489/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779199426545735/633825300114114700748351602688), (-1203255875197/316912650057057350374175801344)), (138655/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890226130020069/39614081257132168796771975168), (-676723678079/9903520314283042199192993792)), (78005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945015605473273/1237940039285380274899124224), (-1437774470109/1237940039285380274899124224)), (165787/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771697168219505/154742504910672534362390528), (-718739132833/38685626227668133590597632)), (165817/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550027940783401/9671406556917033397649408), (-2694642443221/9671406556917033397649408)), (38871/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78700223398777/37778931862957161709568), (-2357182978591/604462909807314587353088)), (136081/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888465661099217/75557863725914323419136), (-1914621488093/37778931862957161709568)), (110595/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298044156657663/4722366482869645213696), (-1435450299051/2361183241434822606848)), (165945/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811070627561623/295147905179352825856), (-1972906248635/295147905179352825856)), (114129/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824339804342567/73786976294838206464), (-4929752899065/73786976294838206464)), (35681/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823628511182335/9223372036854775808), (-2771259333637/4611686018427387904)), (321303/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49839839643419/36028797018963968), (-692275557551/144115188075855872)), (321521/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195356230977229/144115188075855872), (-4841078820033/144115188075855872)), (35197/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492795785552815/36028797018963968), (-7251926561275/36028797018963968)), (211427/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490697250145735/9007199254740992), (-9047966891271/9007199254740992)), (264713/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115401036306369/2251799813685248), (-18045186251973/4503599627370496)), (1061433/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110161073835951/1125899906842624), (-13470588886857/1125899906842624)), (799307/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094460639772561/1125899906842624), (-6672193878181/281474976710656)), (1611583/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094460639772561/1125899906842624), (-6672193878181/281474976710656)), (6147701267722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1063266631427413/1125899906842624), (-103774106898421/2251799813685248)), (3209567/1125899906842624), by norm_num⟩
  | 2 => ⟨((2003452804884199/2251799813685248), (-196002405543667/2251799813685248)), (12715733/2251799813685248), by norm_num⟩
  | 3 => ⟨((1765434997489139/2251799813685248), (-348771295533465/2251799813685248)), (3105037/281474976710656), by norm_num⟩
  | 4 => ⟨((332525042364849/562949953421312), (-546880808420275/2251799813685248)), (5830615/281474976710656), by norm_num⟩
  | 5 => ⟨((326425074121395/1125899906842624), (-646066538893119/2251799813685248)), (19440367/562949953421312), by norm_num⟩
  | 6 => ⟨((15652090083227/9007199254740992), (-749240022363791/4503599627370496)), (358844231/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-487453783/8388608)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile043Terms0
