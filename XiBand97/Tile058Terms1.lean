/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile058Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨58,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78877/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78877/2560))
  have he : value ((69/80), (78877/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1017427393/536870912), (-72691685203/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((209221489727423/9007199254740992), (1337538806141525/9007199254740992)), (6452657/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3507283015/68719476736), (-22421822647/68719476736)), (435/274877906944), by norm_num⟩
  | 2 => ⟨((963286055/17179869184), (98531559577/274877906944)), (481/274877906944), by norm_num⟩
  | 3 => ⟨((-5644148787/137438953472), (-72165321449/274877906944)), (355/274877906944), by norm_num⟩
  | 4 => ⟨((12401462433/549755813888), (2477553405/17179869184)), (49/68719476736), by norm_num⟩
  | 5 => ⟨((-10899519221/1099511627776), (-8709985973/137438953472)), (173/549755813888), by norm_num⟩
  | 6 => ⟨((7982897171/2199023255552), (102068241323/4398046511104)), (255/2199023255552), by norm_num⟩
  | 7 => ⟨((-2505745409/2199023255552), (-2002382575/274877906944)), (161/4398046511104), by norm_num⟩
  | 8 => ⟨((5505685397/17592186044416), (4399684207/2199023255552)), (89/8796093022208), by norm_num⟩
  | 9 => ⟨((-5376545453/70368744177664), (-68743781491/140737488355328)), (175/70368744177664), by norm_num⟩
  | 10 => ⟨((1181347781/70368744177664), (15104552623/140737488355328)), (155/281474976710656), by norm_num⟩
  | 11 => ⟨((-15102175295/4503599627370496), (-96547183281/4503599627370496)), (249/2251799813685248), by norm_num⟩
  | 12 => ⟨((5530478455/9007199254740992), (70711947993/18014398509481984)), (367/18014398509481984), by norm_num⟩
  | 13 => ⟨((-7477971191/72057594037927936), (-95612326179/144115188075855872)), (499/144115188075855872), by norm_num⟩
  | 14 => ⟨((9389018337/576460752303423488), (60023357993/576460752303423488)), (315/576460752303423488), by norm_num⟩
  | 15 => ⟨((-5501275159/2305843009213693952), (-70338558611/4611686018427387904)), (93/1152921504606846976), by norm_num⟩
  | 16 => ⟨((6043768493/18446744073709551616), (77274804857/36893488147419103232)), (411/36893488147419103232), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790753589846217/5070602400912917605986812821504), (922008692389/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889521654882059/316912650057057350374175801344), (2182945236659/633825300114114700748351602688)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890050559266409/39614081257132168796771975168), (1227701113293/19807040628566084398385987584)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472461185660075/618970019642690137449562112), (2608360199765/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885755392476771/77371252455336267181195264), (1303896295199/77371252455336267181195264)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549853296795363/9671406556917033397649408), (1222101305577/4835703278458516698824704)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259050851179281/604462909807314587353088), (1069037251407/302231454903657293676544)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888217655112813/75557863725914323419136), (3473241191697/75557863725914323419136)), (4607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297858300156165/4722366482869645213696), (325492824189/590295810358705651712)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621885942773673/590295810358705651712), (3578815716783/590295810358705651712)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456005256042227/18446744073709551616), (558889092411/9223372036854775808)), (5945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911635189224169/4611686018427387904), (5026694149891/9223372036854775808)), (6691/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594517353956403/1152921504606846976), (5022562268839/1152921504606846976)), (6695/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597522050105729/72057594037927936), (1097524339719/36028797018963968)), (733/18014398509481984), by norm_num⟩
  | 4 => ⟨((5829410064133/140737488355328), (6575866129655/36028797018963968)), (2201/9007199254740992), by norm_num⟩
  | 3 => ⟨((745058080682659/4503599627370496), (4101806915451/4503599627370496)), (11021/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229647144440841/4503599627370496), (16358655128515/4503599627370496)), (11045/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109303907068865/1125899906842624), (1526052804965/140737488355328)), (4157/281474976710656), by norm_num⟩
  | 0 => ⟨((2185564459595967/2251799813685248), (3021931056095/140737488355328)), (33501/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185564459595967/2251799813685248), (3021931056095/140737488355328)), (127796177390670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2120239183253421/2251799813685248), (93857367965463/2251799813685248)), (132941/2251799813685248), by norm_num⟩
  | 2 => ⟨((996226432166509/1125899906842624), (88373783489985/1125899906842624)), (261431/2251799813685248), by norm_num⟩
  | 3 => ⟨((218637814195261/281474976710656), (312781974625705/2251799813685248)), (503683/2251799813685248), by norm_num⟩
  | 4 => ⟨((41099443838489/70368744177664), (242955761293621/1125899906842624)), (461203/1125899906842624), by norm_num⟩
  | 5 => ⟨((663289076491071/2251799813685248), (283800621517813/1125899906842624)), (1475567/2251799813685248), by norm_num⟩
  | 6 => ⟨((209221489727423/9007199254740992), (1337538806141525/9007199254740992)), (6452657/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/536870912), (-72691685203/1073741824)), (1/536870912), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-76177370515/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-79412144969657/2251799813685248), (-1194695390034021/9007199254740992)), (1655875/2251799813685248), by norm_num⟩
  | 1 => ⟨((22320949855/274877906944), (20987608305/68719476736)), (117/68719476736), by norm_num⟩
  | 2 => ⟨((-25697943199/274877906944), (-96651508041/274877906944)), (541/274877906944), by norm_num⟩
  | 3 => ⟨((9861950155/137438953472), (74182773877/274877906944)), (417/274877906944), by norm_num⟩
  | 4 => ⟨((-22707979415/549755813888), (-85406074643/549755813888)), (483/549755813888), by norm_num⟩
  | 5 => ⟨((20914821957/1099511627776), (78661901729/1099511627776)), (447/1099511627776), by norm_num⟩
  | 6 => ⟨((-16052719087/2199023255552), (-60375240769/2199023255552)), (345/2199023255552), by norm_num⟩
  | 7 => ⟨((660049137/274877906944), (79439502503/8796093022208)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((-3039638607/4398046511104), (-91458107129/35184372088832)), (527/35184372088832), by norm_num⟩
  | 9 => ⟨((12442713857/70368744177664), (23398897123/35184372088832)), (271/70368744177664), by norm_num⟩
  | 10 => ⟨((-22920325955/562949953421312), (-21551180683/140737488355328)), (251/281474976710656), by norm_num⟩
  | 11 => ⟨((4797818261/562949953421312), (36089765365/1125899906842624)), (211/1125899906842624), by norm_num⟩
  | 12 => ⟨((-14729846409/9007199254740992), (-55399837159/9007199254740992)), (163/4503599627370496), by norm_num⟩
  | 13 => ⟨((652244707/2251799813685248), (2453131523/2251799813685248)), (29/4503599627370496), by norm_num⟩
  | 14 => ⟨((-27462380605/576460752303423488), (-201733717/1125899906842624)), (613/576460752303423488), by norm_num⟩
  | 15 => ⟨((16862524853/2305843009213693952), (31710484447/1152921504606846976)), (189/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-9706849589/9223372036854775808), (-73016088779/18446744073709551616)), (437/18446744073709551616), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-298080931819/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889450738395311/316912650057057350374175801344), (-2822519123179/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472472731866845/9903520314283042199192993792), (-3174775192817/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889675041087525/2475880078570760549798248448), (-3372514539491/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885670489570913/77371252455336267181195264), (-3371745084149/154742504910672534362390528)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774846996578971/4835703278458516698824704), (-1580096824427/4835703278458516698824704)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314727837476141/151115727451828646838272), (-1382176138109/302231454903657293676544)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29499855599803/1180591620717411303424), (-4490540688713/75557863725914323419136)), (1153/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81105496659885/295147905179352825856), (-1683282826735/2361183241434822606848)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621651412749407/590295810358705651712), (-4626851296687/590295810358705651712)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823727421572413/73786976294838206464), (-5780300806557/73786976294838206464)), (5953/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822939471531141/9223372036854775808), (-3249176813209/4611686018427387904)), (6701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398546423421139/288230376151711744), (-1623187765983/288230376151711744)), (3353/576460752303423488), by norm_num⟩
  | 5 => ⟨((597376526101267/72057594037927936), (-5674858991033/144115188075855872)), (2937/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491890719486451/36028797018963968), (-4249851918021/18014398509481984)), (8823/36028797018963968), by norm_num⟩
  | 3 => ⟨((186195675528085/1125899906842624), (-1325329129945/1125899906842624)), (11049/9007199254740992), by norm_num⟩
  | 2 => ⟨((557134218159701/1125899906842624), (-10569690651909/2251799813685248)), (22161/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216920688541707/2251799813685248), (-7886182263409/562949953421312)), (33399/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091052194074467/1125899906842624), (-31217149620937/1125899906842624)), (67431/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1091052194074467/1125899906842624), (-31217149620937/1125899906842624)), (257228859908293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112835026516273/2251799813685248), (-121003792183225/2251799813685248)), (33607/562949953421312), by norm_num⟩
  | 2 => ⟨((1975943822585835/2251799813685248), (-113536313890889/1125899906842624)), (266713/2251799813685248), by norm_num⟩
  | 3 => ⟨((855491680102327/1125899906842624), (-398510341298441/2251799813685248)), (521871/2251799813685248), by norm_num⟩
  | 4 => ⟨((1229529174817849/2251799813685248), (-302799813148229/1125899906842624)), (488891/1125899906842624), by norm_num⟩
  | 5 => ⟨((127119546484461/562949953421312), (-661339790744259/2251799813685248)), (1593709/2251799813685248), by norm_num⟩
  | 6 => ⟨((-79412144969657/2251799813685248), (-1194695390034021/9007199254740992)), (1655875/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-76177370515/1073741824)), (1/536870912), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2220696383/1073741824), (-79330556429/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((15623103069315/2251799813685248), (568464717964943/4503599627370496)), (703435/1125899906842624), by norm_num⟩
  | 1 => ⟨((-571633377/34359738368), (-83198172605/274877906944)), (207/137438953472), by norm_num⟩
  | 2 => ⟨((2741433945/137438953472), (99750252397/274877906944)), (249/137438953472), by norm_num⟩
  | 3 => ⟨((-4382447665/274877906944), (-79730219561/274877906944)), (25/17179869184), by norm_num⟩
  | 4 => ⟨((2627162635/274877906944), (23898089573/137438953472)), (241/274877906944), by norm_num⟩
  | 5 => ⟨((-5039728691/1099511627776), (-91688185625/1099511627776)), (465/1099511627776), by norm_num⟩
  | 6 => ⟨((4028247201/2199023255552), (36643111147/1099511627776)), (187/1099511627776), by norm_num⟩
  | 7 => ⟨((-2759804263/4398046511104), (-50209338857/4398046511104)), (515/8796093022208), by norm_num⟩
  | 8 => ⟨((1654430399/8796093022208), (120396736295/35184372088832)), (155/8796093022208), by norm_num⟩
  | 9 => ⟨((-440794537/8796093022208), (-128310562143/140737488355328)), (663/140737488355328), by norm_num⟩
  | 10 => ⟨((3382333237/281474976710656), (123070116165/562949953421312)), (319/281474976710656), by norm_num⟩
  | 11 => ⟨((-5898531549/2251799813685248), (-107312454463/2251799813685248)), (559/2251799813685248), by norm_num⟩
  | 12 => ⟨((4714686973/9007199254740992), (21443668939/2251799813685248)), (449/9007199254740992), by norm_num⟩
  | 13 => ⟨((-6957123449/72057594037927936), (-126571501243/72057594037927936)), (333/36028797018963968), by norm_num⟩
  | 14 => ⟨((2383207633/144115188075855872), (86715772715/288230376151711744)), (459/288230376151711744), by norm_num⟩
  | 15 => ⟨((-3047830569/1152921504606846976), (-6931178049/144115188075855872)), (589/2305843009213693952), by norm_num⟩
  | 16 => ⟨((3654189257/9223372036854775808), (33240478157/4611686018427387904)), (355/9223372036854775808), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790640862827485/5070602400912917605986812821504), (1974610278703/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889388040914841/316912650057057350374175801344), (2336873419411/633825300114114700748351602688)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889749960034451/39614081257132168796771975168), (41070373693/618970019642690137449562112)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236190674136085/309485009821345068724781056), (1396097935335/1237940039285380274899124224)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442797869298555/38685626227668133590597632), (2791532820869/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774776995092257/4835703278458516698824704), (1308178856243/4835703278458516698824704)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629394501159339/302231454903657293676544), (143038056097/37778931862957161709568)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((58993507313473/2361183241434822606848), (3717669707465/75557863725914323419136)), (4609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648769653634537/2361183241434822606848), (2787097936387/4722366482869645213696)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810723723048393/295147905179352825856), (478798084265/73786976294838206464)), (1189/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455868270302207/18446744073709551616), (2392584898079/36893488147419103232)), (5947/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911327093663881/4611686018427387904), (2689726582259/4611686018427387904)), (3347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99618841806029/72057594037927936), (5374628091827/1152921504606846976)), (3349/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194505545340165/144115188075855872), (2348688089985/72057594037927936)), (2933/72057594037927936), by norm_num⟩
  | 4 => ⟨((745760916907683/18014398509481984), (109925460581/562949953421312)), (1101/4503599627370496), by norm_num⟩
  | 3 => ⟨((744554220709199/4503599627370496), (4387551477525/4503599627370496)), (2757/2251799813685248), by norm_num⟩
  | 2 => ⟨((2227635334722705/4503599627370496), (4373378027317/1125899906842624)), (22107/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215599193219967/2251799813685248), (26098910722889/2251799813685248)), (33291/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089791850153149/1125899906842624), (25817325039879/1125899906842624)), (67107/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089791850153149/1125899906842624), (25817325039879/1125899906842624)), (255992897994231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2108499583620487/2251799813685248), (24989353183371/562949953421312)), (33247/562949953421312), by norm_num⟩
  | 2 => ⟨((246235199439637/281474976710656), (187192628623063/2251799813685248)), (130429/1125899906842624), by norm_num⟩
  | 3 => ⟨((426924320356533/562949953421312), (163756703282409/1125899906842624)), (249885/1125899906842624), by norm_num⟩
  | 4 => ⟨((1247431035582785/2251799813685248), (248376321297417/1125899906842624)), (903401/2251799813685248), by norm_num⟩
  | 5 => ⟨((36340958037567/140737488355328), (550372781465355/2251799813685248)), (1399501/2251799813685248), by norm_num⟩
  | 6 => ⟨((15623103069315/2251799813685248), (568464717964943/4503599627370496)), (703435/1125899906842624), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2220696383/1073741824), (-79330556429/1073741824)), (1/536870912), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2301277821/1073741824), (-41104594817/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((52116792805139/1125899906842624), (-485278263623935/4503599627370496)), (4574883/9007199254740992), by norm_num⟩
  | 1 => ⟨((-15808760377/137438953472), (36800268075/137438953472)), (349/274877906944), by norm_num⟩
  | 2 => ⟨((19641646893/137438953472), (-45722615427/137438953472)), (109/68719476736), by norm_num⟩
  | 3 => ⟨((-16269219659/137438953472), (37872143707/137438953472)), (363/274877906944), by norm_num⟩
  | 4 => ⟨((20213746059/274877906944), (-23527185435/137438953472)), (227/274877906944), by norm_num⟩
  | 5 => ⟨((-40183417599/1099511627776), (46770287631/549755813888)), (227/549755813888), by norm_num⟩
  | 6 => ⟨((8321003467/549755813888), (-9684983229/274877906944)), (379/2199023255552), by norm_num⟩
  | 7 => ⟨((-184615329/34359738368), (27504319119/2199023255552)), (271/4398046511104), by norm_num⟩
  | 8 => ⟨((7340029739/4398046511104), (-68345665477/17592186044416)), (169/8796093022208), by norm_num⟩
  | 9 => ⟨((-8106350537/17592186044416), (37740577473/35184372088832)), (375/70368744177664), by norm_num⟩
  | 10 => ⟨((4028704871/35184372088832), (-9378181193/35184372088832)), (375/281474976710656), by norm_num⟩
  | 11 => ⟨((-14561389853/562949953421312), (16948294407/281474976710656)), (341/1125899906842624), by norm_num⟩
  | 12 => ⟨((3015307873/562949953421312), (-14038309825/1125899906842624)), (71/1125899906842624), by norm_num⟩
  | 13 => ⟨((-36887426879/36028797018963968), (85868035535/36028797018963968)), (109/9007199254740992), by norm_num⟩
  | 14 => ⟨((13094544621/72057594037927936), (-30482007501/72057594037927936)), (39/18014398509481984), by norm_num⟩
  | 15 => ⟨((-2169248067/72057594037927936), (40397303007/576460752303423488)), (13/36028797018963968), by norm_num⟩
  | 16 => ⟨((21561515787/4611686018427387904), (-25095881719/2305843009213693952)), (65/1152921504606846976), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984075809/5070602400912917605986812821504), (-379402075949/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778661593320491/633825300114114700748351602688), (-897903576221/316912650057057350374175801344)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472405313064809/9903520314283042199192993792), (-504975995517/9903520314283042199192993792)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944694379364865/1237940039285380274899124224), (-2145678699145/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442763743776699/38685626227668133590597632), (-2145150934409/154742504910672534362390528)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387356539985361/2417851639229258349412352), (-2010518416811/9671406556917033397649408)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258677291235939/604462909807314587353088), (-219830402135/75557863725914323419136)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887610966555797/75557863725914323419136), (-357093109815/9444732965739290427392)), (4605/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648701793319613/2361183241434822606848), (-2141639999477/4722366482869645213696)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810630601804457/295147905179352825856), (-2943262920223/590295810358705651712)), (4751/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823240837582337/73786976294838206464), (-3676841830401/73786976294838206464)), (5941/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822393681589505/9223372036854775808), (-4133373541057/9223372036854775808)), (3343/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593641922164425/1152921504606846976), (-4129534805033/1152921504606846976)), (6689/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298569879720093/36028797018963968), (-3609028720203/144115188075855872)), (5857/144115188075855872), by norm_num⟩
  | 4 => ⟨((745592471557859/18014398509481984), (-1351231365281/9007199254740992)), (8793/36028797018963968), by norm_num⟩
  | 3 => ⟨((744345538917011/4503599627370496), (-1685275093789/2251799813685248)), (11003/9007199254740992), by norm_num⟩
  | 2 => ⟨((139175738327919/281474976710656), (-6718564391917/2251799813685248)), (22047/4503599627370496), by norm_num⟩
  | 1 => ⟨((8649967862413/8796093022208), (-10021676738341/1125899906842624)), (33171/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177279395040009/2251799813685248), (-39639384360633/2251799813685248)), (33373/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177279395040009/2251799813685248), (-39639384360633/2251799813685248)), (127307896140670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052263672479303/1125899906842624), (-9581892479513/281474976710656)), (65713/1125899906842624), by norm_num⟩
  | 2 => ⟨((982138667108329/1125899906842624), (-4477608226325/70368744177664)), (127305/1125899906842624), by norm_num⟩
  | 3 => ⟨((1704350125421501/2251799813685248), (-249976447732713/2251799813685248)), (476603/2251799813685248), by norm_num⟩
  | 4 => ⟨((1262244142809275/2251799813685248), (-378406097608127/2251799813685248)), (206821/562949953421312), by norm_num⟩
  | 5 => ⟨((1287920082892411/4503599627370496), (-212115161128589/1125899906842624)), (2411021/4503599627370496), by norm_num⟩
  | 6 => ⟨((52116792805139/1125899906842624), (-485278263623935/4503599627370496)), (4574883/9007199254740992), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2301277821/1073741824), (-41104594817/536870912)), (1/536870912), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2375405559/1073741824), (-42428637741/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-870001887643923/9007199254740992), (231845539338155/4503599627370496)), (2770205/4503599627370496), by norm_num⟩
  | 1 => ⟨((8512538081/34359738368), (-36295902537/274877906944)), (109/68719476736), by norm_num⟩
  | 2 => ⟨((-87336916325/274877906944), (23274287973/137438953472)), (281/137438953472), by norm_num⟩
  | 3 => ⟨((74671589137/274877906944), (-39798246655/274877906944)), (483/274877906944), by norm_num⟩
  | 4 => ⟨((-47882211145/274877906944), (25520121797/274877906944)), (39/34359738368), by norm_num⟩
  | 5 => ⟨((12281544671/137438953472), (-13091564001/274877906944)), (161/274877906944), by norm_num⟩
  | 6 => ⟨((-84004106967/2199023255552), (44772264897/2199023255552)), (553/2199023255552), by norm_num⟩
  | 7 => ⟨((15390448585/1099511627776), (-32811026309/4398046511104)), (407/4398046511104), by norm_num⟩
  | 8 => ⟨((-78951442419/17592186044416), (42079310425/17592186044416)), (131/4398046511104), by norm_num⟩
  | 9 => ⟨((11250358417/8796093022208), (-11992366693/17592186044416)), (75/8796093022208), by norm_num⟩
  | 10 => ⟨((-46170559349/140737488355328), (24607850595/140737488355328)), (309/140737488355328), by norm_num⟩
  | 11 => ⟨((86127379299/1125899906842624), (-1434497513/35184372088832)), (579/1125899906842624), by norm_num⟩
  | 12 => ⟨((-36818727699/2251799813685248), (39247077059/4503599627370496)), (497/4503599627370496), by norm_num⟩
  | 13 => ⟨((29057899063/9007199254740992), (-30974389257/18014398509481984)), (197/9007199254740992), by norm_num⟩
  | 14 => ⟨((-42589736875/72057594037927936), (22699354235/72057594037927936)), (145/36028797018963968), by norm_num⟩
  | 15 => ⟨((14565402431/144115188075855872), (-31052103499/576460752303423488)), (399/576460752303423488), by norm_num⟩
  | 16 => ⟨((-37359519607/2305843009213693952), (39823536459/4611686018427387904)), (257/2305843009213693952), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039964979/10141204801825835211973625643008), (3454412400943/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444636991664453/158456325028528675187087900672), (510898596417/79228162514264337593543950336)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889493040874887/39614081257132168796771975168), (4597179696825/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472313008075179/618970019642690137449562112), (4883398853207/2475880078570760549798248448)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770917684609283/154742504910672534362390528), (4882156345963/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193662106399975/1208925819614629174706176), (4575701646069/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((157320443457755/75557863725914323419136), (1000604819183/151115727451828646838272)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887425012210855/75557863725914323419136), (3250728759081/37778931862957161709568)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648631570490857/2361183241434822606848), (2436964560411/2361183241434822606848)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621066500384733/590295810358705651712), (3349068534077/295147905179352825856)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911497538095187/36893488147419103232), (1045924996827/9223372036854775808)), (373/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822113929643801/9223372036854775808), (4703039928459/4611686018427387904)), (105/144115188075855872), by norm_num⟩
  | 6 => ⟨((1593358090287673/1152921504606846976), (4698513988175/576460752303423488)), (841/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194026587113065/144115188075855872), (8212222323639/144115188075855872)), (5895/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490796415294527/36028797018963968), (6148997357239/18014398509481984)), (8861/36028797018963968), by norm_num⟩
  | 3 => ⟨((186023687776245/1125899906842624), (1917116943989/1125899906842624)), (5553/4503599627370496), by norm_num⟩
  | 2 => ⟨((556440290433327/1125899906842624), (15283668911195/2251799813685248)), (697/140737488355328), by norm_num⟩
  | 1 => ⟨((1106348953979741/1125899906842624), (22792582658101/1125899906842624)), (8421/562949953421312), by norm_num⟩
  | 0 => ⟨((271678159383351/281474976710656), (45054961563655/1125899906842624)), (34143/1125899906842624), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((271678159383351/281474976710656), (45054961563655/1125899906842624)), (130245213035201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((261771583745697/281474976710656), (2717925668683/35184372088832)), (68643/1125899906842624), by norm_num⟩
  | 2 => ⟨((30220975224777/35184372088832), (20221355805297/140737488355328)), (69141/562949953421312), by norm_num⟩
  | 3 => ⟨((1614809464852095/2251799813685248), (555800482109845/2251799813685248)), (277287/1125899906842624), by norm_num⟩
  | 4 => ⟨((510412919010855/1125899906842624), (398575341211831/1125899906842624)), (534579/1125899906842624), by norm_num⟩
  | 5 => ⟨((361165480708273/4503599627370496), (1445513954604949/4503599627370496)), (3452713/4503599627370496), by norm_num⟩
  | 6 => ⟨((-870001887643923/9007199254740992), (231845539338155/4503599627370496)), (2770205/4503599627370496), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2375405559/1073741824), (-42428637741/536870912)), (1/536870912), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-682101719/8388608)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((431357029593931/4503599627370496), (166587188581461/4503599627370496)), (1238433/4503599627370496), by norm_num⟩
  | 1 => ⟨((-34740476399/137438953472), (-1677067341/17179869184)), (101/137438953472), by norm_num⟩
  | 2 => ⟨((91682108875/274877906944), (8851753717/68719476736)), (269/274877906944), by norm_num⟩
  | 3 => ⟨((-80651447141/274877906944), (-31147047369/274877906944)), (239/274877906944), by norm_num⟩
  | 4 => ⟨((53210948181/274877906944), (10274855457/137438953472)), (5/8589934592), by norm_num⟩
  | 5 => ⟨((-56170697125/549755813888), (-5423186521/137438953472)), (171/549755813888), by norm_num⟩
  | 6 => ⟨((98825126639/2199023255552), (2385350023/137438953472)), (19/137438953472), by norm_num⟩
  | 7 => ⟨((-74515764231/4398046511104), (-14388743913/2199023255552)), (231/4398046511104), by norm_num⟩
  | 8 => ⟨((98325686883/17592186044416), (4746590011/2199023255552)), (307/17592186044416), by norm_num⟩
  | 9 => ⟨((-7207975685/4398046511104), (-22269374505/35184372088832)), (91/17592186044416), by norm_num⟩
  | 10 => ⟨((30435617701/70368744177664), (23508062405/140737488355328)), (97/70368744177664), by norm_num⟩
  | 11 => ⟨((-29207759991/281474976710656), (-11279840799/281474976710656)), (47/140737488355328), by norm_num⟩
  | 12 => ⟨((51387302057/2251799813685248), (19845431025/2251799813685248)), (167/2251799813685248), by norm_num⟩
  | 13 => ⟨((-83454791473/18014398509481984), (-32229680127/18014398509481984)), (137/9007199254740992), by norm_num⟩
  | 14 => ⟨((62926279751/72057594037927936), (12150853367/36028797018963968)), (209/72057594037927936), by norm_num⟩
  | 15 => ⟨((-22142141307/144115188075855872), (-34204585215/576460752303423488)), (37/72057594037927936), by norm_num⟩
  | 16 => ⟨((29217190155/1152921504606846976), (11283482665/1152921504606846976)), (197/2305843009213693952), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (480074488707/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444614558270537/158456325028528675187087900672), (567954198925/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944696301857059/19807040628566084398385987584), (159705534185/9903520314283042199192993792)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472286497245767/618970019642690137449562112), (169647744913/618970019642690137449562112)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885406197861141/77371252455336267181195264), (678413820857/154742504910672534362390528)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549198943917067/9671406556917033397649408), (317912395375/4835703278458516698824704)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258478679238071/604462909807314587353088), (1086247263/1180591620717411303424)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887288600587483/75557863725914323419136), (225851300785/18889465931478580854784)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297162143109589/4722366482869645213696), (338622801363/2361183241434822606848)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620929756046263/590295810358705651712), (930712007473/590295810358705651712)), (1185/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822827333194823/73786976294838206464), (145329934147/9223372036854775808)), (2963/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821929594706505/9223372036854775808), (163367280671/1152921504606846976)), (6667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593179215106253/1152921504606846976), (326412632431/288230376151711744)), (1667/288230376151711744), by norm_num⟩
  | 5 => ⟨((298469049900335/36028797018963968), (1140997232211/144115188075855872)), (1459/36028797018963968), by norm_num⟩
  | 4 => ⟨((745291527868765/18014398509481984), (427151531835/9007199254740992)), (2189/9007199254740992), by norm_num⟩
  | 3 => ⟨((743972056259599/4503599627370496), (1065355088157/4503599627370496)), (10949/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225333999351463/4503599627370496), (530789493199/562949953421312)), (21911/4503599627370496), by norm_num⟩
  | 1 => ⟨((553053779258429/562949953421312), (791480714313/281474976710656)), (16449/1125899906842624), by norm_num⟩
  | 0 => ⟨((543271247328167/562949953421312), (6256986424285/1125899906842624)), (65929/2251799813685248), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((543271247328167/562949953421312), (6256986424285/1125899906842624)), (251499184615325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524263051999661/562949953421312), (24153058712079/2251799813685248)), (127983/2251799813685248), by norm_num⟩
  | 2 => ⟨((1952680058903961/2251799813685248), (22493218444313/1125899906842624)), (120561/1125899906842624), by norm_num⟩
  | 3 => ⟨((423098848505137/562949953421312), (19505312528159/562949953421312)), (106955/562949953421312), by norm_num⟩
  | 4 => ⟨((1269257967276983/2251799813685248), (117277569279351/2251799813685248)), (672725/2251799813685248), by norm_num⟩
  | 5 => ⟨((44332919536539/140737488355328), (16526279144135/281474976710656)), (828455/2251799813685248), by norm_num⟩
  | 6 => ⟨((431357029593931/4503599627370496), (166587188581461/4503599627370496)), (1238433/4503599627370496), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-682101719/8388608)), (1/536870912), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2507931583/1073741824), (-89591539601/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-323005992914191/18014398509481984), (-1712579370359909/18014398509481984)), (9240349/18014398509481984), by norm_num⟩
  | 1 => ⟨((6673556855/137438953472), (35383231417/137438953472)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((-18072326983/274877906944), (-47909783477/137438953472)), (261/137438953472), by norm_num⟩
  | 3 => ⟨((8156794787/137438953472), (10811841565/34359738368)), (237/137438953472), by norm_num⟩
  | 4 => ⟨((-5522252441/137438953472), (-58558019449/274877906944)), (323/274877906944), by norm_num⟩
  | 5 => ⟨((11963629467/549755813888), (31715611269/274877906944)), (11/17179869184), by norm_num⟩
  | 6 => ⟨((-21092519/2147483648), (-28629155825/549755813888)), (319/1099511627776), by norm_num⟩
  | 7 => ⟨((16711563065/4398046511104), (44302394965/2199023255552)), (31/274877906944), by norm_num⟩
  | 8 => ⟨((-5656968965/4398046511104), (-59986554797/8796093022208)), (337/8796093022208), by norm_num⟩
  | 9 => ⟨((13617205283/35184372088832), (4512405605/2199023255552)), (51/4398046511104), by norm_num⟩
  | 10 => ⟨((-7375215101/70368744177664), (-78206853799/140737488355328)), (111/35184372088832), by norm_num⟩
  | 11 => ⟨((14525420173/562949953421312), (9626731189/70368744177664)), (439/562949953421312), by norm_num⟩
  | 12 => ⟨((-13111855673/2251799813685248), (-69519123553/2251799813685248)), (199/1125899906842624), by norm_num⟩
  | 13 => ⟨((10925404121/9007199254740992), (57926546621/9007199254740992)), (333/9007199254740992), by norm_num⟩
  | 14 => ⟨((-16906595901/72057594037927936), (-44819427493/36028797018963968)), (517/72057594037927936), by norm_num⟩
  | 15 => ⟨((12209042781/288230376151711744), (64732405139/288230376151711744)), (375/288230376151711744), by norm_num⟩
  | 16 => ⟨((-16531350379/2305843009213693952), (-87649301377/2305843009213693952)), (255/1152921504606846976), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395233316450533/2535301200456458802993406410752), (-286120982619/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778362779554125/633825300114114700748351602688), (-2707707290165/633825300114114700748351602688)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889285030163889/39614081257132168796771975168), (-1522773529933/19807040628566084398385987584)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889031442259273/2475880078570760549798248448), (-808780582931/618970019642690137449562112)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1770697568231561/154742504910672534362390528), (-3234254755559/154742504910672534362390528)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96818187190921/604462909807314587353088), (-1515596150745/4835703278458516698824704)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258383926147113/604462909807314587353088), (-662843008293/151115727451828646838272)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117945879306839/4722366482869645213696), (-4306752886391/75557863725914323419136)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297045756721589/4722366482869645213696), (-1614277235227/2361183241434822606848)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620768933372129/590295810358705651712), (-4436809530183/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911312559763587/36893488147419103232), (-5542334710351/73786976294838206464)), (93/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1821700477366975/9223372036854775808), (-778759225387/1152921504606846976)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592948068344565/1152921504606846976), (-1555940744697/288230376151711744)), (6705/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596835834481951/72057594037927936), (-5438699948749/144115188075855872)), (367/9007199254740992), by norm_num⟩
  | 4 => ⟨((745135860005027/18014398509481984), (-4071941072155/18014398509481984)), (2205/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487547031195259/9007199254740992), (-5077549245075/4503599627370496)), (11045/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112258116541543/2251799813685248), (-10118045963681/2251799813685248)), (22149/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210929916735859/2251799813685248), (-30169425792305/2251799813685248)), (33375/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170283120902403/2251799813685248), (-29801650080251/1125899906842624)), (2105/70368744177664), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170283120902403/2251799813685248), (-29801650080251/1125899906842624)), (8029938012576081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2090139737502317/2251799813685248), (-57445619944659/1125899906842624)), (66705/1125899906842624), by norm_num⟩
  | 2 => ⟨((483555875927849/562949953421312), (-213286051916461/2251799813685248)), (261279/2251799813685248), by norm_num⟩
  | 3 => ⟨((1641233647816643/2251799813685248), (-183205848105773/1125899906842624)), (498357/2251799813685248), by norm_num⟩
  | 4 => ⟨((284149410179613/562949953421312), (-534121373597393/2251799813685248)), (888645/2251799813685248), by norm_num⟩
  | 5 => ⟨((894012468635795/4503599627370496), (-1078392651777619/4503599627370496)), (2637315/4503599627370496), by norm_num⟩
  | 6 => ⟨((-323005992914191/18014398509481984), (-1712579370359909/18014398509481984)), (9240349/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2507931583/1073741824), (-89591539601/1073741824)), (1/536870912), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile058Terms1
