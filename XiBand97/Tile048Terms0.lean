/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile048Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨48,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (37559/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (37559/1280))
  have he : value ((69/80), (37559/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-320962607/536870912), (-10919415363/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((100647459481961/2251799813685248), (-617195233100091/1125899906842624)), (5930481/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1064506573/34359738368), (26111275371/68719476736)), (1/536870912), by norm_num⟩
  | 2 => ⟨((368929865/34359738368), (-18098956905/137438953472)), (91/137438953472), by norm_num⟩
  | 3 => ⟨((-1363854377/549755813888), (16726987933/549755813888)), (43/274877906944), by norm_num⟩
  | 4 => ⟨((118168977/274877906944), (-11594264525/2199023255552)), (61/2199023255552), by norm_num⟩
  | 5 => ⟨((-2096857427/35184372088832), (6429225413/8796093022208)), (137/35184372088832), by norm_num⟩
  | 6 => ⟨((1937907751/281474976710656), (-23767463831/281474976710656)), (129/281474976710656), by norm_num⟩
  | 7 => ⟨((-1535148907/2251799813685248), (18827829193/2251799813685248)), (13/281474976710656), by norm_num⟩
  | 8 => ⟨((2128168273/36028797018963968), (-26100913443/36028797018963968)), (73/18014398509481984), by norm_num⟩
  | 9 => ⟨((-655615039/144115188075855872), (8040788695/144115188075855872)), (23/72057594037927936), by norm_num⟩
  | 10 => ⟨((1454200691/4611686018427387904), (-17835040043/4611686018427387904)), (13/576460752303423488), by norm_num⟩
  | 11 => ⟨((-1466145613/73786976294838206464), (2247692313/9223372036854775808)), (107/73786976294838206464), by norm_num⟩
  | 12 => ⟨((169375783/147573952589676412928), (-16618470289/1180591620717411303424)), (101/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((-1155961565/18889465931478580854784), (14177287171/18889465931478580854784)), (175/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((1831431999/604462909807314587353088), (-22461592299/604462909807314587353088)), (35/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((-1354082055/9671406556917033397649408), (16607135331/9671406556917033397649408)), (105/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((1877156317/309485009821345068724781056), (-1438898629/19342813113834066795298816)), (37/77371252455336267181195264), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-970081037513/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781045601883609/633825300114114700748351602688), (-2301677023831/633825300114114700748351602688)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892302862711167/39614081257132168796771975168), (-2589242941007/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892237489380051/2475880078570760549798248448), (-1375451114809/1237940039285380274899124224)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773903165275911/154742504910672534362390528), (-2750712760905/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552095764020477/9671406556917033397649408), (-2578591883357/9671406556917033397649408)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1261012620664381/604462909807314587353088), (-564016636509/151115727451828646838272)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((14776600003897/590295810358705651712), (-1832865277979/37778931862957161709568)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1300248020401271/4722366482869645213696), (-1374483743393/2361183241434822606848)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406292692507897/147573952589676412928), (-236205828635/36893488147419103232)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828125501056301/73786976294838206464), (-2361655433055/36893488147419103232)), (2973/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827885773710465/9223372036854775808), (-2656308315261/4611686018427387904)), (6693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199891259064351/144115188075855872), (-1327807785677/288230376151711744)), (3349/576460752303423488), by norm_num⟩
  | 5 => ⟨((599538608721635/72057594037927936), (-2322884033677/72057594037927936)), (5865/144115188075855872), by norm_num⟩
  | 4 => ⟨((749186314361427/18014398509481984), (-6965532466321/36028797018963968)), (8807/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497660184378403/9007199254740992), (-8701453371247/9007199254740992)), (11025/9007199254740992), by norm_num⟩
  | 2 => ⟨((140293972425469/281474976710656), (-8693254366603/2251799813685248)), (11051/2251799813685248), by norm_num⟩
  | 1 => ⟨((560278335278201/562949953421312), (-13019364199175/1125899906842624)), (65/4398046511104), by norm_num⟩
  | 0 => ⟨((1115129523414753/1125899906842624), (-3244567561005/140737488355328)), (33535/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115129523414753/1125899906842624), (-3244567561005/140737488355328)), (127925877097701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1103863766613517/1125899906842624), (-51416479294495/1125899906842624)), (67975/1125899906842624), by norm_num⟩
  | 2 => ⟨((1079910881517723/1125899906842624), (-100820309434417/1125899906842624)), (139499/1125899906842624), by norm_num⟩
  | 3 => ⟨((513386123491137/562949953421312), (-193404313428777/1125899906842624)), (146293/562949953421312), by norm_num⟩
  | 4 => ⟨((903149571769443/1125899906842624), (-352752816246723/1125899906842624)), (158543/281474976710656), by norm_num⟩
  | 5 => ⟨((613948536114369/1125899906842624), (-141481739627777/281474976710656)), (1414795/1125899906842624), by norm_num⟩
  | 6 => ⟨((100647459481961/2251799813685248), (-617195233100091/1125899906842624)), (5930481/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-10919415363/536870912)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-2163357985/67108864)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((148795361823819/562949953421312), (-319328442321943/1125899906842624)), (6223979/2251799813685248), by norm_num⟩
  | 1 => ⟨((-9977320129/34359738368), (5353060163/17179869184)), (53/17179869184), by norm_num⟩
  | 2 => ⟨((5480603251/34359738368), (-5880937677/34359738368)), (119/68719476736), by norm_num⟩
  | 3 => ⟨((-8028077441/137438953472), (17228987735/274877906944)), (177/274877906944), by norm_num⟩
  | 4 => ⟨((8819744531/549755813888), (-9463988823/549755813888)), (99/549755813888), by norm_num⟩
  | 5 => ⟨((-15503167559/4398046511104), (16635607073/4398046511104)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((11354646929/17592186044416), (-6092027453/8796093022208)), (131/17592186044416), by norm_num⟩
  | 7 => ⟨((-7128202657/70368744177664), (15297774223/140737488355328)), (167/140737488355328), by norm_num⟩
  | 8 => ⟨((7831131035/562949953421312), (-8403161375/562949953421312)), (93/562949953421312), by norm_num⟩
  | 9 => ⟨((-7647446035/4503599627370496), (4103029489/2251799813685248)), (185/9007199254740992), by norm_num⟩
  | 10 => ⟨((13442525105/72057594037927936), (-14424443575/72057594037927936)), (165/72057594037927936), by norm_num⟩
  | 11 => ⟨((-1342556661/72057594037927936), (2881249267/144115188075855872)), (67/288230376151711744), by norm_num⟩
  | 12 => ⟨((15732791957/9223372036854775808), (-16882004541/9223372036854775808)), (199/9223372036854775808), by norm_num⟩
  | 13 => ⟨((-5318227255/36893488147419103232), (2853350407/18446744073709551616)), (17/9223372036854775808), by norm_num⟩
  | 14 => ⟨((6677336933/590295810358705651712), (-7165087591/590295810358705651712)), (87/590295810358705651712), by norm_num⟩
  | 15 => ⟨((-15649716075/18889465931478580854784), (4198215081/4722366482869645213696)), (207/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((8596485197/151115727451828646838272), (-9224421357/151115727451828646838272)), (115/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-534474272801/5070602400912917605986812821504)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890253649862591/316912650057057350374175801344), (-633699052949/316912650057057350374175801344)), (5771/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891697435231581/39614081257132168796771975168), (-178212660661/4951760157141521099596496896)), (6493/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945797209576695/1237940039285380274899124224), (-1514661045837/2475880078570760549798248448)), (6899/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773260316055271/154742504910672534362390528), (-1514496171715/154742504910672534362390528)), (1725/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551493327663801/9671406556917033397649408), (-1419665001315/9671406556917033397649408)), (6469/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260485723604845/604462909807314587353088), (-1242031737953/604462909807314587353088)), (2831/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890549032863479/75557863725914323419136), (-504493308919/18889465931478580854784)), (9201/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649803289837865/2361183241434822606848), (-1513192676189/4722366482869645213696)), (3451/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812144707260271/295147905179352825856), (-1040086616557/295147905179352825856)), (2373/147573952589676412928), by norm_num⟩
  | 8 => ⟨((57094523270385/2305843009213693952), (-1299758323041/36893488147419103232)), (11867/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913324356043423/4611686018427387904), (-2923494113959/9223372036854775808)), (6677/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597894621957173/1152921504606846976), (-365286479695/144115188075855872)), (13359/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37437437807269/4503599627370496), (-1277826649155/72057594037927936)), (5847/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496757438505651/36028797018963968), (-3830777081615/36028797018963968)), (1097/2251799813685248), by norm_num⟩
  | 3 => ⟨((373911882269263/2251799813685248), (-4783744155985/9007199254740992)), (21959/9007199254740992), by norm_num⟩
  | 2 => ⟨((70021788346653/140737488355328), (-9553317997557/4503599627370496)), (43973/4503599627370496), by norm_num⟩
  | 1 => ⟨((1117575612940749/1125899906842624), (-14294590654093/2251799813685248)), (66099/2251799813685248), by norm_num⟩
  | 0 => ⟨((2218523956042523/2251799813685248), (-28447872488823/2251799813685248)), (66381/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218523956042523/2251799813685248), (-28447872488823/2251799813685248)), (253223423484420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((546345109385163/562949953421312), (-1751717843415/70368744177664)), (66239/562949953421312), by norm_num⟩
  | 2 => ⟨((1059762388291921/1125899906842624), (-54401566374765/1125899906842624)), (263737/1125899906842624), by norm_num⟩
  | 3 => ⟨((1989762646584425/2251799813685248), (-204823656375703/2251799813685248)), (65247/140737488355328), by norm_num⟩
  | 4 => ⟨((1739587433893927/2251799813685248), (-180988762018871/1125899906842624)), (254357/281474976710656), by norm_num⟩
  | 5 => ⟨((40178092967263/70368744177664), (-69909805962897/281474976710656)), (3798191/2251799813685248), by norm_num⟩
  | 6 => ⟨((148795361823819/562949953421312), (-319328442321943/1125899906842624)), (6223979/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-2163357985/67108864)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-320962607/268435456), (-10919415363/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-336084474016481/1125899906842624), (-110345745369307/2251799813685248)), (14196731/4503599627370496), by norm_num⟩
  | 1 => ⟨((14218506201/34359738368), (4668325335/68719476736)), (303/68719476736), by norm_num⟩
  | 2 => ⟨((-9855517485/34359738368), (-25279973/536870912)), (53/17179869184), by norm_num⟩
  | 3 => ⟨((18216864421/137438953472), (1495273985/68719476736)), (99/68719476736), by norm_num⟩
  | 4 => ⟨((-25253936425/549755813888), (-1036444947/137438953472)), (277/549755813888), by norm_num⟩
  | 5 => ⟨((14003755865/1099511627776), (2298908457/1099511627776)), (309/2199023255552), by norm_num⟩
  | 6 => ⟨((-12942218527/4398046511104), (-1062321277/2199023255552)), (9/274877906944), by norm_num⟩
  | 7 => ⟨((10252414037/17592186044416), (1683074281/17592186044416)), (115/17592186044416), by norm_num⟩
  | 8 => ⟨((-28425727535/281474976710656), (-2333236385/140737488355328)), (321/281474976710656), by norm_num⟩
  | 9 => ⟨((17513967019/1125899906842624), (89848679/35184372088832)), (25/140737488355328), by norm_num⟩
  | 10 => ⟨((-606987843/281474976710656), (-3188651957/9007199254740992)), (7/281474976710656), by norm_num⟩
  | 11 => ⟨((19583158087/72057594037927936), (1607421901/36028797018963968)), (57/18014398509481984), by norm_num⟩
  | 12 => ⟨((-9049340543/288230376151711744), (-742786639/144115188075855872)), (213/576460752303423488), by norm_num⟩
  | 13 => ⟨((3860015313/1152921504606846976), (316837209/576460752303423488)), (23/576460752303423488), by norm_num⟩
  | 14 => ⟨((-3057781407/9223372036854775808), (-4015813817/73786976294838206464)), (147/36893488147419103232), by norm_num⟩
  | 15 => ⟨((18086336521/590295810358705651712), (2969120027/590295810358705651712)), (219/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-25072986333/9444732965739290427392), (-4116074351/9444732965739290427392)), (305/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (-970081037513/2535301200456458802993406410752)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890056865517465/316912650057057350374175801344), (-4598823167137/633825300114114700748351602688)), (5791/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891254096865673/39614081257132168796771975168), (-5173092736671/39614081257132168796771975168)), (3259/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945561326328783/1237940039285380274899124224), (-1373934122003/618970019642690137449562112)), (6927/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886393870207883/77371252455336267181195264), (-2747488685959/77371252455336267181195264)), (6929/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551049428622001/9671406556917033397649408), (-5150734571045/9671406556917033397649408)), (6499/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260096452940473/604462909807314587353088), (-2253042930517/302231454903657293676544)), (5689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889914858204705/75557863725914323419136), (-915109529969/9444732965739290427392)), (9249/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299129540882233/4722366482869645213696), (-85770823253/73786976294838206464)), (6941/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623631200007563/590295810358705651712), (-7545679458923/590295810358705651712)), (4775/295147905179352825856), by norm_num⟩
  | 8 => ⟨((114137409367629/4611686018427387904), (-2357217159993/18446744073709551616)), (11947/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912857267813741/4611686018427387904), (-10603033079563/9223372036854775808)), (6727/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399238641931947/288230376151711744), (-2649368746383/288230376151711744)), (421/36028797018963968), by norm_num⟩
  | 5 => ⟨((1197168858702915/144115188075855872), (-4633266877467/72057594037927936)), (11807/144115188075855872), by norm_num⟩
  | 4 => ⟨((747750263242805/18014398509481984), (-13887276947577/36028797018963968)), (17749/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494053364310037/9007199254740992), (-4334289349267/2251799813685248)), (22255/9007199254740992), by norm_num⟩
  | 2 => ⟨((139840001354121/281474976710656), (-8652102385897/1125899906842624)), (11179/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115046961135025/1125899906842624), (-25873771090993/1125899906842624)), (33793/1125899906842624), by norm_num⟩
  | 0 => ⟨((275965941653379/281474976710656), (-51416479294495/1125899906842624)), (8577/140737488355328), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((275965941653379/281474976710656), (-51416479294495/1125899906842624)), (32718658984136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1079910881517721/1125899906842624), (-100820309434417/1125899906842624)), (70407/562949953421312), by norm_num⟩
  | 2 => ⟨((513386123491135/562949953421312), (-193404313428777/1125899906842624)), (18459/70368744177664), by norm_num⟩
  | 3 => ⟨((903149571769435/1125899906842624), (-176376408123361/562949953421312)), (320075/562949953421312), by norm_num⟩
  | 4 => ⟨((613948536114357/1125899906842624), (-565926958511101/1125899906842624)), (1428131/1125899906842624), by norm_num⟩
  | 5 => ⟨((100647459481949/2251799813685248), (-617195233100071/1125899906842624)), (5986383/2251799813685248), by norm_num⟩
  | 6 => ⟨((-336084474016481/1125899906842624), (-110345745369307/2251799813685248)), (14196731/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-10919415363/268435456)), (1/268435456), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-25354097311/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-559002893422265/2251799813685248), (14275487887345/562949953421312)), (5774897/2251799813685248), by norm_num⟩
  | 1 => ⟨((27456068415/68719476736), (-2804627859/68719476736)), (143/34359738368), by norm_num⟩
  | 2 => ⟨((-5523604679/17179869184), (2256937203/68719476736)), (29/8589934592), by norm_num⟩
  | 3 => ⟨((5926599189/34359738368), (-302700025/17179869184)), (251/137438953472), by norm_num⟩
  | 4 => ⟨((-19076986853/274877906944), (1948707585/274877906944)), (51/68719476736), by norm_num⟩
  | 5 => ⟨((24562580717/1099511627776), (-1254529547/549755813888)), (265/1099511627776), by norm_num⟩
  | 6 => ⟨((-13177316211/2199023255552), (1346058277/2199023255552)), (287/4398046511104), by norm_num⟩
  | 7 => ⟨((24237796907/17592186044416), (-2475882541/17592186044416)), (133/8796093022208), by norm_num⟩
  | 8 => ⟨((-4876153657/17592186044416), (996194807/35184372088832)), (27/8796093022208), by norm_num⟩
  | 9 => ⟨((27903525555/562949953421312), (-1425167725/281474976710656)), (311/562949953421312), by norm_num⟩
  | 10 => ⟨((-17963596767/2251799813685248), (1834975175/2251799813685248)), (101/1125899906842624), by norm_num⟩
  | 11 => ⟨((5256598851/4503599627370496), (-2147838993/18014398509481984)), (119/9007199254740992), by norm_num⟩
  | 12 => ⟨((-11280225975/72057594037927936), (2304542337/144115188075855872)), (257/144115188075855872), by norm_num⟩
  | 13 => ⟨((22344397963/1152921504606846976), (-2282472497/1152921504606846976)), (1/4503599627370496), by norm_num⟩
  | 14 => ⟨((-1284354329/576460752303423488), (2099141583/9223372036854775808)), (237/9223372036854775808), by norm_num⟩
  | 15 => ⟨((17639155627/73786976294838206464), (-1801833625/73786976294838206464)), (205/73786976294838206464), by norm_num⟩
  | 16 => ⟨((-28389125809/1180591620717411303424), (724984837/295147905179352825856)), (83/295147905179352825856), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (3959673799581/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222477023524469/79228162514264337593543950336), (73302767571/9903520314283042199192993792)), (181/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1890919378621323/39614081257132168796771975168), (5277115231455/39614081257132168796771975168)), (3259/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945383513856877/1237940039285380274899124224), (2803068336921/1237940039285380274899124224)), (433/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((886216065196117/77371252455336267181195264), (1401309597273/38685626227668133590597632)), (3465/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550716060142649/9671406556917033397649408), (5253956444753/9671406556917033397649408)), (6499/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259804771511697/604462909807314587353088), (4596257211943/604462909807314587353088)), (2845/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((3690314269571/147573952589676412928), (466695479327/4722366482869645213696)), (4625/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298774103269015/4722366482869645213696), (174961842483/147573952589676412928)), (3471/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811571258341323/295147905179352825856), (1923943627019/147573952589676412928)), (597/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1825587761322945/73786976294838206464), (2403974344957/18446744073709551616)), (5975/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825027489517635/9223372036854775808), (10812629534007/9223372036854775808)), (13457/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596267636625279/1152921504606846976), (10806058549527/1152921504606846976)), (13475/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299141981266239/36028797018963968), (36905882209/562949953421312)), (11811/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494599392408563/36028797018963968), (14157060467575/36028797018963968)), (17755/36028797018963968), by norm_num⟩
  | 3 => ⟨((746463711183979/4503599627370496), (8835205862081/4503599627370496)), (22263/9007199254740992), by norm_num⟩
  | 2 => ⟨((558797400650483/1125899906842624), (17631507536257/2251799813685248)), (22369/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113361043887139/1125899906842624), (26349885160477/1125899906842624)), (16907/562949953421312), by norm_num⟩
  | 0 => ⟨((68781244666301/70368744177664), (26154790709849/562949953421312)), (68681/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((68781244666301/70368744177664), (26154790709849/562949953421312)), (261997227195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536621311768641/562949953421312), (6391186456547/70368744177664)), (70323/562949953421312), by norm_num⟩
  | 2 => ⟨((1013760479394203/1125899906842624), (194952853011627/1125899906842624)), (146843/562949953421312), by norm_num⟩
  | 3 => ⟨((219758365878995/281474976710656), (21941948006125/70368744177664)), (39411/70368744177664), by norm_num⟩
  | 4 => ⟨((1153652933025749/2251799813685248), (1096379182406031/2251799813685248)), (2755751/2251799813685248), by norm_num⟩
  | 5 => ⟨((28614394912551/1125899906842624), (1123404533390629/2251799813685248)), (688397/281474976710656), by norm_num⟩
  | 6 => ⟨((-559002893422265/2251799813685248), (14275487887345/562949953421312)), (5774897/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-25354097311/536870912)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-7056569811/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-10109253283205/70368744177664), (-709623910100573/4503599627370496)), (2704381/1125899906842624), by norm_num⟩
  | 1 => ⟨((8844409325/34359738368), (4850293581/17179869184)), (149/34359738368), by norm_num⟩
  | 2 => ⟨((-7923527079/34359738368), (-17381118905/68719476736)), (269/68719476736), by norm_num⟩
  | 3 => ⟨((2366175779/17179869184), (81101001/536870912)), (81/34359738368), by norm_num⟩
  | 4 => ⟨((-2119808929/34359738368), (-9300063137/137438953472)), (147/137438953472), by norm_num⟩
  | 5 => ⟨((12154200709/549755813888), (1666347619/68719476736)), (53/137438953472), by norm_num⟩
  | 6 => ⟨((-7259134737/1099511627776), (-7961851001/1099511627776)), (255/2199023255552), by norm_num⟩
  | 7 => ⟨((14864712461/8796093022208), (16303682199/8796093022208)), (263/8796093022208), by norm_num⟩
  | 8 => ⟨((-13316994655/35184372088832), (-7303069241/17592186044416)), (237/35184372088832), by norm_num⟩
  | 9 => ⟨((10604822789/140737488355328), (11631416415/140737488355328)), (95/70368744177664), by norm_num⟩
  | 10 => ⟨((-7600516661/562949953421312), (-8336280201/562949953421312)), (137/562949953421312), by norm_num⟩
  | 11 => ⟨((2476054127/1125899906842624), (10862988355/4503599627370496)), (45/1125899906842624), by norm_num⟩
  | 12 => ⟨((-11830649143/36028797018963968), (-6487954083/18014398509481984)), (217/36028797018963968), by norm_num⟩
  | 13 => ⟨((13044724695/288230376151711744), (14307511587/288230376151711744)), (241/288230376151711744), by norm_num⟩
  | 14 => ⟨((-13356005141/2305843009213693952), (-14648925353/2305843009213693952)), (249/2305843009213693952), by norm_num⟩
  | 15 => ⟨((3190766491/4611686018427387904), (1749823381/2305843009213693952)), (15/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-11434172149/147573952589676412928), (-6270525225/73786976294838206464)), (217/147573952589676412928), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-1504555311527/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889789247601677/316912650057057350374175801344), (-1782118165721/316912650057057350374175801344)), (5785/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945326151368223/19807040628566084398385987584), (-2004601730669/19807040628566084398385987584)), (3255/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890483669401965/2475880078570760549798248448), (-1064776322579/618970019642690137449562112)), (3459/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772149233008413/154742504910672534362390528), (-4258347722459/154742504910672534362390528)), (865/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550451333410211/9671406556917033397649408), (-3991396123987/9671406556917033397649408)), (3245/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629786812496787/302231454903657293676544), (-872916699711/151115727451828646838272)), (355/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944533105046971/37778931862957161709568), (-5672449649581/75557863725914323419136)), (4617/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298493883435559/4722366482869645213696), (-265813566919/295147905179352825856)), (6929/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622758517076423/590295810358705651712), (-2922876713309/295147905179352825856)), (2383/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912554857235535/36893488147419103232), (-114124603271/1152921504606846976)), (5961/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824492369530715/9223372036854775808), (-2053137115985/2305843009213693952)), (13423/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797867933383989/576460752303423488), (-4103510358043/576460752303423488)), (13437/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299026597708479/36028797018963968), (-224216429493/4503599627370496)), (2943/36028797018963968), by norm_num⟩
  | 4 => ⟨((373478652147125/9007199254740992), (-5374978598611/18014398509481984)), (2211/4503599627370496), by norm_num⟩
  | 3 => ⟨((746042286452611/4503599627370496), (-3353924770477/2251799813685248)), (22163/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116771596538595/2251799813685248), (-418221662077/70368744177664)), (11121/1125899906842624), by norm_num⟩
  | 1 => ⟨((556087585291349/562949953421312), (-19993178742967/1125899906842624)), (33563/1125899906842624), by norm_num⟩
  | 0 => ⟨((274580708543279/281474976710656), (-19830419406277/562949953421312)), (16981/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274580708543279/281474976710656), (-19830419406277/562949953421312)), (64777375341319949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1070024127907799/1125899906842624), (-38689411576953/562949953421312)), (137307/1125899906842624), by norm_num⟩
  | 2 => ⟨((1011603380647019/1125899906842624), (-36769346573613/281474976710656)), (279859/1125899906842624), by norm_num⟩
  | 3 => ⟨((444848443493693/562949953421312), (-132146721291977/562949953421312)), (576015/1125899906842624), by norm_num⟩
  | 4 => ⟨((312991614797/549755813888), (-104423604482539/281474976710656)), (1180773/1125899906842624), by norm_num⟩
  | 5 => ⟨((419968283481349/2251799813685248), (-951221229913445/2251799813685248)), (2220599/1125899906842624), by norm_num⟩
  | 6 => ⟨((-10109253283205/70368744177664), (-709623910100573/4503599627370496)), (2704381/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-7056569811/134217728)), (1/268435456), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-15327337233/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((716703493109933/4503599627370496), (-439526017946067/4503599627370496)), (2551675/2251799813685248), by norm_num⟩
  | 1 => ⟨((-21280526751/68719476736), (6525254357/34359738368)), (77/34359738368), by norm_num⟩
  | 2 => ⟨((20704996491/68719476736), (-12697558679/68719476736)), (19/8589934592), by norm_num⟩
  | 3 => ⟨((-1678752617/8589934592), (8236102767/68719476736)), (25/17179869184), by norm_num⟩
  | 4 => ⟨((13066807021/137438953472), (-4006678991/68719476736)), (99/137438953472), by norm_num⟩
  | 5 => ⟨((-20341465919/549755813888), (3118654925/137438953472)), (39/137438953472), by norm_num⟩
  | 6 => ⟨((3298555415/274877906944), (-1011437045/137438953472)), (103/1099511627776), by norm_num⟩
  | 7 => ⟨((-7335648525/2199023255552), (2249332127/1099511627776)), (29/1099511627776), by norm_num⟩
  | 8 => ⟨((14274512915/17592186044416), (-8753996429/17592186044416)), (57/8796093022208), by norm_num⟩
  | 9 => ⟨((-3086324395/17592186044416), (7570884665/70368744177664)), (25/17592186044416), by norm_num⟩
  | 10 => ⟨((19218271883/562949953421312), (-5892904523/281474976710656)), (79/281474976710656), by norm_num⟩
  | 11 => ⟨((-13598920111/2251799813685248), (8339681977/2251799813685248)), (113/2251799813685248), by norm_num⟩
  | 12 => ⟨((8820758887/9007199254740992), (-5409423933/9007199254740992)), (37/4503599627370496), by norm_num⟩
  | 13 => ⟨((-5281355151/36028797018963968), (202427941/2251799813685248)), (179/144115188075855872), by norm_num⟩
  | 14 => ⟨((11745191531/576460752303423488), (-3601431633/288230376151711744)), (101/576460752303423488), by norm_num⟩
  | 15 => ⟨((-3047344987/1152921504606846976), (1868816631/1152921504606846976)), (107/4611686018427387904), by norm_num⟩
  | 16 => ⟨((2964929769/9223372036854775808), (-3636549249/18446744073709551616)), (105/36893488147419103232), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-716583512707/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111211236388603/39614081257132168796771975168), (-848593944485/633825300114114700748351602688)), (5769/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945214577391967/19807040628566084398385987584), (-954526944681/39614081257132168796771975168)), (3245/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945123543352731/1237940039285380274899124224), (-1014011225357/2475880078570760549798248448)), (431/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771913226028579/154742504910672534362390528), (-506907959701/77371252455336267181195264)), (431/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775115344143655/4835703278458516698824704), (-950244963239/9671406556917033397649408)), (3233/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259381171618797/604462909807314587353088), (-831256939437/604462909807314587353088)), (2829/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888754618522189/75557863725914323419136), (-1350403768007/75557863725914323419136)), (9195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298261191109147/4722366482869645213696), (-1012462784997/4722366482869645213696)), (6897/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622440191079635/590295810358705651712), (-173947999099/73786976294838206464)), (9485/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824714243724205/73786976294838206464), (-1738651888541/73786976294838206464)), (5929/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912025405965745/4611686018427387904), (-244355673415/1152921504606846976)), (6671/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199412310950243/144115188075855872), (-1953423882971/1152921504606846976)), (13345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597864188755357/72057594037927936), (-1707648051387/144115188075855872)), (11681/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493356957286837/36028797018963968), (-1279139873571/18014398509481984)), (2191/4503599627370496), by norm_num⟩
  | 3 => ⟨((745701931519567/4503599627370496), (-3192270663967/9007199254740992)), (10961/4503599627370496), by norm_num⟩
  | 2 => ⟨((558057668147855/1125899906842624), (-6367834457049/4503599627370496)), (43881/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222503237081731/2251799813685248), (-1188761248345/281474976710656)), (65917/2251799813685248), by norm_num⟩
  | 0 => ⟨((548358686298097/562949953421312), (-9427082293157/1125899906842624)), (132217/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548358686298097/562949953421312), (-9427082293157/1125899906842624)), (504367836959075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((534106148408203/562949953421312), (-36730955783779/2251799813685248)), (259795/2251799813685248), by norm_num⟩
  | 2 => ⟨((126647605768369/140737488355328), (-69697951662655/2251799813685248)), (125361/562949953421312), by norm_num⟩
  | 3 => ⟨((1821335928089527/2251799813685248), (-125440333036903/2251799813685248)), (933527/2251799813685248), by norm_num⟩
  | 4 => ⟨((733086765913289/1125899906842624), (-101460611197813/1125899906842624)), (403537/562949953421312), by norm_num⟩
  | 5 => ⟨((936356682381805/2251799813685248), (-264248823109591/2251799813685248)), (2392901/2251799813685248), by norm_num⟩
  | 6 => ⟨((716703493109933/4503599627370496), (-439526017946067/4503599627370496)), (2551675/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-15327337233/268435456)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-962887821/536870912), (-32758246089/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-45266420174835/1125899906842624), (5680268215455/35184372088832)), (23935603/9007199254740992), by norm_num⟩
  | 1 => ⟨((2872585283/34359738368), (-1441868371/4294967296)), (191/34359738368), by norm_num⟩
  | 2 => ⟨((-2986686585/34359738368), (11993123953/34359738368)), (25/4294967296), by norm_num⟩
  | 3 => ⟨((4140426771/68719476736), (-4156500027/17179869184)), (279/68719476736), by norm_num⟩
  | 4 => ⟨((-2152443857/68719476736), (1080399853/8589934592)), (73/34359738368), by norm_num⟩
  | 5 => ⟨((1790352469/137438953472), (-7189210675/137438953472)), (245/274877906944), by norm_num⟩
  | 6 => ⟨((-620488883/137438953472), (19932724439/1099511627776)), (171/549755813888), by norm_num⟩
  | 7 => ⟨((2949189393/2199023255552), (-11842552925/2199023255552)), (409/4398046511104), by norm_num⟩
  | 8 => ⟨((-3066333469/8796093022208), (384779633/274877906944)), (107/4398046511104), by norm_num⟩
  | 9 => ⟨((2833893865/35184372088832), (-11379580491/35184372088832)), (199/35184372088832), by norm_num⟩
  | 10 => ⟨((-2357166651/140737488355328), (295789655/4398046511104)), (333/281474976710656), by norm_num⟩
  | 11 => ⟨((3564792913/1125899906842624), (-7157263083/562949953421312)), (127/562949953421312), by norm_num⟩
  | 12 => ⟨((-2470926157/4503599627370496), (9922073453/4503599627370496)), (177/4503599627370496), by norm_num⟩
  | 13 => ⟨((1580968153/18014398509481984), (-6348422067/18014398509481984)), (455/72057594037927936), by norm_num⟩
  | 14 => ⟨((-1878589059/144115188075855872), (7543527183/144115188075855872)), (17/18014398509481984), by norm_num⟩
  | 15 => ⟨((4166843871/2305843009213693952), (-16732078715/2305843009213693952)), (303/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-2166177061/9223372036854775808), (17396689779/18446744073709551616)), (159/9223372036854775808), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790819754617223/5070602400912917605986812821504), (295508019851/1267650600228229401496703205376)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779198333787695/633825300114114700748351602688), (2799044953429/633825300114114700748351602688)), (4335/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890224838111243/39614081257132168796771975168), (3148422326191/39614081257132168796771975168)), (2439/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118126859868327/154742504910672534362390528), (836146472805/618970019642690137449562112)), (10367/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442923906193527/38685626227668133590597632), (3343896567793/154742504910672534362390528)), (5185/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550026397814685/9671406556917033397649408), (3134170759221/9671406556917033397649408)), (2431/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259202128353683/604462909807314587353088), (1370833645417/302231454903657293676544)), (8511/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944231565782555/37778931862957161709568), (4453836933973/75557863725914323419136)), (6917/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649021051180215/2361183241434822606848), (3339177156459/4722366482869645213696)), (10379/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811069087669067/295147905179352825856), (1147354575545/147573952589676412928)), (14277/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912167786167943/36893488147419103232), (1433462122239/18446744073709551616)), (17855/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823623225219143/9223372036854775808), (1611640052669/2305843009213693952)), (5025/2305843009213693952), by norm_num⟩
  | 6 => ⟨((6229956747813/4503599627370496), (3220769289603/576460752303423488)), (5029/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195350296772703/144115188075855872), (5630700417791/144115188075855872)), (17619/144115188075855872), by norm_num⟩
  | 4 => ⟨((373196354077017/9007199254740992), (263586490307/1125899906842624)), (827/1125899906842624), by norm_num⟩
  | 3 => ⟨((186335215934091/1125899906842624), (10523734140893/9007199254740992)), (16571/4503599627370496), by norm_num⟩
  | 2 => ⟨((139422710935083/281474976710656), (20988370542413/4503599627370496)), (8309/562949953421312), by norm_num⟩
  | 1 => ⟨((1110122539429807/1125899906842624), (31335086836199/2251799813685248)), (100177/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188691701294135/2251799813685248), (7760243756535/281474976710656)), (101119/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2188691701294135/2251799813685248), (7760243756535/281474976710656)), (385738377097701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2125640638968705/2251799813685248), (7542758022593/140737488355328)), (404293/2251799813685248), by norm_num⟩
  | 2 => ⟨((500020410320813/562949953421312), (227845376098385/2251799813685248)), (806621/2251799813685248), by norm_num⟩
  | 3 => ⟨((876723817186707/1125899906842624), (404751213687911/2251799813685248)), (399035/562949953421312), by norm_num⟩
  | 4 => ⟨((1292634915332107/2251799813685248), (630349157893693/2251799813685248)), (3059587/2251799813685248), by norm_num⟩
  | 5 => ⟨((565576458323827/2251799813685248), (723697839738317/2251799813685248)), (163301/70368744177664), by norm_num⟩
  | 6 => ⟨((-45266420174835/1125899906842624), (5680268215455/35184372088832)), (23935603/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-962887821/536870912), (-32758246089/536870912)), (3/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨48,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile048Terms0
