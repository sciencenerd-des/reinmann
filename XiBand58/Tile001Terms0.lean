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
namespace Reinmann.XiBand58.Tile001Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((15/16), (4659/320)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((15/16), (4659/320))
  have he : value ((15/16), (4659/320))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21804525/33554432), (-1354497089/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-923754219692097/2251799813685248), (181841434794655/562949953421312)), (6527789/281474976710656), by norm_num⟩
  | 1 => ⟨((610635407/2147483648), (-480815421/2147483648)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((-846520421/8589934592), (666551707/8589934592)), (53/8589934592), by norm_num⟩
  | 3 => ⟨((782350991/34359738368), (-308012291/17179869184)), (51/34359738368), by norm_num⟩
  | 4 => ⟨((-1084568767/274877906944), (213497851/68719476736)), (73/274877906944), by norm_num⟩
  | 5 => ⟨((300706313/549755813888), (-473553387/1099511627776)), (21/549755813888), by norm_num⟩
  | 6 => ⟨((-69477911/1099511627776), (109414065/2199023255552)), (5/1099511627776), by norm_num⟩
  | 7 => ⟨((440305537/70368744177664), (-693394749/140737488355328)), (65/140737488355328), by norm_num⟩
  | 8 => ⟨((-610393083/1125899906842624), (480624615/1125899906842624)), (47/1125899906842624), by norm_num⟩
  | 9 => ⟨((376081995/9007199254740992), (-592255283/18014398509481984)), (15/4503599627370496), by norm_num⟩
  | 10 => ⟨((-417088279/144115188075855872), (656832127/288230376151711744)), (69/288230376151711744), by norm_num⟩
  | 11 => ⟨((105128569/576460752303423488), (-662227399/4611686018427387904)), (9/576460752303423488), by norm_num⟩
  | 12 => ⟨((-388637713/36893488147419103232), (612028073/73786976294838206464)), (17/18446744073709551616), by norm_num⟩
  | 13 => ⟨((165774237/295147905179352825856), (-522123733/1180591620717411303424)), (15/295147905179352825856), by norm_num⟩
  | 14 => ⟨((-16415135/590295810358705651712), (413609821/18889465931478580854784)), (97/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((388372635/302231454903657293676544), (-611610627/604462909807314587353088)), (37/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-269199397/4835703278458516698824704), (847872363/19342813113834066795298816)), (105/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395782324214913/2535301200456458802993406410752), (402927236301/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780960302086167/633825300114114700748351602688), (1911858806913/316912650057057350374175801344)), (2893/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236525825616329/4951760157141521099596496896), (537676461229/4951760157141521099596496896)), (6511/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892134854173631/2475880078570760549798248448), (4569944460049/2475880078570760549798248448)), (13839/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773800123642233/154742504910672534362390528), (2284800329395/77371252455336267181195264)), (13843/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775999365375841/4835703278458516698824704), (267727199455/604462909807314587353088)), (6491/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((315231821230025/151115727451828646838272), (3747815211449/604462909807314587353088)), (22727/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472816330204927/18889465931478580854784), (6089513926041/75557863725914323419136)), (36947/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300142702903481/4722366482869645213696), (4566535047873/4722366482869645213696)), (6931/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625024808808649/590295810358705651712), (6278009431323/590295810358705651712)), (19071/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913970662876501/36893488147419103232), (7846046324505/73786976294838206464)), (47711/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456919051868979/2305843009213693952), (8824785355053/9223372036854775808)), (53721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598917546766415/1152921504606846976), (4411130894143/576460752303423488)), (26889/576460752303423488), by norm_num⟩
  | 5 => ⟨((599443965190695/72057594037927936), (964579557259/18014398509481984)), (2945/9007199254740992), by norm_num⟩
  | 4 => ⟨((374520512531363/9007199254740992), (1446157562559/4503599627370496)), (35405/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497285340776423/9007199254740992), (903224415113/562949953421312)), (44369/4503599627370496), by norm_num⟩
  | 2 => ⟨((280489883155431/562949953421312), (14436572933591/2251799813685248)), (89079/2251799813685248), by norm_num⟩
  | 1 => ⟨((279981222094953/281474976710656), (21617174684239/1125899906842624)), (134469/1125899906842624), by norm_num⟩
  | 0 => ⟨((1113692888414613/1125899906842624), (43082770778593/1125899906842624)), (272351/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1113692888414613/1125899906842624), (43082770778593/1125899906842624)), (1038936619285201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((549984824157389/562949953421312), (85231333864961/1125899906842624)), (559641/1125899906842624), by norm_num⟩
  | 2 => ⟨((66761532243683/70368744177664), (166536793842981/1125899906842624)), (294559/281474976710656), by norm_num⟩
  | 3 => ⟨((494397259266467/562949953421312), (315999714414027/1125899906842624)), (323029/140737488355328), by norm_num⟩
  | 4 => ⟨((779695224269821/1125899906842624), (555038300601329/1125899906842624)), (5989683/1125899906842624), by norm_num⟩
  | 5 => ⟨((66581657435173/281474976710656), (1537474902113777/2251799813685248)), (28402635/2251799813685248), by norm_num⟩
  | 6 => ⟨((-923754219692097/2251799813685248), (181841434794655/562949953421312)), (6527789/281474976710656), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/33554432), (-1354497089/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-69118709/67108864), (-1073413547/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1542065157512149/4503599627370496), (111177104635/1099511627776)), (137578431/4503599627370496), by norm_num⟩
  | 1 => ⟨((807824961/2147483648), (-477111459/4294967296)), (147/4294967296), by norm_num⟩
  | 2 => ⟨((-887486429/4294967296), (1023751/16777216)), (83/4294967296), by norm_num⟩
  | 3 => ⟨((1300004663/17179869184), (-383899453/17179869184)), (31/4294967296), by norm_num⟩
  | 4 => ⟨((-714100549/34359738368), (421756657/68719476736)), (139/68719476736), by norm_num⟩
  | 5 => ⟨((627615711/137438953472), (-370677637/274877906944)), (31/68719476736), by norm_num⟩
  | 6 => ⟨((-919341777/1099511627776), (135743669/549755813888)), (93/1099511627776), by norm_num⟩
  | 7 => ⟨((1154285913/8796093022208), (-340867801/8796093022208)), (119/8796093022208), by norm_num⟩
  | 8 => ⟨((-1268112689/70368744177664), (374481555/70368744177664)), (133/70368744177664), by norm_num⟩
  | 9 => ⟨((1238368163/562949953421312), (-91424453/140737488355328)), (33/140737488355328), by norm_num⟩
  | 10 => ⟨((-544194593/2251799813685248), (40176011/562949953421312)), (59/2251799813685248), by norm_num⟩
  | 11 => ⟨((434806449/18014398509481984), (-256802091/36028797018963968)), (3/1125899906842624), by norm_num⟩
  | 12 => ⟨((-636911611/288230376151711744), (376167911/576460752303423488)), (143/576460752303423488), by norm_num⟩
  | 13 => ⟨((107649065/576460752303423488), (-254315501/4611686018427387904)), (99/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-270319053/18446744073709551616), (159653791/36893488147419103232)), (127/73786976294838206464), by norm_num⟩
  | 15 => ⟨((633548445/590295810358705651712), (-187090791/590295810358705651712)), (151/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-1392048215/18889465931478580854784), (102770121/4722366482869645213696)), (169/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98914633969175/633825300114114700748351602688), (1859118369425/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780370544630267/633825300114114700748351602688), (4407926451015/633825300114114700748351602688)), (46317/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945771516521683/19807040628566084398385987584), (4958432170069/39614081257132168796771975168)), (52121/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945714840063813/1237940039285380274899124224), (5267776948631/2475880078570760549798248448)), (27697/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773094804693733/154742504910672534362390528), (329196864385/9671406556917033397649408)), (13853/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551337340421657/9671406556917033397649408), (4937286491457/9671406556917033397649408)), (51969/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260348414726325/604462909807314587353088), (1079864756187/151115727451828646838272)), (11373/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472581092248341/18889465931478580854784), (7017870552387/75557863725914323419136)), (9245/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162429592198011/590295810358705651712), (328894278939/295147905179352825856)), (55501/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624053698529331/590295810358705651712), (7233894934583/590295810358705651712)), (38183/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913363413538433/36893488147419103232), (9039698608949/73786976294838206464)), (47767/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826309058399089/9223372036854775808), (2541496891359/2305843009213693952)), (53791/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399387338209449/288230376151711744), (10161392801717/1152921504606846976)), (53857/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197689588989831/144115188075855872), (8886045405205/144115188075855872)), (1475/2251799813685248), by norm_num⟩
  | 4 => ⟨((374070551003337/9007199254740992), (13318711074261/36028797018963968)), (141897/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495031469698793/9007199254740992), (8315120307869/4503599627370496)), (177895/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119699608583031/2251799813685248), (8301485811345/1125899906842624)), (178681/2251799813685248), by norm_num⟩
  | 1 => ⟨((1116520017527069/1125899906842624), (24836122497219/1125899906842624)), (269989/1125899906842624), by norm_num⟩
  | 0 => ⟨((1106824092566269/1125899906842624), (49397937152805/1125899906842624)), (547873/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1106824092566269/1125899906842624), (49397937152805/1125899906842624)), (2089969639304732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((542952090261203/562949953421312), (48561001410085/562949953421312)), (1125257/1125899906842624), by norm_num⟩
  | 2 => ⟨((1038951330162729/1125899906842624), (93671904795595/562949953421312)), (1182351/562949953421312), by norm_num⟩
  | 3 => ⟨((231886102198767/281474976710656), (345752049519845/1125899906842624)), (321945/70368744177664), by norm_num⟩
  | 4 => ⟨((657957377949553/1125899906842624), (569678314053533/1125899906842624)), (11650953/1125899906842624), by norm_num⟩
  | 5 => ⟨((192511837041165/2251799813685248), (1331642528830147/2251799813685248)), (793983/35184372088832), by norm_num⟩
  | 6 => ⟨((-1542065157512149/4503599627370496), (111177104635/1099511627776)), (137578431/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/67108864), (-1073413547/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-1354497089/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((288001569142519/4503599627370496), (-1193546898338349/4503599627370496)), (45009699/2251799813685248), by norm_num⟩
  | 1 => ⟨((-380759193/4294967296), (1577956519/4294967296)), (121/4294967296), by norm_num⟩
  | 2 => ⟨((263922161/4294967296), (-68359757/268435456)), (43/2147483648), by norm_num⟩
  | 3 => ⟨((-243915869/8589934592), (1010845287/8589934592)), (81/8589934592), by norm_num⟩
  | 4 => ⟨((169069597/17179869184), (-1401329121/34359738368)), (115/34359738368), by norm_num⟩
  | 5 => ⟨((-187504183/68719476736), (1554123727/137438953472)), (65/68719476736), by norm_num⟩
  | 6 => ⟨((173290661/274877906944), (-718157653/274877906944)), (61/274877906944), by norm_num⟩
  | 7 => ⟨((-17159419/137438953472), (142225415/274877906944)), (99/2199023255552), by norm_num⟩
  | 8 => ⟨((380608093/17592186044416), (-1577330327/17592186044416)), (35/4398046511104), by norm_num⟩
  | 9 => ⟨((-234504379/70368744177664), (971841839/70368744177664)), (11/8796093022208), by norm_num⟩
  | 10 => ⟨((260073679/562949953421312), (-1077807089/562949953421312)), (99/562949953421312), by norm_num⟩
  | 11 => ⟨((-262209945/4503599627370496), (271665071/1125899906842624)), (51/2251799813685248), by norm_num⟩
  | 12 => ⟨((242333445/36028797018963968), (-502143675/18014398509481984)), (97/36028797018963968), by norm_num⟩
  | 13 => ⟨((-206735685/288230376151711744), (1713523557/576460752303423488)), (21/72057594037927936), by norm_num⟩
  | 14 => ⟨((163769437/2305843009213693952), (-1357398883/4611686018427387904)), (135/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-242168157/36893488147419103232), (250900589/9223372036854775808)), (101/36893488147419103232), by norm_num⟩
  | 16 => ⟨((335716351/590295810358705651712), (-1391288287/590295810358705651712)), (71/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (-1737714603069/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889981128001635/316912650057057350374175801344), (-2059125109769/633825300114114700748351602688)), (23101/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118192765035899/2475880078570760549798248448), (-579061377627/9903520314283042199192993792)), (51983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890942870653111/2475880078570760549798248448), (-2460684159197/2475880078570760549798248448)), (6905/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772608734777561/154742504910672534362390528), (-2460316668345/154742504910672534362390528)), (55249/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775441217716025/4835703278458516698824704), (-576539117031/2417851639229258349412352)), (12951/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629975579082777/302231454903657293676544), (-504374139511/151115727451828646838272)), (22669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944840149497165/37778931862957161709568), (-409712514815/9444732965739290427392)), (36845/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649477486236483/2361183241434822606848), (-614408723753/1180591620717411303424)), (55283/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623393362503825/590295810358705651712), (-3378207892255/590295810358705651712)), (76037/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912952270895907/36893488147419103232), (-527650016177/9223372036854775808)), (95083/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825388294874819/9223372036854775808), (-2373353076673/4611686018427387904)), (107017/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596633969305323/1152921504606846976), (-1186006782501/288230376151711744)), (13385/144115188075855872), by norm_num⟩
  | 5 => ⟨((149611834374377/18014398509481984), (-1037002791783/36028797018963968)), (23441/36028797018963968), by norm_num⟩
  | 4 => ⟨((11680483683345/281474976710656), (-6215994931725/36028797018963968)), (140785/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493577208099787/9007199254740992), (-7759462961535/9007199254740992)), (88113/4503599627370496), by norm_num⟩
  | 2 => ⟨((559138468325195/1125899906842624), (-483980116761/140737488355328)), (176593/2251799813685248), by norm_num⟩
  | 1 => ⟨((1114464750935501/1125899906842624), (-5788061219305/562949953421312)), (265807/1125899906842624), by norm_num⟩
  | 0 => ⟨((1103027125417773/1125899906842624), (-22994957680819/1125899906842624)), (535293/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1103027125417773/1125899906842624), (-22994957680819/1125899906842624)), (2041980747703170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2160298733373361/2251799813685248), (-45055625132621/1125899906842624)), (2141405/2251799813685248), by norm_num⟩
  | 2 => ⟨((1034454872870279/1125899906842624), (-86449611829439/1125899906842624)), (535021/281474976710656), by norm_num⟩
  | 3 => ⟨((1887598253026831/2251799813685248), (-317712868333001/2251799813685248)), (2130589/562949953421312), by norm_num⟩
  | 4 => ⟨((1537474902113783/2251799813685248), (-532653259481389/2251799813685248)), (16692823/2251799813685248), by norm_num⟩
  | 5 => ⟨((923754219692103/2251799813685248), (-363682869589315/1125899906842624)), (15346073/1125899906842624), by norm_num⟩
  | 6 => ⟨((288001569142519/4503599627370496), (-1193546898338349/4503599627370496)), (45009699/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-1354497089/67108864)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-50628539/33554432), (-1572522423/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-257321831144475/9007199254740992), (1975384245889259/9007199254740992)), (164527367/9007199254740992), by norm_num⟩
  | 1 => ⟨((197479015/4294967296), (-378997123/1073741824)), (1/33554432), by norm_num⟩
  | 2 => ⟨((-158915107/4294967296), (1219944677/4294967296)), (105/4294967296), by norm_num⟩
  | 3 => ⟨((42627333/2147483648), (-1308950143/8589934592)), (57/4294967296), by norm_num⟩
  | 4 => ⟨((-34303023/4294967296), (1053336993/17179869184)), (93/17179869184), by norm_num⟩
  | 5 => ⟨((88333737/34359738368), (-1356224393/68719476736)), (61/34359738368), by norm_num⟩
  | 6 => ⟨((-189556887/274877906944), (1455172637/274877906944)), (133/274877906944), by norm_num⟩
  | 7 => ⟨((43582863/274877906944), (-1338291435/1099511627776)), (31/274877906944), by norm_num⟩
  | 8 => ⟨((-8767989/274877906944), (1076948487/4398046511104)), (101/4398046511104), by norm_num⟩
  | 9 => ⟨((200697371/35184372088832), (-1540694867/35184372088832)), (147/35184372088832), by norm_num⟩
  | 10 => ⟨((-129203983/140737488355328), (247965273/35184372088832)), (3/4398046511104), by norm_num⟩
  | 11 => ⟨((151233301/1125899906842624), (-580486853/562949953421312)), (57/562949953421312), by norm_num⟩
  | 12 => ⟨((-2535423/140737488355328), (311419183/2251799813685248)), (31/2251799813685248), by norm_num⟩
  | 13 => ⟨((80356547/36028797018963968), (-616873649/36028797018963968)), (31/18014398509481984), by norm_num⟩
  | 14 => ⟨((-147804427/576460752303423488), (1134651243/576460752303423488)), (29/144115188075855872), by norm_num⟩
  | 15 => ⟨((63435213/2305843009213693952), (-973947055/4611686018427387904)), (101/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-102095037/36893488147419103232), (1567507315/73786976294838206464)), (165/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582010324067835/10141204801825835211973625643008), (2214871130215/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889818996343899/316912650057057350374175801344), (1311816155473/316912650057057350374175801344)), (23115/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890719408783039/39614081257132168796771975168), (737796680555/9903520314283042199192993792)), (52017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236319398518771/309485009821345068724781056), (3135152502595/2475880078570760549798248448)), (55277/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772220997522899/154742504910672534362390528), (391826093359/19342813113834066795298816)), (6911/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550518873638263/9671406556917033397649408), (91816188661/302231454903657293676544)), (12961/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629816491770809/302231454903657293676544), (1285137853255/302231454903657293676544)), (45375/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944581578256331/37778931862957161709568), (2087807626537/37778931862957161709568)), (73755/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649283510308887/2361183241434822606848), (3130764201071/4722366482869645213696)), (6917/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622859774589099/590295810358705651712), (537907732563/73786976294838206464)), (76117/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912618663083587/36893488147419103232), (1344192389751/18446744073709551616)), (95191/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456159340188839/2305843009213693952), (1511423390477/2305843009213693952)), (107153/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595882640578313/1152921504606846976), (6041729803053/1152921504606846976)), (3351/36028797018963968), by norm_num⟩
  | 5 => ⟨((1196236819894645/144115188075855872), (660257048267/18014398509481984)), (46959/72057594037927936), by norm_num⟩
  | 4 => ⟨((747057123778893/18014398509481984), (1978543822755/9007199254740992)), (70527/18014398509481984), by norm_num⟩
  | 3 => ⟨((373085273562329/2251799813685248), (4938569664139/4503599627370496)), (44157/2251799813685248), by norm_num⟩
  | 2 => ⟨((1117038538309787/2251799813685248), (2463448150235/562949953421312)), (22137/281474976710656), by norm_num⟩
  | 1 => ⟨((556300749824373/562949953421312), (14722402470535/1125899906842624)), (266817/1125899906842624), by norm_num⟩
  | 0 => ⟨((549639175666555/562949953421312), (3651517751631/140737488355328)), (538331/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((549639175666555/562949953421312), (3651517751631/140737488355328)), (2053569797996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1072528327899969/1125899906842624), (14260714969355/281474976710656)), (269785/281474976710656), by norm_num⟩
  | 2 => ⟨((1018796714800015/1125899906842624), (108677659090549/1125899906842624)), (2165319/1125899906842624), by norm_num⟩
  | 3 => ⟨((911391773163485/1125899906842624), (393358029006689/2251799813685248)), (8673389/2251799813685248), by norm_num⟩
  | 4 => ⟨((703394968443471/1125899906842624), (318414869177719/1125899906842624)), (17072085/2251799813685248), by norm_num⟩
  | 5 => ⟨((698776952244855/2251799813685248), (795706316328881/2251799813685248)), (7746881/562949953421312), by norm_num⟩
  | 6 => ⟨((-257321831144475/9007199254740992), (1975384245889259/9007199254740992)), (164527367/9007199254740992), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50628539/33554432), (-1572522423/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-112727759/67108864), (-437665523/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((121376280271969/1125899906842624), (-684921399656525/4503599627370496)), (26071725/2251799813685248), by norm_num⟩
  | 1 => ⟨((-829609297/4294967296), (585181429/2147483648)), (91/4294967296), by norm_num⟩
  | 2 => ⟨((743230157/4294967296), (-1048504367/4294967296)), (83/4294967296), by norm_num⟩
  | 3 => ⟨((-887793115/8589934592), (626222543/4294967296)), (51/4294967296), by norm_num⟩
  | 4 => ⟨((198838965/4294967296), (-1122040171/17179869184)), (47/8589934592), by norm_num⟩
  | 5 => ⟨((-285017279/17179869184), (804170441/34359738368)), (69/34359738368), by norm_num⟩
  | 6 => ⟨((340454939/68719476736), (-960586669/137438953472)), (21/34359738368), by norm_num⟩
  | 7 => ⟨((-697158127/549755813888), (61469295/34359738368)), (11/68719476736), by norm_num⟩
  | 8 => ⟨((312284919/1099511627776), (-881105531/2199023255552)), (5/137438953472), by norm_num⟩
  | 9 => ⟨((-248684205/4398046511104), (701657413/8796093022208)), (65/8796093022208), by norm_num⟩
  | 10 => ⟨((712931647/70368744177664), (-1005761051/70368744177664)), (95/70368744177664), by norm_num⟩
  | 11 => ⟨((-464509829/281474976710656), (81912813/35184372088832)), (63/281474976710656), by norm_num⟩
  | 12 => ⟨((554859923/2251799813685248), (-391381489/1125899906842624)), (77/2251799813685248), by norm_num⟩
  | 13 => ⟨((-611800321/18014398509481984), (107886383/2251799813685248)), (87/18014398509481984), by norm_num⟩
  | 14 => ⟨((626399439/144115188075855872), (-883686621/144115188075855872)), (91/144115188075855872), by norm_num⟩
  | 15 => ⟨((-598590467/1152921504606846976), (422227699/576460752303423488)), (89/1152921504606846976), by norm_num⟩
  | 16 => ⟨((536265069/9223372036854775808), (-378265239/4611686018427387904)), (81/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790893836630535/5070602400912917605986812821504), (-310723941083/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889688403895279/316912650057057350374175801344), (-1471861015807/633825300114114700748351602688)), (46173/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890425764403467/39614081257132168796771975168), (-1655597740759/39614081257132168796771975168)), (51949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945121713979033/1237940039285380274899124224), (-1758771061885/2475880078570760549798248448)), (55201/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771909503795005/154742504910672534362390528), (-1758431915915/154742504910672534362390528)), (6901/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193778391409269/1208925819614629174706176), (-206021207661/1208925819614629174706176)), (51763/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259377991852353/604462909807314587353088), (-720894143395/302231454903657293676544)), (11325/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944374662573859/37778931862957161709568), (-585557712721/18889465931478580854784)), (9203/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298257110689367/4722366482869645213696), (-1756082610019/4722366482869645213696)), (13807/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811217200638285/295147905179352825856), (-1206827175471/295147905179352825856)), (18989/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824706737904621/73786976294838206464), (-3015629729877/73786976294838206464)), (47485/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824041999049897/9223372036854775808), (-3390606961471/9223372036854775808)), (106877/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595289214341549/1152921504606846976), (-3388137933555/1152921504606846976)), (106921/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195719746394249/144115188075855872), (-1480922601867/72057594037927936)), (46803/72057594037927936), by norm_num⟩
  | 4 => ⟨((373335744715799/9007199254740992), (-4437222246113/36028797018963968)), (140509/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491384589566743/9007199254740992), (-2768417627729/4503599627370496)), (175811/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232186744747671/4503599627370496), (-11044641508055/4503599627370496)), (88037/1125899906842624), by norm_num⟩
  | 1 => ⟨((2222423964384817/2251799813685248), (-8247279900047/1125899906842624)), (132385/562949953421312), by norm_num⟩
  | 0 => ⟨((2193223102474715/2251799813685248), (-16350264041591/1125899906842624)), (266093/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2193223102474715/2251799813685248), (-16350264041591/1125899906842624)), (1015064241649436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((533923822120463/562949953421312), (-63699759827037/2251799813685248)), (2104283/2251799813685248), by norm_num⟩
  | 2 => ⟨((2023775238875895/2251799813685248), (-120830702723421/2251799813685248)), (4110623/2251799813685248), by norm_num⟩
  | 3 => ⟨((1812357445792467/2251799813685248), (-108594992672743/1125899906842624)), (3914943/1125899906842624), by norm_num⟩
  | 4 => ⟨((718862307810269/1125899906842624), (-349610018350831/2251799813685248)), (14114155/2251799813685248), by norm_num⟩
  | 5 => ⟨((107959469443639/281474976710656), (-27902287660949/140737488355328)), (5601457/562949953421312), by norm_num⟩
  | 6 => ⟨((121376280271969/1125899906842624), (-684921399656525/4503599627370496)), (26071725/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-112727759/67108864), (-437665523/16777216)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-122426081/67108864), (-1901277035/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1450797828842509/9007199254740992), (82642061017269/9007199254740992)), (118651619/9007199254740992), by norm_num⟩
  | 1 => ⟨((168271197/536870912), (-76682103/4294967296)), (7/268435456), by norm_num⟩
  | 2 => ⟨((-163720315/536870912), (74608241/4294967296)), (111/4294967296), by norm_num⟩
  | 3 => ⟨((1699120121/8589934592), (-96787289/8589934592)), (73/4294967296), by norm_num⟩
  | 4 => ⟨((-206645943/2147483648), (23542421/4294967296)), (9/1073741824), by norm_num⟩
  | 5 => ⟨((1286766201/34359738368), (-36649149/17179869184)), (57/17179869184), by norm_num⟩
  | 6 => ⟨((-1669287607/137438953472), (95087935/137438953472)), (75/68719476736), by norm_num⟩
  | 7 => ⟨((29002533/8589934592), (-52866451/274877906944)), (169/549755813888), by norm_num⟩
  | 8 => ⟨((-902981173/1099511627776), (25718341/549755813888)), (83/1099511627776), by norm_num⟩
  | 9 => ⟨((195235581/1099511627776), (-88969921/8796093022208)), (145/8796093022208), by norm_num⟩
  | 10 => ⟨((-1215714875/35184372088832), (69250989/35184372088832)), (57/17592186044416), by norm_num⟩
  | 11 => ⟨((1720488665/281474976710656), (-98004511/281474976710656)), (163/281474976710656), by norm_num⟩
  | 12 => ⟨((-557986059/562949953421312), (15892331/281474976710656)), (107/1125899906842624), by norm_num⟩
  | 13 => ⟨((334089457/2251799813685248), (-19030799/2251799813685248)), (65/4503599627370496), by norm_num⟩
  | 14 => ⟨((-371490323/18014398509481984), (42322543/36028797018963968)), (147/72057594037927936), by norm_num⟩
  | 15 => ⟨((1542158485/576460752303423488), (-87846257/576460752303423488)), (77/288230376151711744), by norm_num⟩
  | 16 => ⟨((-375112731/1152921504606846976), (42735231/2305843009213693952)), (19/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395399856174459/2535301200456458802993406410752), (2009077193553/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889571480328521/316912650057057350374175801344), (4757241377755/633825300114114700748351602688)), (23167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472540524961095/9903520314283042199192993792), (2675501768291/19807040628566084398385987584)), (26071/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944981263416633/1237940039285380274899124224), (2842189532241/1237940039285380274899124224)), (27709/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885813875494349/77371252455336267181195264), (5683183952215/154742504910672534362390528)), (55437/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387490520909137/2417851639229258349412352), (5326715169551/9671406556917033397649408)), (51993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259145171383427/604462909807314587353088), (4659606011129/604462909807314587353088)), (45515/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888369298552371/75557863725914323419136), (7569479014259/75557863725914323419136)), (4625/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297970610341239/4722366482869645213696), (5675026152103/4722366482869645213696)), (55535/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405509515004103/147573952589676412928), (7799776004703/590295810358705651712)), (597/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1824207710555033/73786976294838206464), (4872321373389/36893488147419103232)), (95603/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823475648953915/9223372036854775808), (2738935536113/2305843009213693952)), (26917/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797358346968043/576460752303423488), (10947016399813/1152921504606846976)), (107811/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195211863320045/144115188075855872), (9568823503329/144115188075855872)), (94497/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492567333483033/36028797018963968), (14333605146579/36028797018963968)), (35517/9007199254740992), by norm_num⟩
  | 3 => ⟨((372597731107375/2251799813685248), (17882657429823/9007199254740992)), (22269/1125899906842624), by norm_num⟩
  | 2 => ⟨((278765925075017/562949953421312), (17831141599149/2251799813685248)), (44751/562949953421312), by norm_num⟩
  | 1 => ⟨((1109578000789681/1125899906842624), (26617951036879/1125899906842624)), (270639/1125899906842624), by norm_num⟩
  | 0 => ⟨((546494476425409/562949953421312), (26360518356895/562949953421312)), (274921/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((546494476425409/562949953421312), (26360518356895/562949953421312)), (1048740389110374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1058571313576229/1125899906842624), (102359917361765/1125899906842624)), (559517/562949953421312), by norm_num⟩
  | 2 => ⟨((123245377597247/140737488355328), (96238814410297/562949953421312)), (288463/140737488355328), by norm_num⟩
  | 3 => ⟨((830513827261499/1125899906842624), (337109583526525/1125899906842624)), (2415395/562949953421312), by norm_num⟩
  | 4 => ⟨((1023377553307931/2251799813685248), (497334032483011/1125899906842624)), (20039237/2251799813685248), by norm_num⟩
  | 5 => ⟨((51458443862697/4503599627370496), (1808190878233627/4503599627370496)), (8979505/562949953421312), by norm_num⟩
  | 6 => ⟨((-1450797828842509/9007199254740992), (82642061017269/9007199254740992)), (118651619/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-122426081/67108864), (-1901277035/67108864)), (1/33554432), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-65413575/33554432), (-1015872817/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((534774417598757/9007199254740992), (1165313582055209/9007199254740992)), (43802669/2251799813685248), by norm_num⟩
  | 1 => ⟨((-530258245/4294967296), (-144434063/536870912)), (11/268435456), by norm_num⟩
  | 2 => ⟨((551320511/4294967296), (1201368763/4294967296)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-191073129/2147483648), (-832725371/4294967296)), (131/4294967296), by norm_num⟩
  | 4 => ⟨((198662701/4294967296), (865801865/8589934592)), (69/4294967296), by norm_num⟩
  | 5 => ⟨((-660971957/34359738368), (-360076873/8589934592)), (29/4294967296), by norm_num⟩
  | 6 => ⟨((7158607/1073741824), (998345077/68719476736)), (163/68719476736), by norm_num⟩
  | 7 => ⟨((-544398803/274877906944), (-296571461/68719476736)), (49/68719476736), by norm_num⟩
  | 8 => ⟨((566022743/1099511627776), (77087877/68719476736)), (103/549755813888), by norm_num⟩
  | 9 => ⟨((-523116091/4398046511104), (-569954609/2199023255552)), (193/4398046511104), by norm_num⟩
  | 10 => ⟨((108778933/4398046511104), (948149833/17592186044416)), (163/17592186044416), by norm_num⟩
  | 11 => ⟨((-82254339/17592186044416), (-1433907019/140737488355328)), (125/70368744177664), by norm_num⟩
  | 12 => ⟨((456114905/562949953421312), (993908607/562949953421312)), (11/35184372088832), by norm_num⟩
  | 13 => ⟨((-583670327/4503599627370496), (-317965361/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | 14 => ⟨((346773807/18014398509481984), (755646149/18014398509481984)), (137/18014398509481984), by norm_num⟩
  | 15 => ⟨((-384584459/144115188075855872), (-209509599/36028797018963968)), (77/72057594037927936), by norm_num⟩
  | 16 => ⟨((199930225/576460752303423488), (871325927/1152921504606846976)), (81/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24709943068253/158456325028528675187087900672), (1485703277633/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444740091855623/158456325028528675187087900672), (1758615721189/633825300114114700748351602688)), (92373/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889957316203061/39614081257132168796771975168), (494525859987/9903520314283042199192993792)), (103931/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472436439334927/618970019642690137449562112), (1050658408633/1237940039285380274899124224)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771411895731835/154742504910672534362390528), (1050423302875/77371252455336267181195264)), (55227/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193720086272955/1208925819614629174706176), (1969044225267/9671406556917033397649408)), (103567/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258969922371183/604462909807314587353088), (1722414378101/604462909807314587353088)), (22659/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888086336886895/75557863725914323419136), (87437108031/2361183241434822606848)), (9207/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648879989284093/2361183241434822606848), (1048835994681/2361183241434822606848)), (110509/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810875510936465/295147905179352825856), (2882969346427/590295810358705651712)), (151991/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28497699680847/1152921504606846976), (900429564845/18446744073709551616)), (190051/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823081661621811/9223372036854775808), (4049193764935/9223372036854775808)), (53473/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594329334101959/1152921504606846976), (1011443047093/288230376151711744)), (106999/576460752303423488), by norm_num⟩
  | 5 => ⟨((298720091404799/36028797018963968), (3536204853157/144115188075855872)), (23421/18014398509481984), by norm_num⟩
  | 4 => ⟨((746042468405721/18014398509481984), (5296624304181/36028797018963968)), (281291/36028797018963968), by norm_num⟩
  | 3 => ⟨((744906919241857/4503599627370496), (3303677305461/4503599627370496)), (352033/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229050649147631/4503599627370496), (823406847981/281474976710656)), (705325/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108866672344725/1125899906842624), (19661536564209/2251799813685248)), (530573/1125899906842624), by norm_num⟩
  | 0 => ⟨((136493500035813/140737488355328), (38923786549989/2251799813685248)), (2134971/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((136493500035813/140737488355328), (38923786549989/2251799813685248)), (8144268044478606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1058683514223311/1125899906842624), (37750026115581/1125899906842624)), (2107495/1125899906842624), by norm_num⟩
  | 2 => ⟨((994214238773321/1125899906842624), (35496343917587/562949953421312)), (8209357/2251799813685248), by norm_num⟩
  | 3 => ⟨((1746908379469317/2251799813685248), (250757427602791/2251799813685248)), (3883411/562949953421312), by norm_num⟩
  | 4 => ⟨((331824523276641/562949953421312), (389066780120727/2251799813685248)), (6890273/562949953421312), by norm_num⟩
  | 5 => ⟨((357568923041909/1125899906842624), (14333190061093/70368744177664)), (2625949/140737488355328), by norm_num⟩
  | 6 => ⟨((534774417598757/9007199254740992), (1165313582055209/9007199254740992)), (43802669/2251799813685248), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65413575/33554432), (-1015872817/33554432)), (1/16777216), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand58.Tile001Terms0
