/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile039Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (34337/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (34337/1280))
  have he : value ((69/80), (34337/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-20060163/33554432), (-2495673243/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((599165799960839/1125899906842624), (312811612733803/2251799813685248)), (736375/140737488355328), by norm_num⟩
  | 1 => ⟨((-3168564491/8589934592), (-1654239559/17179869184)), (65/17179869184), by norm_num⟩
  | 2 => ⟨((4392563087/34359738368), (573315743/17179869184)), (47/34359738368), by norm_num⟩
  | 3 => ⟨((-1014897573/34359738368), (-1059712509/137438953472)), (45/137438953472), by norm_num⟩
  | 4 => ⟨((5627787131/1099511627776), (367268369/274877906944)), (65/1099511627776), by norm_num⟩
  | 5 => ⟨((-6241415653/8796093022208), (-1629254621/8796093022208)), (75/8796093022208), by norm_num⟩
  | 6 => ⟨((1442073221/17592186044416), (376437749/17592186044416)), (71/70368744177664), by norm_num⟩
  | 7 => ⟨((-1142364557/140737488355328), (-596404033/281474976710656)), (29/281474976710656), by norm_num⟩
  | 8 => ⟨((6334614175/9007199254740992), (206697887/1125899906842624)), (83/9007199254740992), by norm_num⟩
  | 9 => ⟨((-121967221/2251799813685248), (-1018823521/72057594037927936)), (53/72057594037927936), by norm_num⟩
  | 10 => ⟨((4328511251/1152921504606846976), (564955721/576460752303423488)), (61/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-545508249/2305843009213693952), (-569596313/9223372036854775808)), (63/18446744073709551616), by norm_num⟩
  | 12 => ⟨((504156673/36893488147419103232), (526418771/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-3440785491/4722366482869645213696), (-112272519/590295810358705651712)), (53/4722366482869645213696), by norm_num⟩
  | 14 => ⟨((2725680871/75557863725914323419136), (2779335/295147905179352825856)), (43/75557863725914323419136), by norm_num⟩
  | 15 => ⟨((-4030502423/2417851639229258349412352), (-1052119433/2417851639229258349412352)), (33/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((2793731391/38685626227668133590597632), (1458547237/77371252455336267181195264)), (47/38685626227668133590597632), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (41576315935/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111315521310543/39614081257132168796771975168), (197293313491/316912650057057350374175801344)), (11531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892306110577413/39614081257132168796771975168), (443886001389/39614081257132168796771975168)), (3243/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892241142929575/2475880078570760549798248448), (235800045763/1237940039285380274899124224)), (13783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773907046816401/154742504910672534362390528), (117891927789/38685626227668133590597632)), (1723/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552099645160561/9671406556917033397649408), (55257541003/1208925819614629174706176)), (12923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315254064701937/151115727451828646838272), (96692097291/151115727451828646838272)), (2827/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891411166398727/75557863725914323419136), (314217071741/37778931862957161709568)), (18375/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81265824493569/295147905179352825856), (471269186885/4722366482869645213696)), (13783/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406294631469755/147573952589676412928), (323951730771/295147905179352825856)), (2369/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828136163077373/73786976294838206464), (404870922241/36893488147419103232)), (23691/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827899097832889/9223372036854775808), (910770574361/9223372036854775808)), (26655/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99946566091993/72057594037927936), (227633595005/288230376151711744)), (13329/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199092196549223/144115188075855872), (199112985391/36028797018963968)), (11665/72057594037927936), by norm_num⟩
  | 4 => ⟨((749199414496257/18014398509481984), (298536706147/9007199254740992)), (4375/4503599627370496), by norm_num⟩
  | 3 => ⟨((1497699458449903/9007199254740992), (1491754563831/9007199254740992)), (43761/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122400825907657/2251799813685248), (1490361986425/2251799813685248)), (87557/4503599627370496), by norm_num⟩
  | 1 => ⟨((280163656324665/281474976710656), (1116032294839/562949953421312)), (131423/2251799813685248), by norm_num⟩
  | 0 => ⟨((557711348129769/562949953421312), (8900467853307/2251799813685248)), (65799/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557711348129769/562949953421312), (8900467853307/2251799813685248)), (251003267528343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2210050785487453/2251799813685248), (8817643371823/1125899906842624)), (523575/2251799813685248), by norm_num⟩
  | 2 => ⟨((2168937683275719/2251799813685248), (17308323361261/1125899906842624)), (1035937/2251799813685248), by norm_num⟩
  | 3 => ⟨((65268517836269/70368744177664), (33342817193969/1125899906842624)), (2027485/2251799813685248), by norm_num⟩
  | 4 => ⟨((483809875806727/562949953421312), (123704709195409/2251799813685248)), (1940579/1125899906842624), by norm_num⟩
  | 5 => ⟨((828192865348145/1125899906842624), (212628350455681/2251799813685248)), (7097513/2251799813685248), by norm_num⟩
  | 6 => ⟨((599165799960839/1125899906842624), (312811612733803/2251799813685248)), (736375/140737488355328), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-2495673243/134217728)), (1/134217728), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-494443563/16777216)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-318940074644853/2251799813685248), (50790654909587/140737488355328)), (28197665/2251799813685248), by norm_num⟩
  | 1 => ⟨((1336637441/8589934592), (-851428797/2147483648)), (15/1073741824), by norm_num⟩
  | 2 => ⟨((-734223159/8589934592), (3741560557/17179869184)), (67/8589934592), by norm_num⟩
  | 3 => ⟨((2151004227/68719476736), (-5480699209/68719476736)), (199/68719476736), by norm_num⟩
  | 4 => ⟨((-2363119677/274877906944), (3010581751/137438953472)), (221/274877906944), by norm_num⟩
  | 5 => ⟨((2076921853/1099511627776), (-5291939373/1099511627776)), (197/1099511627776), by norm_num⟩
  | 6 => ⟨((-380288645/1099511627776), (3875859751/4398046511104)), (73/2199023255552), by norm_num⟩
  | 7 => ⟨((1909896131/35184372088832), (-4866362459/35184372088832)), (185/35184372088832), by norm_num⟩
  | 8 => ⟨((-65569855/8796093022208), (5346245599/281474976710656)), (103/140737488355328), by norm_num⟩
  | 9 => ⟨((1024509845/1125899906842624), (-2610422717/1125899906842624)), (51/562949953421312), by norm_num⟩
  | 10 => ⟨((-1800862569/18014398509481984), (4588547961/18014398509481984)), (181/18014398509481984), by norm_num⟩
  | 11 => ⟨((44964767/4503599627370496), (-1833103701/72057594037927936)), (147/144115188075855872), by norm_num⟩
  | 12 => ⟨((-1053842039/1152921504606846976), (5370320673/2305843009213693952)), (109/1152921504606846976), by norm_num⟩
  | 13 => ⟨((1424940079/18446744073709551616), (-907676967/4611686018427387904)), (149/18446744073709551616), by norm_num⟩
  | 14 => ⟨((-894546675/147573952589676412928), (4558560321/295147905179352825856)), (95/147573952589676412928), by norm_num⟩
  | 15 => ⟨((2096554603/4722366482869645213696), (-667745385/590295810358705651712)), (225/4722366482869645213696), by norm_num⟩
  | 16 => ⟨((-2303300651/75557863725914323419136), (2934373143/37778931862957161709568)), (125/37778931862957161709568), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (633327700921/2535301200456458802993406410752)), (7279/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890251672535149/316912650057057350374175801344), (3003618207303/633825300114114700748351602688)), (271/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((472923187514291/9903520314283042199192993792), (1689387414915/19807040628566084398385987584)), (19515/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891589149014799/2475880078570760549798248448), (1794799994303/1237940039285380274899124224)), (20739/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773254717347325/154742504910672534362390528), (1794604071121/77371252455336267181195264)), (2593/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775743864935983/4835703278458516698824704), (420558284103/1208925819614629174706176)), (4863/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260480476648335/604462909807314587353088), (1471745800729/302231454903657293676544)), (8513/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890539852636181/75557863725914323419136), (4782393069529/75557863725914323419136)), (27675/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299599122565901/4722366482869645213696), (896527890135/1180591620717411303424)), (20765/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624278232049125/590295810358705651712), (2464896511091/295147905179352825856)), (7141/147573952589676412928), by norm_num⟩
  | 8 => ⟨((913504686971487/36893488147419103232), (3080287766199/36893488147419103232)), (8931/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913314753241453/4611686018427387904), (3464178387157/4611686018427387904)), (40217/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798936513176571/576460752303423488), (6925492951461/1152921504606846976)), (40251/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197976427602767/144115188075855872), (3028291958833/72057594037927936)), (17629/72057594037927936), by norm_num⟩
  | 4 => ⟨((748359849845865/18014398509481984), (4539214759099/18014398509481984)), (26481/18014398509481984), by norm_num⟩
  | 3 => ⟨((747795490511833/4503599627370496), (5668376175075/4503599627370496)), (2073/281474976710656), by norm_num⟩
  | 2 => ⟨((1120278033752205/2251799813685248), (11319818734369/2251799813685248)), (66537/2251799813685248), by norm_num⟩
  | 1 => ⟨((558717384543275/562949953421312), (16937370491957/1125899906842624)), (50153/562949953421312), by norm_num⟩
  | 0 => ⟨((1108841024541835/1125899906842624), (1053286587631/35184372088832)), (101311/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108841024541835/1125899906842624), (1053286587631/35184372088832)), (386470796825218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1091031602101153/1125899906842624), (66388985201509/1125899906842624)), (411237/1125899906842624), by norm_num⟩
  | 2 => ⟨((1053328499469439/1125899906842624), (128665932817057/1125899906842624)), (845501/1125899906842624), by norm_num⟩
  | 3 => ⟨((121341382000801/140737488355328), (30093148849947/140737488355328)), (443813/281474976710656), by norm_num⟩
  | 4 => ⟨((392734971744609/562949953421312), (415132520880477/1125899906842624)), (238773/70368744177664), by norm_num⟩
  | 5 => ⟨((789818028281487/2251799813685248), (1158447978314303/2251799813685248)), (8147693/1125899906842624), by norm_num⟩
  | 6 => ⟨((-318940074644853/2251799813685248), (50790654909587/140737488355328)), (28197665/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-494443563/16777216)), (3/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-20060163/16777216), (-2495673243/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((1188513748137947/4503599627370496), (83233873207383/562949953421312)), (15962395/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3142604651/8589934592), (-1760660539/8589934592)), (43/4294967296), by norm_num⟩
  | 2 => ⟨((4356575107/17179869184), (2440793777/17179869184)), (121/17179869184), by norm_num⟩
  | 3 => ⟨((-4026330337/34359738368), (-2255772433/34359738368)), (57/17179869184), by norm_num⟩
  | 4 => ⟨((2790839521/68719476736), (781791151/34359738368)), (81/68719476736), by norm_num⟩
  | 5 => ⟨((-3095140073/274877906944), (-1734068263/274877906944)), (23/68719476736), by norm_num⟩
  | 6 => ⟨((715129205/274877906944), (801309685/549755813888)), (87/1099511627776), by norm_num⟩
  | 7 => ⟨((-4532020957/8796093022208), (-79346507/274877906944)), (35/2199023255552), by norm_num⟩
  | 8 => ⟨((3141357549/35184372088832), (439990461/8796093022208)), (99/35184372088832), by norm_num⟩
  | 9 => ⟨((-1935487225/140737488355328), (-1084366747/140737488355328)), (31/70368744177664), by norm_num⟩
  | 10 => ⟨((2146524021/1125899906842624), (2405202411/2251799813685248)), (139/2251799813685248), by norm_num⟩
  | 11 => ⟨((-2164155743/9007199254740992), (-1212479469/9007199254740992)), (71/9007199254740992), by norm_num⟩
  | 12 => ⟨((1000052301/36028797018963968), (2241137935/144115188075855872)), (67/72057594037927936), by norm_num⟩
  | 13 => ⟨((-1706297681/576460752303423488), (-1911924235/1152921504606846976)), (29/288230376151711744), by norm_num⟩
  | 14 => ⟨((2703349547/9223372036854775808), (189320699/1152921504606846976)), (93/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-1998740391/73786976294838206464), (-2239609323/147573952589676412928)), (35/36893488147419103232), by norm_num⟩
  | 16 => ⟨((1385421267/590295810358705651712), (194047361/147573952589676412928)), (99/1180591620717411303424), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (41576315935/633825300114114700748351602688)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111257792961313/39614081257132168796771975168), (394198252581/316912650057057350374175801344)), (11535/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891267069147279/39614081257132168796771975168), (886851530181/39614081257132168796771975168)), (25955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891137244070229/2475880078570760549798248448), (471082384069/1237940039285380274899124224)), (13789/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772803240943311/154742504910672534362390528), (942035435839/154742504910672534362390528)), (6895/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387766231486157/2417851639229258349412352), (220755207289/2417851639229258349412352)), (12929/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260110978275111/604462909807314587353088), (772505860143/604462909807314587353088)), (5657/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((7382579182537/295147905179352825856), (1255064519127/75557863725914323419136)), (36773/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299150182173241/4722366482869645213696), (941073130137/4722366482869645213696)), (27583/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623662150769335/590295810358705651712), (40425300423/18446744073709551616)), (37931/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114140068063747/4611686018427387904), (50514477857/2305843009213693952)), (11855/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825767682309565/9223372036854775808), (1817767005991/9223372036854775808)), (53357/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597014320288339/1152921504606846976), (1816824710769/1152921504606846976)), (53369/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149653570555067/18014398509481984), (794331079709/72057594037927936)), (46711/144115188075855872), by norm_num⟩
  | 4 => ⟨((93475306635623/2251799813685248), (297609482781/4503599627370496)), (70093/36028797018963968), by norm_num⟩
  | 3 => ⟨((747104861556213/4503599627370496), (2972392899055/9007199254740992)), (87663/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118915090545719/2251799813685248), (741711740299/562949953421312)), (175465/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230872028213421/2251799813685248), (2218214956161/562949953421312)), (263549/2251799813685248), by norm_num⟩
  | 0 => ⟨((552512696371863/562949953421312), (8817643371823/1125899906842624)), (528509/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552512696371863/562949953421312), (8817643371823/1125899906842624)), (2016101845748137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2168937683275717/2251799813685248), (17308323361261/1125899906842624)), (1045699/2251799813685248), by norm_num⟩
  | 2 => ⟨((2088592570760605/2251799813685248), (33342817193969/1125899906842624)), (1023295/1125899906842624), by norm_num⟩
  | 3 => ⟨((1935239503226903/2251799813685248), (123704709195409/2251799813685248)), (1958865/1125899906842624), by norm_num⟩
  | 4 => ⟨((1656385730696281/2251799813685248), (212628350455681/2251799813685248)), (895549/281474976710656), by norm_num⟩
  | 5 => ⟨((2340491406097/4398046511104), (156405806366901/1125899906842624)), (11893021/2251799813685248), by norm_num⟩
  | 6 => ⟨((1188513748137947/4503599627370496), (83233873207383/562949953421312)), (15962395/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-2495673243/67108864)), (1/67108864), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-2911141/2097152), (-2897386909/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((776608409586433/4503599627370496), (812316960524377/4503599627370496)), (32032785/4503599627370496), by norm_num⟩
  | 1 => ⟨((-596000203/2147483648), (-311702183/1073741824)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((1918450645/8589934592), (2006661243/8589934592)), (163/17179869184), by norm_num⟩
  | 3 => ⟨((-1029209067/8589934592), (-4306128909/34359738368)), (177/34359738368), by norm_num⟩
  | 4 => ⟨((3312896185/68719476736), (3465223561/68719476736)), (9/4294967296), by norm_num⟩
  | 5 => ⟨((-66648759/4294967296), (-1115412435/68719476736)), (47/68719476736), by norm_num⟩
  | 6 => ⟨((1144181755/274877906944), (598395687/137438953472)), (103/549755813888), by norm_num⟩
  | 7 => ⟨((-2104559423/2199023255552), (-1100663663/1099511627776)), (3/68719476736), by norm_num⟩
  | 8 => ⟨((846789431/4398046511104), (442862457/2199023255552)), (157/17592186044416), by norm_num⟩
  | 9 => ⟨((-1211426679/35184372088832), (-316782057/8796093022208)), (57/35184372088832), by norm_num⟩
  | 10 => ⟨((3119545641/562949953421312), (203936421/35184372088832)), (149/562949953421312), by norm_num⟩
  | 11 => ⟨((-3651429109/4503599627370496), (-3819322271/4503599627370496)), (177/4503599627370496), by norm_num⟩
  | 12 => ⟨((3917832295/36028797018963968), (4097974709/36028797018963968)), (3/562949953421312), by norm_num⟩
  | 13 => ⟨((-3880312511/288230376151711744), (-4058729761/288230376151711744)), (3/4503599627370496), by norm_num⟩
  | 14 => ⟨((3568641181/2305843009213693952), (3732727745/2305843009213693952)), (179/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-765800855/4611686018427387904), (-3204049893/18446744073709551616)), (155/18446744073709551616), by norm_num⟩
  | 16 => ⟨((2465017859/147573952589676412928), (1289179843/73786976294838206464)), (63/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (1052337980147/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444956778115353/158456325028528675187087900672), (1246798240769/633825300114114700748351602688)), (23081/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945466153379987/19807040628566084398385987584), (350618711999/9903520314283042199192993792)), (25969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945390784555317/1237940039285380274899124224), (744959204037/1237940039285380274899124224)), (13797/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886223788665959/77371252455336267181195264), (1489680947125/154742504910672534362390528)), (6899/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775365751687863/4835703278458516698824704), (1396323633251/9671406556917033397649408)), (25875/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629909622802291/302231454903657293676544), (610765488969/302231454903657293676544)), (22643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472366556951747/18889465931478580854784), (992257537845/37778931862957161709568)), (36799/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649397334918679/2361183241434822606848), (185996594053/590295810358705651712)), (6901/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623173353615141/590295810358705651712), (127830670117/36893488147419103232)), (37963/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228203767638943/9223372036854775808), (2555606056079/73786976294838206464)), (5933/9223372036854775808), by norm_num⟩
  | 7 => ⟨((228135054095701/1152921504606846976), (359209039697/1152921504606846976)), (13353/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399081788621963/288230376151711744), (358992825775/144115188075855872)), (53431/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196627388819841/144115188075855872), (627751275759/36028797018963968)), (46773/144115188075855872), by norm_num⟩
  | 4 => ⟨((747351666127831/18014398509481984), (1881310708855/18014398509481984)), (70201/36028797018963968), by norm_num⟩
  | 3 => ⟨((746541544368661/4503599627370496), (18345636203/35184372088832)), (43913/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235577916834163/4503599627370496), (9372612039427/4503599627370496)), (687/17592186044416), by norm_num⟩
  | 1 => ⟨((2227496162033985/2251799813685248), (14008131760413/2251799813685248)), (264365/2251799813685248), by norm_num⟩
  | 0 => ⟨((1101654643642291/1125899906842624), (27813705074341/2251799813685248)), (530963/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1101654643642291/1125899906842624), (27813705074341/2251799813685248)), (2025463112837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2155519413291409/2251799813685248), (27214761424017/1125899906842624)), (65761/140737488355328), by norm_num⟩
  | 2 => ⟨((2062040035663537/2251799813685248), (52102275007793/1125899906842624)), (2065243/2251799813685248), by norm_num⟩
  | 3 => ⟨((470862295868827/562949953421312), (190846408925475/2251799813685248)), (3973553/2251799813685248), by norm_num⟩
  | 4 => ⟨((1559178774949845/2251799813685248), (19953456279469/140737488355328)), (7320655/2251799813685248), by norm_num⟩
  | 5 => ⟨((1034334620342281/2251799813685248), (27632123716115/140737488355328)), (12213669/2251799813685248), by norm_num⟩
  | 6 => ⟨((776608409586433/4503599627370496), (812316960524377/4503599627370496)), (32032785/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-2897386909/67108864)), (1/67108864), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-6451221747/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-565238946060663/4503599627370496), (194079549992599/1125899906842624)), (21513603/2251799813685248), by norm_num⟩
  | 1 => ⟨((241463717/1073741824), (-2653075191/8589934592)), (149/8589934592), by norm_num⟩
  | 2 => ⟨((-3461159211/17179869184), (1188418149/4294967296)), (269/17179869184), by norm_num⟩
  | 3 => ⟨((258398533/2147483648), (-2839145963/17179869184)), (81/8589934592), by norm_num⟩
  | 4 => ⟨((-1851952073/34359738368), (635883333/8589934592)), (147/34359738368), by norm_num⟩
  | 5 => ⟨((2654602131/137438953472), (-3645919947/137438953472)), (213/137438953472), by norm_num⟩
  | 6 => ⟨((-792734751/137438953472), (4355074393/549755813888)), (1/2147483648), by norm_num⟩
  | 7 => ⟨((3246605707/2199023255552), (-2229498795/1099511627776)), (33/274877906944), by norm_num⟩
  | 8 => ⟨((-2908568259/8796093022208), (1997362789/4398046511104)), (119/4398046511104), by norm_num⟩
  | 9 => ⟨((1158101049/17592186044416), (-3181149947/35184372088832)), (191/35184372088832), by norm_num⟩
  | 10 => ⟨((-1660030817/140737488355328), (4559884433/281474976710656)), (69/70368744177664), by norm_num⟩
  | 11 => ⟨((2163182499/1125899906842624), (-2970987677/1125899906842624)), (181/1125899906842624), by norm_num⟩
  | 12 => ⟨((-2583935151/9007199254740992), (221803971/562949953421312)), (109/4503599627370496), by norm_num⟩
  | 13 => ⟨((712275427/18014398509481984), (-3913052213/72057594037927936)), (121/36028797018963968), by norm_num⟩
  | 14 => ⟨((-2917088551/576460752303423488), (250401727/36028797018963968)), (125/288230376151711744), by norm_num⟩
  | 15 => ⟨((348448069/576460752303423488), (-3828562479/4611686018427387904)), (241/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-2497340509/36893488147419103232), (1714965769/18446744073709551616)), (109/18446744073709551616), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (716480332791/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444894781469677/158456325028528675187087900672), (3394631241979/633825300114114700748351602688)), (11567/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472663262202009/9903520314283042199192993792), (3818425853237/39614081257132168796771975168)), (26031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890484508556539/2475880078570760549798248448), (2028218143109/1237940039285380274899124224)), (1729/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((55379691387455/4835703278458516698824704), (1013928741761/38685626227668133590597632)), (3459/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550452224562319/9671406556917033397649408), (3801466439995/9671406556917033397649408)), (25949/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259574460195783/604462909807314587353088), (3325516860803/604462909807314587353088)), (22713/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472266917798019/18889465931478580854784), (5402528278093/75557863725914323419136)), (36923/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298495070103727/4722366482869645213696), (4050639309001/4722366482869645213696)), (3463/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622760296249171/590295810358705651712), (5567586857573/590295810358705651712)), (1191/18446744073709551616), by norm_num⟩
  | 8 => ⟨((114069509967867/4611686018427387904), (3478210377895/36893488147419103232)), (23835/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824495423778001/9223372036854775808), (7821762746715/9223372036854775808)), (26835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99733706251101/72057594037927936), (122132822617/18014398509481984)), (53721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196109820611275/144115188075855872), (6833519796849/144115188075855872)), (5883/18014398509481984), by norm_num⟩
  | 4 => ⟨((186740075361099/4503599627370496), (10238447146219/36028797018963968)), (35355/18014398509481984), by norm_num⟩
  | 3 => ⟨((373023387185465/2251799813685248), (12777360979121/9007199254740992)), (88589/9007199254740992), by norm_num⟩
  | 2 => ⟨((69798924314041/140737488355328), (1593291516889/281474976710656)), (22223/562949953421312), by norm_num⟩
  | 1 => ⟨((139024684210451/140737488355328), (9520994859353/562949953421312)), (134097/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098389334528905/1125899906842624), (37774329835633/1125899906842624)), (67809/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098389334528905/1125899906842624), (37774329835633/1125899906842624)), (258670807958507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1045198849529/1099511627776), (4606417581869/70368744177664)), (273709/562949953421312), by norm_num⟩
  | 2 => ⟨((1012589963978343/1125899906842624), (140123952791899/1125899906842624)), (139053/140737488355328), by norm_num⟩
  | 3 => ⟨((893244334502117/1125899906842624), (63010977906531/281474976710656)), (2277835/1125899906842624), by norm_num⟩
  | 4 => ⟨((652242089433781/1125899906842624), (799846575126351/2251799813685248)), (9268241/2251799813685248), by norm_num⟩
  | 5 => ⟨((471589180672549/2251799813685248), (926713996894905/2251799813685248)), (4330635/562949953421312), by norm_num⟩
  | 6 => ⟨((-565238946060663/4503599627370496), (194079549992599/1125899906842624)), (21513603/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-6451221747/134217728)), (1/67108864), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-225263989/134217728), (-3503120281/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-599075309512527/9007199254740992), (-196393133828137/1125899906842624)), (18283607/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111742711/8589934592), (5831350591/17179869184)), (273/17179869184), by norm_num⟩
  | 2 => ⟨((-16901183/134217728), (-5673642149/17179869184)), (67/4294967296), by norm_num⟩
  | 3 => ⟨((350807291/4294967296), (3680132613/17179869184)), (175/17179869184), by norm_num⟩
  | 4 => ⟨((-170659867/4294967296), (-3580603701/34359738368)), (43/8589934592), by norm_num⟩
  | 5 => ⟨((1062684055/68719476736), (5574026465/137438953472)), (135/68719476736), by norm_num⟩
  | 6 => ⟨((-86161987/17179869184), (-3615518223/274877906944)), (11/17179869184), by norm_num⟩
  | 7 => ⟨((1532923291/1099511627776), (4020270631/1099511627776)), (197/1099511627776), by norm_num⟩
  | 8 => ⟨((-1491465495/4398046511104), (-3911542711/4398046511104)), (193/4398046511104), by norm_num⟩
  | 9 => ⟨((1289892375/17592186044416), (3382893627/17592186044416)), (169/17592186044416), by norm_num⟩
  | 10 => ⟨((-2008011731/140737488355328), (-5266245633/140737488355328)), (265/140737488355328), by norm_num⟩
  | 11 => ⟨((44402391/17592186044416), (3726414845/562949953421312)), (189/562949953421312), by norm_num⟩
  | 12 => ⟨((-921632675/2251799813685248), (-2417089489/2251799813685248)), (247/4503599627370496), by norm_num⟩
  | 13 => ⟨((17244369/281474976710656), (723605995/4503599627370496)), (149/18014398509481984), by norm_num⟩
  | 14 => ⟨((-306797647/36028797018963968), (-402306357/18014398509481984)), (167/144115188075855872), by norm_num⟩
  | 15 => ⟨((1273601397/1152921504606846976), (417521079/144115188075855872)), (175/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-619578471/4611686018427387904), (-812458505/2305843009213693952)), (43/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532090827/10141204801825835211973625643008), (-630163634223/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222421925479471/79228162514264337593543950336), (-373126812543/79228162514264337593543950336)), (5781/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945211988492135/19807040628566084398385987584), (-1678818101493/19807040628566084398385987584)), (6505/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945120631486455/1237940039285380274899124224), (-1783438321251/1237940039285380274899124224)), (27651/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771907039904131/154742504910672534362390528), (-3566188415991/154742504910672534362390528)), (27657/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775112251976339/4835703278458516698824704), (-3342570504715/9671406556917033397649408)), (25935/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259375375706235/604462909807314587353088), (-2924018174821/604462909807314587353088)), (5675/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888744479476349/75557863725914323419136), (-4750159129379/75557863725914323419136)), (36899/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649126478348371/2361183241434822606848), (-445177561847/590295810358705651712)), (13843/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202803480711585/73786976294838206464), (-4895005517753/590295810358705651712)), (9521/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228087159867377/9223372036854775808), (-6115836230199/73786976294838206464)), (47631/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824029621124885/9223372036854775808), (-6876301185939/9223372036854775808)), (53621/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199409333599643/144115188075855872), (-1717821246633/288230376151711744)), (26833/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195704584752529/144115188075855872), (-1501683478337/36028797018963968)), (1469/4503599627370496), by norm_num⟩
  | 4 => ⟨((46666105578511/1125899906842624), (-4499413455087/18014398509481984)), (70613/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491341611851085/9007199254740992), (-11228819832923/9007199254740992)), (22111/2251799813685248), by norm_num⟩
  | 2 => ⟨((279009431680137/562949953421312), (-2799820100245/562949953421312)), (44355/1125899906842624), by norm_num⟩
  | 1 => ⟨((277774252861635/281474976710656), (-8362590799225/562949953421312)), (133733/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096256603392791/1125899906842624), (-16578032773405/562949953421312)), (270143/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096256603392791/1125899906842624), (-16578032773405/562949953421312)), (1030513767722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((266604342113953/281474976710656), (-64566229337641/1125899906842624)), (541973/1125899906842624), by norm_num⟩
  | 2 => ⟨((1006374722021997/1125899906842624), (-122310247941047/1125899906842624)), (1088841/1125899906842624), by norm_num⟩
  | 3 => ⟨((1772502650207477/2251799813685248), (-218651659928271/1125899906842624)), (2183069/1125899906842624), by norm_num⟩
  | 4 => ⟨((1310299180905517/2251799813685248), (-172111501359817/562949953421312)), (2142357/562949953421312), by norm_num⟩
  | 5 => ⟨((275985021741839/1125899906842624), (-400599658789579/1125899906842624)), (3803203/562949953421312), by norm_num⟩
  | 6 => ⟨((-599075309512527/9007199254740992), (-196393133828137/1125899906842624)), (18283607/2251799813685248), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-225263989/134217728), (-3503120281/67108864)), (1/67108864), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-240721955/134217728), (-7487019729/134217728)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((539986461544229/4503599627370496), (1038915757523111/9007199254740992)), (62900603/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4283410187/17179869184), (-4120568437/17179869184)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((2226775271/8589934592), (267765037/1073741824)), (133/8589934592), by norm_num⟩
  | 3 => ⟨((-1543483001/8589934592), (-2969609287/17179869184)), (187/17179869184), by norm_num⟩
  | 4 => ⟨((3209582671/34359738368), (3087564457/34359738368)), (197/34359738368), by norm_num⟩
  | 5 => ⟨((-2669655815/68719476736), (-1284081959/34359738368)), (83/34359738368), by norm_num⟩
  | 6 => ⟨((3700928803/274877906944), (1780115579/137438953472)), (233/274877906944), by norm_num⟩
  | 7 => ⟨((-2198818599/549755813888), (-132201653/34359738368)), (35/137438953472), by norm_num⟩
  | 8 => ⟨((2286157369/2199023255552), (2199244873/2199023255552)), (147/2199023255552), by norm_num⟩
  | 9 => ⟨((-4225716093/17592186044416), (-508133461/2199023255552)), (275/17592186044416), by norm_num⟩
  | 10 => ⟨((3514851835/70368744177664), (422653531/8796093022208)), (231/70368744177664), by norm_num⟩
  | 11 => ⟨((-1328896167/140737488355328), (-319593931/35184372088832)), (177/281474976710656), by norm_num⟩
  | 12 => ⟨((1842241263/1125899906842624), (3544410115/2251799813685248)), (31/281474976710656), by norm_num⟩
  | 13 => ⟨((-589358925/2251799813685248), (-1133906713/4503599627370496)), (5/281474976710656), by norm_num⟩
  | 14 => ⟨((2801228415/72057594037927936), (2694734541/72057594037927936)), (3/1125899906842624), by norm_num⟩
  | 15 => ⟨((-3106661725/576460752303423488), (-2988556239/576460752303423488)), (215/576460752303423488), by norm_num⟩
  | 16 => ⟨((807515181/1152921504606846976), (3107263997/4611686018427387904)), (113/2305843009213693952), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509236873/10141204801825835211973625643008), (124728947805/1267650600228229401496703205376)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889600888621003/316912650057057350374175801344), (295357408639/158456325028528675187087900672)), (8655/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890228909119619/39614081257132168796771975168), (166112312875/4951760157141521099596496896)), (38949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945017168348625/1237940039285380274899124224), (1411696298033/2475880078570760549798248448)), (41387/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885850244208273/77371252455336267181195264), (1411405725301/154742504910672534362390528)), (41391/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550031259953679/9671406556917033397649408), (1322884213521/9671406556917033397649408)), (4851/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314801671253019/151115727451828646838272), (289303780603/151115727451828646838272)), (33961/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888471102524573/75557863725914323419136), (3671672277/147573952589676412928)), (55193/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81128035985811/295147905179352825856), (1409416272407/4722366482869645213696)), (20701/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622147880223231/590295810358705651712), (1937125672705/590295810358705651712)), (56937/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824348908052397/73786976294838206464), (2420175161395/73786976294838206464)), (35593/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455909970530379/2305843009213693952), (680251041459/2305843009213693952)), (40053/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594887648945403/1152921504606846976), (169930598121/72057594037927936)), (80133/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195368996408679/144115188075855872), (594162884587/36028797018963968)), (35073/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492818091514609/36028797018963968), (3560228844815/36028797018963968)), (105279/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490730642093081/9007199254740992), (2220993975771/4503599627370496)), (131705/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230885318402759/4503599627370496), (1107391043407/562949953421312)), (131863/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220487938623325/2251799813685248), (1653342124721/281474976710656)), (198193/1125899906842624), by norm_num⟩
  | 0 => ⟨((2189415160418059/2251799813685248), (3275828728005/281474976710656)), (397985/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189415160418059/2251799813685248), (3275828728005/281474976710656)), (1518192295554732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2128453838610911/2251799813685248), (25480592143009/1125899906842624)), (391591/562949953421312), by norm_num⟩
  | 2 => ⟨((2010711020258821/2251799813685248), (48169703032445/1125899906842624)), (1516013/1125899906842624), by norm_num⟩
  | 3 => ⟨((111957041577219/140737488355328), (86024834127169/1125899906842624)), (2837123/1125899906842624), by norm_num⟩
  | 4 => ⟨((1411848405424497/2251799813685248), (136865962915761/1125899906842624)), (4947421/1125899906842624), by norm_num⟩
  | 5 => ⟨((851934857184605/2251799813685248), (85813130601189/562949953421312)), (14813531/2251799813685248), by norm_num⟩
  | 6 => ⟨((539986461544229/4503599627370496), (1038915757523111/9007199254740992)), (62900603/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-240721955/134217728), (-7487019729/134217728)), (3/134217728), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile039Terms0
