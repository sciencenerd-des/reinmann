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
namespace Reinmann.XiBand97.Tile058Terms0
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
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-2567700857/4294967296), (-5732918379/268435456)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-498769115619449/1125899906842624), (-734007636641801/2251799813685248)), (1715735/2251799813685248), by norm_num⟩
  | 1 => ⟨((42202198027/137438953472), (31053181387/137438953472)), (37/68719476736), by norm_num⟩
  | 2 => ⟨((-1828270911/17179869184), (-10762212563/137438953472)), (105/549755813888), by norm_num⟩
  | 3 => ⟨((1689681103/68719476736), (39785585571/2199023255552)), (99/2199023255552), by norm_num⟩
  | 4 => ⟨((-37478326163/8796093022208), (-55154532931/17592186044416)), (35/4398046511104), by norm_num⟩
  | 5 => ⟨((41564793779/70368744177664), (30584167197/70368744177664)), (79/70368744177664), by norm_num⟩
  | 6 => ⟨((-19207013079/281474976710656), (-14132886175/281474976710656)), (149/1125899906842624), by norm_num⟩
  | 7 => ⟨((60860740401/9007199254740992), (44782492367/9007199254740992)), (15/1125899906842624), by norm_num⟩
  | 8 => ⟨((-5273181327/9007199254740992), (-31040858323/72057594037927936)), (85/72057594037927936), by norm_num⟩
  | 9 => ⟨((51983513165/1152921504606846976), (38250459429/1152921504606846976)), (107/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-57651560937/18446744073709551616), (-42421116973/18446744073709551616)), (121/18446744073709551616), by norm_num⟩
  | 11 => ⟨((58125115517/295147905179352825856), (1336548983/9223372036854775808)), (31/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-26859506627/2361183241434822606848), (-39527473461/4722366482869645213696)), (117/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((45827917021/75557863725914323419136), (33721054503/75557863725914323419136)), (51/37778931862957161709568), by norm_num⟩
  | 14 => ⟨((-72606837655/2417851639229258349412352), (-13356373631/604462909807314587353088)), (41/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((26841186565/19342813113834066795298816), (39500512959/38685626227668133590597632)), (123/38685626227668133590597632), by norm_num⟩
  | 16 => ⟨((-74419571161/1237940039285380274899124224), (-6844917297/154742504910672534362390528)), (173/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (-3265946093761/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((890520213675773/316912650057057350374175801344), (-968624371881/158456325028528675187087900672)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((473074181754367/9903520314283042199192993792), (-4358555090125/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946115293661247/1237940039285380274899124224), (-1157669940827/618970019642690137449562112)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221736979064531/19342813113834066795298816), (-4630358948617/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((388022108005553/2417851639229258349412352), (-4340620499025/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630502873862639/302231454903657293676544), (-1898850876527/302231454903657293676544)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((945696387237285/37778931862957161709568), (-6170625272007/75557863725914323419136)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300238250775241/4722366482869645213696), (-2313704264795/2361183241434822606848)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812578059125791/295147905179352825856), (-6361775368937/590295810358705651712)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828105359182299/73786976294838206464), (-7950851001267/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456965150714429/2305843009213693952), (-8942824186229/9223372036854775808)), (105/576460752303423488), by norm_num⟩
  | 6 => ⟨((99943860264761/72057594037927936), (-4470233674243/576460752303423488)), (1681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599524460169489/72057594037927936), (-7820253572565/144115188075855872)), (737/72057594037927936), by norm_num⟩
  | 4 => ⟨((187290391745337/4503599627370496), (-11725059868423/36028797018963968)), (1107/18014398509481984), by norm_num⟩
  | 3 => ⟨((374396498164505/2251799813685248), (-14646992013731/9007199254740992)), (2775/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122259128156833/2251799813685248), (-14632948933409/2251799813685248)), (2785/2251799813685248), by norm_num⟩
  | 1 => ⟨((560185816973533/562949953421312), (-5478540647651/281474976710656)), (1051/281474976710656), by norm_num⟩
  | 0 => ⟨((1114575747712195/1125899906842624), (-21843183078879/562949953421312)), (2129/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114575747712195/1125899906842624), (-21843183078879/562949953421312)), (8121491552257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((275417599571199/281474976710656), (-43246974201871/562949953421312)), (17523/1125899906842624), by norm_num⟩
  | 2 => ⟨((1071317668662985/1125899906842624), (-84632587682143/562949953421312)), (36985/1125899906842624), by norm_num⟩
  | 3 => ⟨((496967288476209/562949953421312), (-322118817054747/1125899906842624)), (40753/562949953421312), by norm_num⟩
  | 4 => ⟨((392639436946155/562949953421312), (-568727341057459/1125899906842624)), (11909/70368744177664), by norm_num⟩
  | 5 => ⟨((260424678546733/1125899906842624), (-793337956994423/1125899906842624)), (458297/1125899906842624), by norm_num⟩
  | 6 => ⟨((-498769115619449/1125899906842624), (-734007636641801/2251799813685248)), (1715735/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-5732918379/268435456)), (1/2147483648), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-1017427393/1073741824), (-72691685203/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-10363891820173/35184372088832), (-283800621517825/1125899906842624)), (2437701/2251799813685248), by norm_num⟩
  | 1 => ⟨((44476167625/137438953472), (38059918253/137438953472)), (83/68719476736), by norm_num⟩
  | 2 => ⟨((-24431032153/137438953472), (-20906546949/137438953472)), (185/274877906944), by norm_num⟩
  | 3 => ⟨((71573952395/1099511627776), (61248505045/1099511627776)), (273/1099511627776), by norm_num⟩
  | 4 => ⟨((-39316011825/2199023255552), (-4205522519/274877906944)), (19/274877906944), by norm_num⟩
  | 5 => ⟨((17277221493/4398046511104), (59139055611/17592186044416)), (135/8796093022208), by norm_num⟩
  | 6 => ⟨((-50615914257/70368744177664), (-43313928823/70368744177664)), (25/8796093022208), by norm_num⟩
  | 7 => ⟨((63551160463/562949953421312), (27191551129/281474976710656)), (127/281474976710656), by norm_num⟩
  | 8 => ⟨((-17454521461/1125899906842624), (-59745944437/4503599627370496)), (141/2251799813685248), by norm_num⟩
  | 9 => ⟨((68180450737/36028797018963968), (58344558895/36028797018963968)), (139/18014398509481984), by norm_num⟩
  | 10 => ⟨((-59923104821/288230376151711744), (-51278439503/288230376151711744)), (247/288230376151711744), by norm_num⟩
  | 11 => ⟨((47878006787/2305843009213693952), (20485499557/1152921504606846976)), (25/288230376151711744), by norm_num⟩
  | 12 => ⟨((-35066244409/18446744073709551616), (-7501873851/4611686018427387904)), (37/4611686018427387904), by norm_num⟩
  | 13 => ⟨((23707204323/147573952589676412928), (40574280865/295147905179352825856)), (101/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-29765743999/2361183241434822606848), (-50943318357/4722366482869645213696)), (1/18446744073709551616), by norm_num⟩
  | 15 => ⟨((69762159229/75557863725914323419136), (7462260743/9444732965739290427392)), (151/37778931862957161709568), by norm_num⟩
  | 16 => ⟨((-19160391353/302231454903657293676544), (-16396262707/302231454903657293676544)), (21/75557863725914323419136), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (-1585133249777/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445125155369853/158456325028528675187087900672), (-58731629513/9903520314283042199192993792)), (1447/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891689523353855/39614081257132168796771975168), (-2114150430771/19807040628566084398385987584)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891585519457443/2475880078570760549798248448), (-4492133046321/2475880078570760549798248448)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773250861505201/154742504910672534362390528), (-4491641720819/154742504910672534362390528)), (1731/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387870968665723/2417851639229258349412352), (-4210391990683/9671406556917033397649408)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1260476863062533/604462909807314587353088), (-3683570768913/604462909807314587353088)), (1421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945266765103319/37778931862957161709568), (-2992411559215/37778931862957161709568)), (1155/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299593986853629/4722366482869645213696), (-4487760167569/4722366482869645213696)), (867/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812135265344599/295147905179352825856), (-6169276928531/590295810358705651712)), (2385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826998788162709/73786976294838206464), (-3854752755623/36893488147419103232)), (1491/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913308139821769/4611686018427387904), (-8670317926973/9223372036854775808)), (1679/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399464538391757/288230376151711744), (-4333360759107/576460752303423488)), (1681/576460752303423488), by norm_num⟩
  | 5 => ⟨((598980782040307/72057594037927936), (-3789666523331/72057594037927936)), (2945/144115188075855872), by norm_num⟩
  | 4 => ⟨((23385839209097/562949953421312), (-11360897216541/36028797018963968)), (4425/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495552037293757/9007199254740992), (-1773366176979/1125899906842624)), (5545/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120229427183211/2251799813685248), (-3541403847087/562949953421312)), (2783/1125899906842624), by norm_num⟩
  | 1 => ⟨((558668887730565/562949953421312), (-21195047928553/1125899906842624)), (4201/562949953421312), by norm_num⟩
  | 0 => ⟨((277137785711707/281474976710656), (-1318001825349/35184372088832)), (17013/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277137785711707/281474976710656), (-1318001825349/35184372088832)), (64899448875045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089889792996873/1125899906842624), (-83052352111101/1125899906842624)), (34777/1125899906842624), by norm_num⟩
  | 2 => ⟨((1048905023004547/1125899906842624), (-80396055013551/562949953421312)), (36231/562949953421312), by norm_num⟩
  | 3 => ⟨((954212393222421/1125899906842624), (-74898155174331/281474976710656)), (2433/17592186044416), by norm_num⟩
  | 4 => ⟨((728986251810477/1125899906842624), (-507815996519715/1125899906842624)), (346803/1125899906842624), by norm_num⟩
  | 5 => ⟨((121477880646815/562949953421312), (-1315182202831655/2251799813685248)), (1523855/2251799813685248), by norm_num⟩
  | 6 => ⟨((-10363891820173/35184372088832), (-283800621517825/1125899906842624)), (2437701/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-72691685203/2147483648)), (1/1073741824), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-2567700857/2147483648), (-5732918379/134217728)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((50661176602107/562949953421312), (650324842485157/2251799813685248)), (1518721/2251799813685248), by norm_num⟩
  | 1 => ⟨((-17146314319/137438953472), (-3439108513/8589934592)), (65/68719476736), by norm_num⟩
  | 2 => ⟨((11884919427/137438953472), (76281867821/274877906944)), (183/274877906944), by norm_num⟩
  | 3 => ⟨((-343249933/8589934592), (-70499415477/549755813888)), (171/549755813888), by norm_num⟩
  | 4 => ⟨((30454108581/2199023255552), (48866471069/1099511627776)), (15/137438953472), by norm_num⟩
  | 5 => ⟨((-16887343599/4398046511104), (-6774331329/549755813888)), (135/4398046511104), by norm_num⟩
  | 6 => ⟨((31214438941/35184372088832), (100172984765/35184372088832)), (63/8796093022208), by norm_num⟩
  | 7 => ⟨((-6181771527/35184372088832), (-39676926833/70368744177664)), (101/70368744177664), by norm_num⟩
  | 8 => ⟨((17139510019/562949953421312), (55003899935/562949953421312)), (141/562949953421312), by norm_num⟩
  | 9 => ⟨((-10560180485/2251799813685248), (-8472399591/562949953421312)), (11/281474976710656), by norm_num⟩
  | 10 => ⟨((11711614927/18014398509481984), (18792383645/9007199254740992)), (197/36028797018963968), by norm_num⟩
  | 11 => ⟨((-23615630157/288230376151711744), (-18946745803/72057594037927936)), (201/288230376151711744), by norm_num⟩
  | 12 => ⟨((10912738307/1152921504606846976), (35021022491/1152921504606846976)), (187/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-18619406251/18446744073709551616), (-59753164307/18446744073709551616)), (81/9223372036854775808), by norm_num⟩
  | 14 => ⟨((14749701653/147573952589676412928), (47334556993/147573952589676412928)), (259/295147905179352825856), by norm_num⟩
  | 15 => ⟨((-681580941/73786976294838206464), (-4374641963/147573952589676412928)), (97/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((30235898085/37778931862957161709568), (97032663763/37778931862957161709568)), (271/37778931862957161709568), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (413164549091/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890061485756103/316912650057057350374175801344), (1958672138433/633825300114114700748351602688)), (1445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891265037563407/39614081257132168796771975168), (2203269161679/39614081257132168796771975168)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891134958902709/2475880078570760549798248448), (2340687568439/2475880078570760549798248448)), (1727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27700012709331/2417851639229258349412352), (1170182972423/77371252455336267181195264)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775531249449181/4835703278458516698824704), (1096875693723/4835703278458516698824704)), (405/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260108703450285/604462909807314587353088), (1919190822277/604462909807314587353088)), (1417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889936290847983/75557863725914323419136), (3118044601679/75557863725914323419136)), (2303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299146949514949/4722366482869645213696), (2337973121045/4722366482869645213696)), (1729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25369645367555/9223372036854775808), (1606901340309/295147905179352825856)), (2377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826234426886369/73786976294838206464), (4015888117173/73786976294838206464)), (743/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912879679442687/4611686018427387904), (2257998717781/4611686018427387904)), (209/576460752303423488), by norm_num⟩
  | 6 => ⟨((798502481133845/576460752303423488), (4513652315219/1152921504606846976)), (1673/576460752303423488), by norm_num⟩
  | 5 => ⟨((598609606852915/72057594037927936), (1973404273381/72057594037927936)), (1465/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495588558767663/36028797018963968), (739367617587/4503599627370496)), (4399/36028797018963968), by norm_num⟩
  | 3 => ⟨((747092617375223/4503599627370496), (230764255929/281474976710656)), (5505/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118884537332781/2251799813685248), (7370637818545/2251799813685248)), (5517/2251799813685248), by norm_num⟩
  | 1 => ⟨((139421884895567/140737488355328), (11021451437983/1125899906842624)), (4151/562949953421312), by norm_num⟩
  | 0 => ⟨((276210860919563/281474976710656), (10952562812313/562949953421312)), (2089/140737488355328), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276210860919563/281474976710656), (10952562812313/562949953421312)), (7968903124761537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1083754597628495/1125899906842624), (42990916478865/1125899906842624)), (16725/562949953421312), by norm_num⟩
  | 2 => ⟨((2083090693682991/2251799813685248), (165526626681727/2251799813685248)), (133901/2251799813685248), by norm_num⟩
  | 3 => ⟨((1914853952719421/2251799813685248), (153125057343859/1125899906842624)), (8357/70368744177664), by norm_num⟩
  | 4 => ⟨((396668978497211/562949953421312), (520849357093447/2251799813685248)), (263779/1125899906842624), by norm_num⟩
  | 5 => ⟨((124692278904863/281474976710656), (734007636641773/2251799813685248)), (987515/2251799813685248), by norm_num⟩
  | 6 => ⟨((50661176602107/562949953421312), (650324842485157/2251799813685248)), (1518721/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-5732918379/134217728)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-6655712125/134217728)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((876278278225521/4503599627370496), (175911172543673/1125899906842624)), (1847463/4503599627370496), by norm_num⟩
  | 1 => ⟨((-672490827/2147483648), (-4320039525/17179869184)), (23/34359738368), by norm_num⟩
  | 2 => ⟨((4329328931/17179869184), (27811341579/137438953472)), (75/137438953472), by norm_num⟩
  | 3 => ⟨((-37161525957/274877906944), (-59680836711/549755813888)), (163/549755813888), by norm_num⟩
  | 4 => ⟨((59809168759/1099511627776), (3001643789/68719476736)), (133/1099511627776), by norm_num⟩
  | 5 => ⟨((-38503657485/2199023255552), (-30918139607/2199023255552)), (87/2199023255552), by norm_num⟩
  | 6 => ⟨((41312830749/8796093022208), (8293471011/2199023255552)), (95/8796093022208), by norm_num⟩
  | 7 => ⟨((-75989069803/70368744177664), (-30509318105/35184372088832)), (177/70368744177664), by norm_num⟩
  | 8 => ⟨((7643730617/35184372088832), (49102853241/281474976710656)), (9/17592186044416), by norm_num⟩
  | 9 => ⟨((-43740835013/1125899906842624), (-17561776359/562949953421312)), (105/1125899906842624), by norm_num⟩
  | 10 => ⟨((56318526553/9007199254740992), (45223341891/9007199254740992)), (137/9007199254740992), by norm_num⟩
  | 11 => ⟨((-65920852223/72057594037927936), (-3308370953/4503599627370496)), (163/72057594037927936), by norm_num⟩
  | 12 => ⟨((70730345859/576460752303423488), (56795921495/576460752303423488)), (177/576460752303423488), by norm_num⟩
  | 13 => ⟨((-35026492365/2305843009213693952), (-56252005739/4611686018427387904)), (89/2305843009213693952), by norm_num⟩
  | 14 => ⟨((64426245431/36893488147419103232), (404170137/288230376151711744)), (83/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-13825338927/73786976294838206464), (-44406561557/295147905179352825856)), (145/295147905179352825856), by norm_num⟩
  | 16 => ⟨((44502049243/2361183241434822606848), (35734801865/2361183241434822606848)), (59/1180591620717411303424), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (881298637995/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827360409635/633825300114114700748351602688), (1044152745769/633825300114114700748351602688)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236366575023745/4951760157141521099596496896), (293631744049/9903520314283042199192993792)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236347737394827/309485009821345068724781056), (1247758127443/2475880078570760549798248448)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772447927933149/154742504910672534362390528), (311889821455/38685626227668133590597632)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775365926946457/4835703278458516698824704), (1169375602573/9671406556917033397649408)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629909787062601/302231454903657293676544), (255748117719/151115727451828646838272)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889466802539683/75557863725914323419136), (1661966898903/75557863725914323419136)), (575/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298795136640531/4722366482869645213696), (623064444985/2361183241434822606848)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623174053527585/590295810358705651712), (1712864697029/590295810358705651712)), (2373/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912815551508227/36893488147419103232), (2140237405181/73786976294838206464)), (1483/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825081634435199/9223372036854775808), (37603247517/144115188075855872)), (1669/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399082126347133/288230376151711744), (2405159580279/1152921504606846976)), (3339/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196628738499587/144115188075855872), (525721605859/36028797018963968)), (2923/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494705691450923/36028797018963968), (1575537962511/18014398509481984)), (4385/36028797018963968), by norm_num⟩
  | 3 => ⟨((746543311024165/4503599627370496), (3933157002769/9007199254740992)), (5485/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235586730954145/4503599627370496), (7849274627593/4503599627370496)), (5491/2251799813685248), by norm_num⟩
  | 1 => ⟨((2227513732914137/2251799813685248), (5865699275629/1125899906842624)), (16501/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203361713898083/2251799813685248), (11646626498433/1125899906842624)), (16559/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203361713898083/2251799813685248), (11646626498433/1125899906842624)), (63167576316451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((269465575777157/281474976710656), (45584391235419/2251799813685248)), (65497/2251799813685248), by norm_num⟩
  | 2 => ⟨((515706437678869/562949953421312), (87278978573859/2251799813685248)), (64029/1125899906842624), by norm_num⟩
  | 3 => ⟨((1886327741879677/2251799813685248), (79954409536809/1125899906842624)), (122275/1125899906842624), by norm_num⟩
  | 4 => ⟨((784408431401787/1125899906842624), (133955265364431/1125899906842624)), (111113/562949953421312), by norm_num⟩
  | 5 => ⟨((530555665299343/1125899906842624), (186651831026771/1125899906842624)), (362527/1125899906842624), by norm_num⟩
  | 6 => ⟨((876278278225521/4503599627370496), (175911172543673/1125899906842624)), (1847463/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-6655712125/134217728)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-1659352607/1073741824), (-118555032235/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((108816318295849/2251799813685248), (467653998955655/2251799813685248)), (2215727/4503599627370496), by norm_num⟩
  | 1 => ⟨((-23800374599/274877906944), (-102285581171/274877906944)), (61/68719476736), by norm_num⟩
  | 2 => ⟨((21322273279/274877906944), (45817789657/137438953472)), (221/274877906944), by norm_num⟩
  | 3 => ⟨((-25469590035/549755813888), (-109459277969/549755813888)), (133/274877906944), by norm_num⟩
  | 4 => ⟨((22817689561/1099511627776), (49031174449/549755813888)), (15/68719476736), by norm_num⟩
  | 5 => ⟨((-16353524535/2199023255552), (-70281656885/2199023255552)), (87/1099511627776), by norm_num⟩
  | 6 => ⟨((9767194147/4398046511104), (10493985353/1099511627776)), (105/4398046511104), by norm_num⟩
  | 7 => ⟨((-10000264343/17592186044416), (-21488797287/8796093022208)), (217/35184372088832), by norm_num⟩
  | 8 => ⟨((17918068331/140737488355328), (77005512043/140737488355328)), (49/35184372088832), by norm_num⟩
  | 9 => ⟨((-7134415245/281474976710656), (-61322380171/562949953421312)), (79/281474976710656), by norm_num⟩
  | 10 => ⟨((5113262429/1125899906842624), (43949982139/2251799813685248)), (229/4503599627370496), by norm_num⟩
  | 11 => ⟨((-13326162001/18014398509481984), (-57271124851/18014398509481984)), (151/18014398509481984), by norm_num⟩
  | 12 => ⟨((3979546159/36028797018963968), (68410720177/144115188075855872)), (91/72057594037927936), by norm_num⟩
  | 13 => ⟨((-8775864017/576460752303423488), (-4714444449/72057594037927936)), (203/1152921504606846976), by norm_num⟩
  | 14 => ⟨((17970557089/9223372036854775808), (9653886267/1152921504606846976)), (209/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-8586377555/36893488147419103232), (-73802419771/73786976294838206464)), (101/36893488147419103232), by norm_num⟩
  | 16 => ⟨((15384723291/590295810358705651712), (33059046119/295147905179352825856)), (183/590295810358705651712), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (1748337790571/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779582991926541/633825300114114700748351602688), (2070874040009/633825300114114700748351602688)), (1445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890657622236155/39614081257132168796771975168), (1164706209769/19807040628566084398385987584)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890489652597441/2475880078570760549798248448), (2474610148907/2475880078570760549798248448)), (1727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772155588646411/154742504910672534362390528), (309271357385/19342813113834066795298816)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550457687352797/9671406556917033397649408), (2319068517785/9671406556917033397649408)), (405/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259579580013675/604462909807314587353088), (1014359191813/302231454903657293676544)), (709/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944538313888823/37778931862957161709568), (3295792753659/75557863725914323419136)), (9/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1298502344427899/4722366482869645213696), (1235539735457/2361183241434822606848)), (1729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622771202658923/590295810358705651712), (1698245682649/295147905179352825856)), (2377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825127147552383/73786976294838206464), (1060937623775/18446744073709551616)), (743/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912257073247509/4611686018427387904), (2385828879277/4611686018427387904)), (3345/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797880173038841/576460752303423488), (2384228702525/576460752303423488)), (3347/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598065422717925/72057594037927936), (130275062703/4503599627370496)), (2931/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493957348580019/36028797018963968), (6246011999227/36028797018963968)), (4401/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492148571845233/9007199254740992), (3897471477861/4503599627370496)), (1377/2251799813685248), by norm_num⟩
  | 2 => ⟨((2233702802105745/4503599627370496), (15552218659857/4503599627370496)), (11039/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224668395634445/2251799813685248), (2904291354467/281474976710656)), (16615/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197594023458573/2251799813685248), (46093698108387/2251799813685248)), (16731/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197594023458573/2251799813685248), (46093698108387/2251799813685248)), (63823704246139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2143749561394307/2251799813685248), (89968242173639/2251799813685248)), (16671/562949953421312), by norm_num⟩
  | 2 => ⟨((2037289402680317/2251799813685248), (171302420869739/2251799813685248)), (66149/1125899906842624), by norm_num⟩
  | 3 => ⟨((915091023152057/1125899906842624), (154983850949099/1125899906842624)), (4055/35184372088832), by norm_num⟩
  | 4 => ⟨((722419090414009/1125899906842624), (125965309949067/562949953421312)), (246653/1125899906842624), by norm_num⟩
  | 5 => ⟨((25447438875689/70368744177664), (161648018769831/562949953421312)), (213453/562949953421312), by norm_num⟩
  | 6 => ⟨((108816318295849/2251799813685248), (467653998955655/2251799813685248)), (2215727/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-118555032235/2147483648)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-16094336629/268435456)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-405606931767879/2251799813685248), (110429938303491/2251799813685248)), (565375/1125899906842624), by norm_num⟩
  | 1 => ⟨((48173501285/137438953472), (-3278911403/34359738368)), (271/274877906944), by norm_num⟩
  | 2 => ⟨((-46870652533/137438953472), (6380466977/68719476736)), (133/137438953472), by norm_num⟩
  | 3 => ⟨((3800253269/17179869184), (-16554420595/274877906944)), (87/137438953472), by norm_num⟩
  | 4 => ⟨((-59159611241/549755813888), (4026676881/137438953472)), (171/549755813888), by norm_num⟩
  | 5 => ⟨((46047715171/1099511627776), (-25073764511/2199023255552)), (67/549755813888), by norm_num⟩
  | 6 => ⟨((-7467059691/549755813888), (16263764279/4398046511104)), (175/4398046511104), by norm_num⟩
  | 7 => ⟨((66423895937/17592186044416), (-18084470841/17592186044416)), (49/4398046511104), by norm_num⟩
  | 8 => ⟨((-32313733311/35184372088832), (17595377675/70368744177664)), (3/1099511627776), by norm_num⟩
  | 9 => ⟨((55892996981/281474976710656), (-15217343997/281474976710656)), (21/35184372088832), by norm_num⟩
  | 10 => ⟨((-87010200069/2251799813685248), (5922316825/562949953421312)), (263/2251799813685248), by norm_num⟩
  | 11 => ⟨((30784369343/4503599627370496), (-2095326621/1125899906842624)), (47/2251799813685248), by norm_num⟩
  | 12 => ⟨((-39935744491/36028797018963968), (10872846233/36028797018963968)), (245/72057594037927936), by norm_num⟩
  | 13 => ⟨((95644763711/576460752303423488), (-26040100719/576460752303423488)), (37/72057594037927936), by norm_num⟩
  | 14 => ⟨((-106352066519/4611686018427387904), (7238813753/1152921504606846976)), (331/4611686018427387904), by norm_num⟩
  | 15 => ⟨((55187084163/18446744073709551616), (-7512576613/9223372036854775808)), (173/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-107389107169/295147905179352825856), (14618799077/147573952589676412928)), (339/295147905179352825856), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (936505145617/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779369646946305/633825300114114700748351602688), (4436119902045/633825300114114700748351602688)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890417168984685/39614081257132168796771975168), (623733507907/4951760157141521099596496896)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890233605715525/2475880078570760549798248448), (5300823653435/2475880078570760549798248448)), (433/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771898906165201/154742504910672534362390528), (1324949619765/38685626227668133590597632)), (433/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550216372573007/9671406556917033397649408), (4967471835665/9671406556917033397649408)), (1625/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629683877522139/302231454903657293676544), (4345448628017/604462909807314587353088)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888731148330367/75557863725914323419136), (7059311739921/75557863725914323419136)), (2313/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324560532459807/1180591620717411303424), (661587104019/590295810358705651712)), (217/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405602903406949/147573952589676412928), (7274554357121/590295810358705651712)), (597/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824674973207357/73786976294838206464), (9088837344325/73786976294838206464)), (2987/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824001758992745/9223372036854775808), (10218953191095/9223372036854775808)), (3363/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398810837859169/288230376151711744), (10211467368745/1152921504606846976)), (3367/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195673301805085/144115188075855872), (1115826586185/18014398509481984)), (2951/144115188075855872), by norm_num⟩
  | 4 => ⟨((746630355378333/18014398509481984), (417908665037/1125899906842624)), (4435/36028797018963968), by norm_num⟩
  | 3 => ⟨((372814941238555/2251799813685248), (16686875342759/9007199254740992)), (5561/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115935688734225/2251799813685248), (8321336150761/1125899906842624)), (5585/2251799813685248), by norm_num⟩
  | 1 => ⟨((555446873377425/562949953421312), (12426757669819/562949953421312)), (8441/1125899906842624), by norm_num⟩
  | 0 => ⟨((547825430657301/562949953421312), (24632576679223/562949953421312)), (17129/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547825430657301/562949953421312), (24632576679223/562949953421312)), (65341953757857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((532029422545931/562949953421312), (47941568679357/562949953421312)), (17419/562949953421312), by norm_num⟩
  | 2 => ⟨((997448923268675/1125899906842624), (181233340160421/1125899906842624)), (8973/140737488355328), by norm_num⟩
  | 3 => ⟨((854479892126513/1125899906842624), (160556901110629/562949953421312)), (150299/1125899906842624), by norm_num⟩
  | 4 => ⟨((556907242163213/1125899906842624), (974812362679085/2251799813685248)), (156933/562949953421312), by norm_num⟩
  | 5 => ⟨((257859123443327/4503599627370496), (1928697431190383/4503599627370496)), (2328979/4503599627370496), by norm_num⟩
  | 6 => ⟨((-405606931767879/2251799813685248), (110429938303491/2251799813685248)), (565375/1125899906842624), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-16094336629/268435456)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1925775643/1073741824), (-17198755137/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((61106133179517/1125899906842624), (-354146336676979/2251799813685248)), (3330919/4503599627370496), by norm_num⟩
  | 1 => ⟨((-31022126901/274877906944), (89895825723/274877906944)), (425/274877906944), by norm_num⟩
  | 2 => ⟨((32254349695/274877906944), (-2920829913/8589934592)), (445/274877906944), by norm_num⟩
  | 3 => ⟨((-698656611/8589934592), (64786080611/274877906944)), (155/137438953472), by norm_num⟩
  | 4 => ⟨((23245049285/549755813888), (-67359433673/549755813888)), (325/549755813888), by norm_num⟩
  | 5 => ⟨((-19334688449/1099511627776), (28014000921/549755813888)), (17/68719476736), by norm_num⟩
  | 6 => ⟨((26803569571/4398046511104), (-77671303019/4398046511104)), (379/4398046511104), by norm_num⟩
  | 7 => ⟨((-31849403447/17592186044416), (92293105197/17592186044416)), (453/17592186044416), by norm_num⟩
  | 8 => ⟨((33114486303/70368744177664), (-95959058479/70368744177664)), (237/35184372088832), by norm_num⟩
  | 9 => ⟨((-7651070939/70368744177664), (11085625139/35184372088832)), (441/281474976710656), by norm_num⟩
  | 10 => ⟨((12727963799/562949953421312), (-73766110175/1125899906842624)), (369/1125899906842624), by norm_num⟩
  | 11 => ⟨((-19248768483/4503599627370496), (6972377903/562949953421312)), (281/4503599627370496), by norm_num⟩
  | 12 => ⟨((26684459207/36028797018963968), (-77326145365/36028797018963968)), (49/4503599627370496), by norm_num⟩
  | 13 => ⟨((-17073468613/144115188075855872), (49475445825/144115188075855872)), (505/288230376151711744), by norm_num⟩
  | 14 => ⟨((20287588511/1152921504606846976), (-58789312767/1152921504606846976)), (151/576460752303423488), by norm_num⟩
  | 15 => ⟨((-22499655643/9223372036854775808), (65199434227/9223372036854775808)), (337/9223372036854775808), by norm_num⟩
  | 16 => ⟨((23393359309/73786976294838206464), (-67789206013/73786976294838206464)), (11/2305843009213693952), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (-403321974349/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779200572454055/633825300114114700748351602688), (-1910128086331/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890227484764671/39614081257132168796771975168), (-2148553378627/39614081257132168796771975168)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890032734674153/2475880078570760549798248448), (-1141210037871/1237940039285380274899124224)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221462348341843/19342813113834066795298816), (-2281950065131/154742504910672534362390528)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193753694849731/1208925819614629174706176), (-534707228801/2417851639229258349412352)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629602545368553/302231454903657293676544), (-467744039943/151115727451828646838272)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888468313660133/75557863725914323419136), (-1519700323005/37778931862957161709568)), (4605/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649023155433539/2361183241434822606848), (-2278732098335/4722366482869645213696)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811072242347355/295147905179352825856), (-1565963637275/295147905179352825856)), (297/36893488147419103232), by norm_num⟩
  | 8 => ⟨((114021515135823/4611686018427387904), (-1956457978209/36893488147419103232)), (2971/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911817027114069/4611686018427387904), (-4399291356705/9223372036854775808)), (209/288230376151711744), by norm_num⟩
  | 6 => ⟨((3115002145873/2251799813685248), (-1098967422769/288230376151711744)), (6691/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298840613448757/36028797018963968), (-1921269816141/72057594037927936)), (2929/72057594037927936), by norm_num⟩
  | 4 => ⟨((746403329560883/18014398509481984), (-5756124314845/36028797018963968)), (2199/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490713527817179/9007199254740992), (-3590861704673/4503599627370496)), (11009/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115421326296189/2251799813685248), (-14323218798067/4503599627370496)), (22059/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220402965777269/2251799813685248), (-21384495609763/2251799813685248)), (33195/2251799813685248), by norm_num⟩
  | 0 => ⟨((1094581014872711/1125899906842624), (-5296135409259/281474976710656)), (66819/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094581014872711/1125899906842624), (-5296135409259/281474976710656)), (254894265181731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2127469424300803/2251799813685248), (-82381024969465/2251799813685248)), (33109/562949953421312), by norm_num⟩
  | 2 => ⟨((1003494957809663/1125899906842624), (-155664913639251/2251799813685248)), (129969/1125899906842624), by norm_num⟩
  | 3 => ⟨((1778034144832287/2251799813685248), (-277482847268233/2251799813685248)), (15603/70368744177664), by norm_num⟩
  | 4 => ⟨((1369752617846397/2251799813685248), (-438204119255837/2251799813685248)), (911549/2251799813685248), by norm_num⟩
  | 5 => ⟨((747934773654657/2251799813685248), (-266556216877659/1125899906842624)), (365939/562949953421312), by norm_num⟩
  | 6 => ⟨((61106133179517/1125899906842624), (-354146336676979/2251799813685248)), (3330919/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-17198755137/268435456)), (1/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨58,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile058Terms0
