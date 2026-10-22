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
namespace Reinmann.XiBand97.Tile041Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (35053/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (35053/1280))
  have he : value ((69/80), (35053/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-1009507541/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1200142165000141/9007199254740992), (626452296918753/9007199254740992)), (121003855/4503599627370496), by norm_num⟩
  | 1 => ⟨((1257410937/4294967296), (-328172775/2147483648)), (1/16777216), by norm_num⟩
  | 2 => ⟨((-345351777/1073741824), (721069287/4294967296)), (71/1073741824), by norm_num⟩
  | 3 => ⟨((1011753883/4294967296), (-528117053/4294967296)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((-1111525249/8589934592), (145048971/2147483648)), (233/8589934592), by norm_num⟩
  | 5 => ⟨((488454119/8589934592), (-509928263/17179869184)), (207/17179869184), by norm_num⟩
  | 6 => ⟨((-715495597/34359738368), (373475637/34359738368)), (77/17179869184), by norm_num⟩
  | 7 => ⟨((898345435/137438953472), (-234459957/68719476736)), (195/137438953472), by norm_num⟩
  | 8 => ⟨((-986933335/549755813888), (128790295/137438953472)), (27/68719476736), by norm_num⟩
  | 9 => ⟨((60236505/137438953472), (-125769423/549755813888)), (213/2199023255552), by norm_num⟩
  | 10 => ⟨((-847060027/8796093022208), (110537467/2199023255552)), (189/8796093022208), by norm_num⟩
  | 11 => ⟨((676793131/35184372088832), (-353273657/35184372088832)), (305/70368744177664), by norm_num⟩
  | 12 => ⟨((-247844417/70368744177664), (517481041/281474976710656)), (113/140737488355328), by norm_num⟩
  | 13 => ⟨((1340479617/2251799813685248), (-174926471/562949953421312)), (77/562949953421312), by norm_num⟩
  | 14 => ⟨((-841524217/9007199254740992), (109815069/2251799813685248)), (195/9007199254740992), by norm_num⟩
  | 15 => ⟨((986142769/72057594037927936), (-64343565/9007199254740992)), (231/72057594037927936), by norm_num⟩
  | 16 => ⟨((-1083388565/576460752303423488), (282754525/288230376151711744)), (1/2251799813685248), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (866404358719/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222379606851001/79228162514264337593543950336), (1025648284829/158456325028528675187087900672)), (23151/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890042929844225/39614081257132168796771975168), (2307313887149/19807040628566084398385987584)), (104205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944918080851649/1237940039285380274899124224), (2451045788307/1237940039285380274899124224)), (27687/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771501670357941/154742504910672534362390528), (2450511176925/77371252455336267181195264)), (55391/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549844185180501/9671406556917033397649408), (143549141351/302231454903657293676544)), (51947/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629521156103347/302231454903657293676544), (4018240154171/604462909807314587353088)), (90943/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944101359120961/37778931862957161709568), (1631877723721/18889465931478580854784)), (73925/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648923084941171/2361183241434822606848), (1223442565379/1180591620717411303424)), (55473/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810933878871849/295147905179352825856), (1681476850155/147573952589676412928)), (152647/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823996036615125/73786976294838206464), (8402845097337/73786976294838206464)), (23869/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455809792322171/2305843009213693952), (4723480439947/4611686018427387904)), (53755/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594482278397275/1152921504606846976), (9439163288231/1152921504606846976)), (215267/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597504534028509/72057594037927936), (4125249327765/72057594037927936)), (188637/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492267767733423/36028797018963968), (12358217234401/36028797018963968)), (283513/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490024543322005/9007199254740992), (15417110105513/9007199254740992)), (355369/9007199254740992), by norm_num⟩
  | 2 => ⟨((557354695232263/1125899906842624), (1921394105797/281474976710656)), (356837/2251799813685248), by norm_num⟩
  | 1 => ⟨((554538282128165/562949953421312), (22941958938253/1125899906842624)), (67367/140737488355328), by norm_num⟩
  | 0 => ⟨((1092105292967061/1125899906842624), (45425578838643/1125899906842624)), (546319/562949953421312), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092105292967061/1125899906842624), (45425578838643/1125899906842624)), (2084041597606468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((132186538128059/140737488355328), (44062100710973/562949953421312)), (551963/281474976710656), by norm_num⟩
  | 2 => ⟨((493171770225993/562949953421312), (165539874945847/1125899906842624)), (561629/140737488355328), by norm_num⟩
  | 3 => ⟨((839746165576713/1125899906842624), (72510524846721/281474976710656)), (9193445/1125899906842624), by norm_num⟩
  | 4 => ⟨((1103204999680047/2251799813685248), (216326282057327/562949953421312)), (18450391/1125899906842624), by norm_num⟩
  | 5 => ⟨((415941331492243/4503599627370496), (1695726126114317/4503599627370496)), (129033787/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1200142165000141/9007199254740992), (626452296918753/9007199254740992)), (121003855/4503599627370496), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-1009507541/16777216)), (1/16777216), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-33319209/16777216), (-132239385/2097152)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1205098648874101/9007199254740992), (-275563098855781/9007199254740992)), (93681815/4503599627370496), by norm_num⟩
  | 1 => ⟨((-661573931/2147483648), (302556745/4294967296)), (13/268435456), by norm_num⟩
  | 2 => ⟨((47604071/134217728), (-348331325/4294967296)), (121/2147483648), by norm_num⟩
  | 3 => ⟨((-146149899/536870912), (66838543/1073741824)), (47/1073741824), by norm_num⟩
  | 4 => ⟨((1346090315/8589934592), (-153901433/4294967296)), (219/8589934592), by norm_num⟩
  | 5 => ⟨((-1239794997/17179869184), (70874229/4294967296)), (51/4294967296), by norm_num⟩
  | 6 => ⟨((475788913/17179869184), (-54397981/8589934592)), (159/34359738368), by norm_num⟩
  | 7 => ⟨((-626025405/68719476736), (286299383/137438953472)), (211/137438953472), by norm_num⟩
  | 8 => ⟨((720738383/274877906944), (-164807173/274877906944)), (123/274877906944), by norm_num⟩
  | 9 => ⟨((-1475165739/2199023255552), (337317813/2199023255552)), (127/1099511627776), by norm_num⟩
  | 10 => ⟨((42458683/274877906944), (-310681187/8796093022208)), (59/2199023255552), by norm_num⟩
  | 11 => ⟨((-284406489/8796093022208), (130067249/17592186044416)), (25/4398046511104), by norm_num⟩
  | 12 => ⟨((1746320379/281474976710656), (-99830303/70368744177664)), (155/140737488355328), by norm_num⟩
  | 13 => ⟨((-1237246545/1125899906842624), (282914175/1125899906842624)), (111/562949953421312), by norm_num⟩
  | 14 => ⟨((1627923115/9007199254740992), (-186123989/4503599627370496)), (295/9007199254740992), by norm_num⟩
  | 15 => ⟨((-999581733/36028797018963968), (228568705/36028797018963968)), (183/36028797018963968), by norm_num⟩
  | 16 => ⟨((1150810999/288230376151711744), (-131574723/144115188075855872)), (213/288230376151711744), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806918929/10141204801825835211973625643008), (-146413207025/5070602400912917605986812821504)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778905675724267/633825300114114700748351602688), (-346595532135/633825300114114700748351602688)), (46117/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889895889268141/39614081257132168796771975168), (-389852274193/39614081257132168796771975168)), (51883/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118105038854049/154742504910672534362390528), (-414134143949/2475880078570760549798248448)), (220507/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442836726674731/38685626227668133590597632), (-414039793029/154742504910672534362390528)), (220513/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549699918684193/9671406556917033397649408), (-194031044211/4835703278458516698824704)), (206737/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157364612866097/75557863725914323419136), (-84863535983/151115727451828646838272)), (180901/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944000235934427/37778931862957161709568), (-551425212393/75557863725914323419136)), (36747/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648847917361389/2361183241434822606848), (-25837792603/295147905179352825856)), (55123/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((3167311011587/1152921504606846976), (-568164703045/590295810358705651712)), (303193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911871834864387/36893488147419103232), (-354903007411/36893488147419103232)), (47377/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822959764534707/9223372036854775808), (-199495584781/2305843009213693952)), (213213/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398552124924089/288230376151711744), (-398648066185/576460752303423488)), (426469/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597387914362135/72057594037927936), (-696862926803/144115188075855872)), (373209/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491930512131093/36028797018963968), (-521876996945/18014398509481984)), (559909/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489624960860917/9007199254740992), (-1302001251615/9007199254740992)), (700057/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228685301982845/4503599627370496), (-2595946561801/4503599627370496)), (700313/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108608082041571/1125899906842624), (-60528782585/35184372088832)), (2102235/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182983923916155/2251799813685248), (-3833872314887/1125899906842624)), (2104861/1125899906842624), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182983923916155/2251799813685248), (-3833872314887/1125899906842624)), (8029407505515670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2116244964941967/2251799813685248), (-14866830663865/2251799813685248)), (8190813/2251799813685248), by norm_num⟩
  | 2 => ⟨((1988752153620261/2251799813685248), (-13971870565865/1125899906842624)), (15503633/2251799813685248), by norm_num⟩
  | 3 => ⟨((878043032917117/1125899906842624), (-6169861883169/281474976710656)), (867809/70368744177664), by norm_num⟩
  | 4 => ⟨((1368417366129953/2251799813685248), (-76985944596365/2251799813685248)), (22265303/1125899906842624), by norm_num⟩
  | 5 => ⟨((828954350611541/2251799813685248), (-1462009729025/35184372088832)), (28583663/1125899906842624), by norm_num⟩
  | 6 => ⟨((1205098648874101/9007199254740992), (-275563098855781/9007199254740992)), (93681815/4503599627370496), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33319209/16777216), (-132239385/2097152)), (1/8388608), by norm_num⟩, -10, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-550852513/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-16961057983073/140737488355328), (-171891572656721/4503599627370496)), (99412375/4503599627370496), by norm_num⟩
  | 1 => ⟨((155146945/536870912), (196541781/2147483648)), (115/2147483648), by norm_num⟩
  | 2 => ⟨((-186013063/536870912), (-29455413/268435456)), (139/2147483648), by norm_num⟩
  | 3 => ⟨((1189439585/4294967296), (376698643/4294967296)), (7/134217728), by norm_num⟩
  | 4 => ⟨((-1426075779/8589934592), (-112910487/2147483648)), (271/8589934592), by norm_num⟩
  | 5 => ⟨((341958037/4294967296), (433196037/17179869184)), (131/8589934592), by norm_num⟩
  | 6 => ⟨((-1093306081/34359738368), (-173126455/17179869184)), (53/8589934592), by norm_num⟩
  | 7 => ⟨((374519069/34359738368), (474444695/137438953472)), (293/137438953472), by norm_num⟩
  | 8 => ⟨((-898057505/274877906944), (-284417173/274877906944)), (177/274877906944), by norm_num⟩
  | 9 => ⟨((239271983/274877906944), (37889033/137438953472)), (191/1099511627776), by norm_num⟩
  | 10 => ⟨((-917998651/4398046511104), (-145366293/2199023255552)), (185/4398046511104), by norm_num⟩
  | 11 => ⟨((100057483/2199023255552), (253507743/17592186044416)), (325/35184372088832), by norm_num⟩
  | 12 => ⟨((-159951577/17592186044416), (-405256679/140737488355328)), (131/70368744177664), by norm_num⟩
  | 13 => ⟨((944116013/562949953421312), (299004023/562949953421312)), (195/562949953421312), by norm_num⟩
  | 14 => ⟨((-1293652185/4503599627370496), (-51212881/562949953421312)), (135/2251799813685248), by norm_num⟩
  | 15 => ⟨((413605661/9007199254740992), (261980001/18014398509481984)), (175/18014398509481984), by norm_num⟩
  | 16 => ⟨((-991783059/144115188075855872), (-314100303/144115188075855872)), (53/36028797018963968), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-3692752470785/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778768781788927/633825300114114700748351602688), (-8535599549/1237940039285380274899124224)), (46315/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944870667734033/19807040628566084398385987584), (-4915589941929/39614081257132168796771975168)), (104237/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944757846554685/1237940039285380274899124224), (-5221709440663/2475880078570760549798248448)), (1731/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1771181174235683/154742504910672534362390528), (-2610233244995/77371252455336267181195264)), (27705/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774771845451707/4835703278458516698824704), (-4892866858977/9671406556917033397649408)), (25983/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258779350648915/604462909807314587353088), (-4279938205429/604462909807314587353088)), (90979/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29496489865927/1180591620717411303424), (-6952424409685/75557863725914323419136)), (18489/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297525597466719/4722366482869645213696), (-5212152911497/4722366482869645213696)), (110997/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810713447099005/295147905179352825856), (-7163192201565/590295810358705651712)), (152723/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823444843146777/73786976294838206464), (-8948714429735/73786976294838206464)), (11941/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822618920932681/9223372036854775808), (-10060051521169/9223372036854775808)), (215149/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199232729631559/144115188075855872), (-10050989326401/1152921504606846976)), (215413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149308245877641/18014398509481984), (-2196106230689/36028797018963968)), (11799/9007199254740992), by norm_num⟩
  | 4 => ⟨((46607896627605/1125899906842624), (-1644533314273/4503599627370496)), (141885/18014398509481984), by norm_num⟩
  | 3 => ⟨((186125621151367/1125899906842624), (-4102427014707/2251799813685248)), (355755/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113688747195773/2251799813685248), (-16356318498317/2251799813685248)), (178661/1125899906842624), by norm_num⟩
  | 1 => ⟨((17305359596881/17592186044416), (-24401172918715/1125899906842624)), (539907/1125899906842624), by norm_num⟩
  | 0 => ⟨((544514188001929/562949953421312), (-24135073835885/562949953421312)), (1095569/1125899906842624), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544514188001929/562949953421312), (-24135073835885/562949953421312)), (4179264072898482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525647435172403/562949953421312), (-46689372837653/562949953421312)), (1106661/562949953421312), by norm_num⟩
  | 2 => ⟨((486944402253457/562949953421312), (-174382457500999/1125899906842624)), (562557/140737488355328), by norm_num⟩
  | 3 => ⟨((1630784684287467/2251799813685248), (-150838562140821/562949953421312)), (18359517/2251799813685248), by norm_num⟩
  | 4 => ⟨((1019372292020297/2251799813685248), (-109239380625323/281474976710656)), (36431047/2251799813685248), by norm_num⟩
  | 5 => ⟨((244597554527855/4503599627370496), (-1582458222158509/4503599627370496)), (122523221/4503599627370496), by norm_num⟩
  | 6 => ⟨((-16961057983073/140737488355328), (-171891572656721/4503599627370496)), (99412375/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-550852513/8388608)), (1/16777216), by norm_num⟩, -10, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-17978733/8388608), (-570841057/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((511346990770463/9007199254740992), (57769019706349/562949953421312)), (69898533/2251799813685248), by norm_num⟩
  | 1 => ⟨((-302946457/2147483648), (-273801081/1073741824)), (167/2147483648), by norm_num⟩
  | 2 => ⟨((752793665/4294967296), (1360740253/4294967296)), (209/2147483648), by norm_num⟩
  | 3 => ⟨((-623540661/4294967296), (-140888021/536870912)), (349/4294967296), by norm_num⟩
  | 4 => ⟨((96840021/1073741824), (87523395/536870912)), (219/4294967296), by norm_num⟩
  | 5 => ⟨((-385021459/8589934592), (-173989973/2147483648)), (55/2147483648), by norm_num⟩
  | 6 => ⟨((19932133/1073741824), (576465121/17179869184)), (367/34359738368), by norm_num⟩
  | 7 => ⟨((-226420525/34359738368), (-818549721/68719476736)), (131/34359738368), by norm_num⟩
  | 8 => ⟨((140658467/68719476736), (508504911/137438953472)), (41/34359738368), by norm_num⟩
  | 9 => ⟨((-621374507/1099511627776), (-1123188653/1099511627776)), (365/1099511627776), by norm_num⟩
  | 10 => ⟨((308811529/2199023255552), (1116407581/4398046511104)), (365/4398046511104), by norm_num⟩
  | 11 => ⟨((-558085689/17592186044416), (-504394295/8796093022208)), (83/4398046511104), by norm_num⟩
  | 12 => ⟨((462263613/70368744177664), (835581825/70368744177664)), (277/70368744177664), by norm_num⟩
  | 13 => ⟨((-706881185/562949953421312), (-319437359/140737488355328)), (213/281474976710656), by norm_num⟩
  | 14 => ⟨((125466697/562949953421312), (226792005/562949953421312)), (19/140737488355328), by norm_num⟩
  | 15 => ⟨((-665115797/18014398509481984), (-1202254851/18014398509481984)), (203/9007199254740992), by norm_num⟩
  | 16 => ⟨((413187667/72057594037927936), (11669887/1125899906842624)), (127/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790591984073989/5070602400912917605986812821504), (1387908651315/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778661875834957/633825300114114700748351602688), (821165868927/316912650057057350374175801344)), (184723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472405396492875/9903520314283042199192993792), (461819207669/9903520314283042199192993792)), (207835/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944694567026107/1237940039285380274899124224), (1962302491397/2475880078570760549798248448)), (13803/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((221381921719553/19342813113834066795298816), (980909937153/77371252455336267181195264)), (220875/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549426558444277/9671406556917033397649408), (1838693505825/9671406556917033397649408)), (207099/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629338832338199/302231454903657293676544), (804172182441/302231454903657293676544)), (181241/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887611619764769/75557863725914323419136), (2612599112911/75557863725914323419136)), (147285/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297404117079257/4722366482869645213696), (979304641665/2361183241434822606848)), (220975/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25332218730589/9223372036854775808), (2691723372065/590295810358705651712)), (303917/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823241930081503/73786976294838206464), (840652208703/18446744073709551616)), (380011/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911197522984301/4611686018427387904), (3780124503923/9223372036854775808)), (53459/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593643455380529/1152921504606846976), (236038400109/72057594037927936)), (427871/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194281049960559/144115188075855872), (1650296389139/72057594037927936)), (374611/144115188075855872), by norm_num⟩
  | 4 => ⟨((745593808853057/18014398509481984), (4943009615079/36028797018963968)), (140591/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488695080134919/9007199254740992), (3082497743185/4503599627370496)), (175935/2251799813685248), by norm_num⟩
  | 2 => ⟨((2226821785522263/4503599627370496), (12288781973153/4503599627370496)), (1409839/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214411617182191/2251799813685248), (4582616732593/562949953421312)), (2120677/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088669214761793/1125899906842624), (4531500448253/281474976710656)), (2132565/1125899906842624), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088669214761793/1125899906842624), (4531500448253/281474976710656)), (8135089878562545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2104755671490925/2251799813685248), (70106481113787/2251799813685248)), (2096379/562949953421312), by norm_num⟩
  | 2 => ⟨((1965130954841435/2251799813685248), (131056955272615/2251799813685248)), (8099007/1125899906842624), by norm_num⟩
  | 3 => ⟨((1707329275358075/2251799813685248), (57186273417439/562949953421312)), (7539321/562949953421312), by norm_num⟩
  | 4 => ⟨((317817876085063/562949953421312), (86718009443687/562949953421312)), (6482231/281474976710656), by norm_num⟩
  | 5 => ⟨((332136768567697/1125899906842624), (391658738574805/2251799813685248)), (37265055/1125899906842624), by norm_num⟩
  | 6 => ⟨((511346990770463/9007199254740992), (57769019706349/562949953421312)), (69898533/2251799813685248), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17978733/8388608), (-570841057/8388608)), (1/8388608), by norm_num⟩, -11, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-579933/262144), (-1178457471/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((423742856257967/9007199254740992), (-222535766286195/2251799813685248)), (268831523/9007199254740992), by norm_num⟩
  | 1 => ⟨((-259132139/2147483648), (1088701193/4294967296)), (331/4294967296), by norm_num⟩
  | 2 => ⟨((332330407/2147483648), (-1396231713/4294967296)), (427/4294967296), by norm_num⟩
  | 3 => ⟨((-35517111/268435456), (1193754545/4294967296)), (367/4294967296), by norm_num⟩
  | 4 => ⟨((91099591/1073741824), (-191369997/1073741824)), (237/4294967296), by norm_num⟩
  | 5 => ⟨((-93466335/2147483648), (785366961/8589934592)), (245/8589934592), by norm_num⟩
  | 6 => ⟨((639297109/34359738368), (-335737747/8589934592)), (421/34359738368), by norm_num⟩
  | 7 => ⟨((-468504203/68719476736), (984171793/68719476736)), (311/68719476736), by norm_num⟩
  | 8 => ⟨((600844777/274877906944), (-315543851/68719476736)), (401/274877906944), by norm_num⟩
  | 9 => ⟨((-342474761/549755813888), (44964111/34359738368)), (459/1099511627776), by norm_num⟩
  | 10 => ⟨((351372167/2199023255552), (-738116273/2199023255552)), (237/2199023255552), by norm_num⟩
  | 11 => ⟨((-655455865/17592186044416), (1376895171/17592186044416)), (445/17592186044416), by norm_num⟩
  | 12 => ⟨((140100925/17592186044416), (-73576383/4398046511104)), (191/35184372088832), by norm_num⟩
  | 13 => ⟨((-442279111/281474976710656), (464540791/140737488355328)), (303/281474976710656), by norm_num⟩
  | 14 => ⟨((162060503/562949953421312), (-1361741261/2251799813685248)), (447/2251799813685248), by norm_num⟩
  | 15 => ⟨((-221694391/4503599627370496), (931412633/9007199254740992)), (307/9007199254740992), by norm_num⟩
  | 16 => ⟨((284317443/36028797018963968), (-1194513117/72057594037927936)), (99/18014398509481984), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581094039954061/10141204801825835211973625643008), (-1467392757599/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889277649231337/316912650057057350374175801344), (-868094266955/316912650057057350374175801344)), (92371/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472375424968645/9903520314283042199192993792), (-244104324837/4951760157141521099596496896)), (12991/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944630885426799/1237940039285380274899124224), (-1037209244809/1237940039285380274899124224)), (220873/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442732007078539/38685626227668133590597632), (-2073891872011/154742504910672534362390528)), (110451/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549307190959797/9671406556917033397649408), (-121482141991/604462909807314587353088)), (103563/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258573236996851/604462909807314587353088), (-1700190824415/604462909807314587353088)), (90633/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887441960169241/75557863725914323419136), (-2761762071765/75557863725914323419136)), (294613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648638451673513/2361183241434822606848), (-258800618945/590295810358705651712)), (110505/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621087130199863/590295810358705651712), (-2845318104491/590295810358705651712)), (151985/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823023419882049/73786976294838206464), (-3554415929889/73786976294838206464)), (95021/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822149325822915/9223372036854775808), (-3995651533361/9223372036854775808)), (427763/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593397865049289/1152921504606846976), (-1995910923691/576460752303423488)), (427973/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194066304500975/144115188075855872), (-3488540251625/144115188075855872)), (374713/144115188075855872), by norm_num⟩
  | 4 => ⟨((745432895886925/18014398509481984), (-5224213965951/36028797018963968)), (562543/36028797018963968), by norm_num⟩
  | 3 => ⟨((372073327346123/2251799813685248), (-6515249171501/9007199254740992)), (704009/9007199254740992), by norm_num⟩
  | 2 => ⟨((139126236241493/281474976710656), (-12985545063295/4503599627370496)), (705257/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106606225606987/1125899906842624), (-19366289206513/2251799813685248)), (2122029/2251799813685248), by norm_num⟩
  | 0 => ⟨((67967358897277/70368744177664), (-19143294016597/1125899906842624)), (4269205/2251799813685248), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((67967358897277/70368744177664), (-19143294016597/1125899906842624)), (16285724648482512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2100082551263747/2251799813685248), (-73960059973055/2251799813685248)), (8392207/2251799813685248), by norm_num⟩
  | 2 => ⟨((244519772854625/281474976710656), (-8622115879033/140737488355328)), (8102415/1125899906842624), by norm_num⟩
  | 3 => ⟨((845440066938629/1125899906842624), (-239683437970075/2251799813685248)), (470939/35184372088832), by norm_num⟩
  | 4 => ⟨((1244172532423535/2251799813685248), (-179978682483207/1125899906842624)), (51680769/2251799813685248), by norm_num⟩
  | 5 => ⟨((1259788705215595/4503599627370496), (-397769876001389/2251799813685248)), (73632361/2251799813685248), by norm_num⟩
  | 6 => ⟨((423742856257967/9007199254740992), (-222535766286195/2251799813685248)), (268831523/9007199254740992), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-579933/262144), (-1178457471/16777216)), (1/8388608), by norm_num⟩, -11, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2386755/1048576), (-303126533/4194304)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-924718449746909/9007199254740992), (26571306954915/18014398509481984)), (599921939/18014398509481984), by norm_num⟩
  | 1 => ⟨((1163666249/4294967296), (-8359337/2147483648)), (379/4294967296), by norm_num⟩
  | 2 => ⟨((-1535490971/4294967296), (11030385/2147483648)), (503/4294967296), by norm_num⟩
  | 3 => ⟨((1350749567/4294967296), (-9703273/2147483648)), (445/4294967296), by norm_num⟩
  | 4 => ⟨((-445588193/2147483648), (12803747/4294967296)), (589/8589934592), by norm_num⟩
  | 5 => ⟨((940746229/8589934592), (-13515929/8589934592)), (39/1073741824), by norm_num⟩
  | 6 => ⟨((-827561077/17179869184), (23779541/34359738368)), (551/34359738368), by norm_num⟩
  | 7 => ⟨((1247989215/68719476736), (-17930163/68719476736)), (209/34359738368), by norm_num⟩
  | 8 => ⟨((-823378771/137438953472), (5914841/68719476736)), (553/274877906944), by norm_num⟩
  | 9 => ⟨((965752791/549755813888), (-3468801/137438953472)), (651/1099511627776), by norm_num⟩
  | 10 => ⟨((-2038941585/4398046511104), (29293967/4398046511104)), (689/4398046511104), by norm_num⟩
  | 11 => ⟨((978342497/8796093022208), (-28112167/17592186044416)), (83/2199023255552), by norm_num⟩
  | 12 => ⟨((-860633979/35184372088832), (24729873/70368744177664)), (293/35184372088832), by norm_num⟩
  | 13 => ⟨((174712493/35184372088832), (-20081093/281474976710656)), (239/140737488355328), by norm_num⟩
  | 14 => ⟨((-2107777303/2251799813685248), (15141473/1125899906842624)), (723/2251799813685248), by norm_num⟩
  | 15 => ⟨((741672685/4503599627370496), (-21311581/9007199254740992)), (511/9007199254740992), by norm_num⟩
  | 16 => ⟨((-1957316735/72057594037927936), (14060621/36028797018963968)), (169/18014398509481984), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779474461/10141204801825835211973625643008), (509195192881/1267650600228229401496703205376)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778445965491339/633825300114114700748351602688), (4819244590971/633825300114114700748351602688)), (185349/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944689058878171/19807040628566084398385987584), (1355135174121/9903520314283042199192993792)), (104289/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889129697145399/2475880078570760549798248448), (5757983365295/2475880078570760549798248448)), (221685/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770795091685015/154742504910672534362390528), (5756474624973/154742504910672534362390528)), (221765/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774590823336577/4835703278458516698824704), (5395092136603/9671406556917033397649408)), (207989/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629231235143799/302231454903657293676544), (4719103033279/604462909807314587353088)), (182075/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887260249350479/75557863725914323419136), (7665538086285/75557863725914323419136)), (148015/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297139121248801/4722366482869645213696), (2873262635901/2361183241434822606848)), (222161/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810447623451491/295147905179352825856), (7897202224717/590295810358705651712)), (152849/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455694980382571/18446744073709551616), (308284356669/2305843009213693952)), (95615/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821870387701317/9223372036854775808), (1386179365745/1152921504606846976)), (430733/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593112686333557/1152921504606846976), (11078436615981/1152921504606846976)), (107829/288230376151711744), by norm_num⟩
  | 5 => ⟨((149226221203307/18014398509481984), (4840632283789/72057594037927936)), (189029/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490467025336031/36028797018963968), (14497176017677/36028797018963968)), (35525/2251799813685248), by norm_num⟩
  | 3 => ⟨((1487770510424169/9007199254740992), (9039120210279/4503599627370496)), (356401/4503599627370496), by norm_num⟩
  | 2 => ⟨((2172755413749/4398046511104), (18013460011741/2251799813685248)), (358131/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105677421769489/1125899906842624), (26858464220829/1125899906842624)), (135383/140737488355328), by norm_num⟩
  | 0 => ⟨((271315910269075/281474976710656), (26535693265755/562949953421312)), (2200955/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((271315910269075/281474976710656), (26535693265755/562949953421312)), (8395977024558639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043592411219595/1125899906842624), (102311841104371/1125899906842624)), (139079/35184372088832), by norm_num⟩
  | 2 => ⟨((479002352415919/562949953421312), (1481757230171/8796093022208)), (4529603/562949953421312), by norm_num⟩
  | 3 => ⟨((391597967621437/562949953421312), (645527687958025/2251799813685248)), (36937479/2251799813685248), by norm_num⟩
  | 4 => ⟨((904555317761527/2251799813685248), (3508128935233/8796093022208)), (72566605/2251799813685248), by norm_num⟩
  | 5 => ⟨((10365776683911/4503599627370496), (1443048260515795/4503599627370496)), (58091843/1125899906842624), by norm_num⟩
  | 6 => ⟨((-924718449746909/9007199254740992), (26571306954915/18014398509481984)), (599921939/18014398509481984), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2386755/1048576), (-303126533/4194304)), (1/8388608), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-622102339/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((569595878820893/18014398509481984), (1647064510094783/18014398509481984)), (499946225/18014398509481984), by norm_num⟩
  | 1 => ⟨((-91939821/1073741824), (-531713173/2147483648)), (325/4294967296), by norm_num⟩
  | 2 => ⟨((497955301/4294967296), (1439905965/4294967296)), (221/2147483648), by norm_num⟩
  | 3 => ⟨((-28093499/268435456), (-1299779213/4294967296)), (401/4294967296), by norm_num⟩
  | 4 => ⟨((152157211/2147483648), (109995855/536870912)), (137/2147483648), by norm_num⟩
  | 5 => ⟨((-329639493/8589934592), (-953197751/8589934592)), (299/8589934592), by norm_num⟩
  | 6 => ⟨((148780049/8589934592), (860435787/17179869184)), (17/1073741824), by norm_num⟩
  | 7 => ⟨((-460461533/68719476736), (-1331487603/68719476736)), (423/68719476736), by norm_num⟩
  | 8 => ⟨((311738237/137438953472), (450716909/68719476736)), (9/4294967296), by norm_num⟩
  | 9 => ⟨((-187600621/274877906944), (-8476139/4294967296)), (349/549755813888), by norm_num⟩
  | 10 => ⟨((406425519/2199023255552), (293808767/549755813888)), (95/549755813888), by norm_num⟩
  | 11 => ⟨((-25014107/549755813888), (-1157307477/8796093022208)), (47/1099511627776), by norm_num⟩
  | 12 => ⟨((361277107/35184372088832), (130585281/4398046511104)), (171/17592186044416), by norm_num⟩
  | 13 => ⟨((-150516391/70368744177664), (-435238765/70368744177664)), (287/140737488355328), by norm_num⟩
  | 14 => ⟨((465835363/1125899906842624), (1347026771/1125899906842624)), (223/562949953421312), by norm_num⟩
  | 15 => ⟨((-42050185/562949953421312), (-972750965/4503599627370496)), (81/1125899906842624), by norm_num⟩
  | 16 => ⟨((28468503/2251799813685248), (1317129223/36028797018963968)), (441/36028797018963968), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (1612432394681/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889182379163269/316912650057057350374175801344), (1907407711769/633825300114114700748351602688)), (184775/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889287366415763/39614081257132168796771975168), (2145396751895/39614081257132168796771975168)), (207897/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889034069749507/2475880078570760549798248448), (569735227533/618970019642690137449562112)), (220919/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885350179470791/77371252455336267181195264), (142395631809/9671406556917033397649408)), (110475/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387273446160535/2417851639229258349412352), (2135285711127/9671406556917033397649408)), (103587/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258386540192997/604462909807314587353088), (1867726467779/604462909807314587353088)), (181311/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887138641106185/75557863725914323419136), (1516920009945/37778931862957161709568)), (73673/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297049469398037/4722366482869645213696), (1137158481607/2361183241434822606848)), (110537/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810387249240307/295147905179352825856), (390682413337/73786976294838206464)), (304067/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822632765208111/73786976294838206464), (3904236003143/73786976294838206464)), (380217/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821710024960881/9223372036854775808), (4388709498099/9223372036854775808)), (53491/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592958796327557/1152921504606846976), (1096067124691/288230376151711744)), (428159/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596841190320115/72057594037927936), (3831244317585/144115188075855872)), (93725/36028797018963968), by norm_num⟩
  | 4 => ⟨((2910723493759/70368744177664), (5736898987755/36028797018963968)), (281435/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487575021236503/9007199254740992), (3576855762547/4503599627370496)), (176125/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112292976366217/2251799813685248), (3563827451073/1125899906842624)), (44117/140737488355328), by norm_num⟩
  | 1 => ⟨((2211068591964145/2251799813685248), (10626556268605/1125899906842624)), (1062249/1125899906842624), by norm_num⟩
  | 0 => ⟨((542673835561043/562949953421312), (10497348731249/562949953421312)), (4276649/2251799813685248), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542673835561043/562949953421312), (10497348731249/562949953421312)), (16314121254927825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1045864541538849/1125899906842624), (20238518413893/562949953421312)), (8404723/2251799813685248), by norm_num⟩
  | 2 => ⟨((1940126723699203/2251799813685248), (37599698967433/562949953421312)), (16218849/2251799813685248), by norm_num⟩
  | 3 => ⟨((1661547302506223/2251799813685248), (259163999664345/2251799813685248)), (15057253/1125899906842624), by norm_num⟩
  | 4 => ⟨((1196186909410673/2251799813685248), (382461391045489/2251799813685248)), (51373371/2251799813685248), by norm_num⟩
  | 5 => ⟨((570470962293349/2251799813685248), (12698045651727/70368744177664)), (36015851/1125899906842624), by norm_num⟩
  | 6 => ⟨((569595878820893/18014398509481984), (1647064510094783/18014398509481984)), (499946225/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-622102339/8388608)), (1/8388608), by norm_num⟩, -12, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile041Terms1
