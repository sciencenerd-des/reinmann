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
namespace Reinmann.XiBand97.Tile057Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨57,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78519/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78519/2560))
  have he : value ((69/80), (78519/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-15897303/8388608), (-18090439641/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-51281041719087/2251799813685248), (1338173296957193/9007199254740992)), (441893/140737488355328), by norm_num⟩
  | 1 => ⟨((3438597571/68719476736), (-22432458929/68719476736)), (119/17179869184), by norm_num⟩
  | 2 => ⟨((-3777685547/68719476736), (6161143761/17179869184)), (525/68719476736), by norm_num⟩
  | 3 => ⟨((2766807843/68719476736), (-18049888661/68719476736)), (387/68719476736), by norm_num⟩
  | 4 => ⟨((-3039649097/137438953472), (4957457373/34359738368)), (427/137438953472), by norm_num⟩
  | 5 => ⟨((2671516681/274877906944), (-17428235489/274877906944)), (377/274877906944), by norm_num⟩
  | 6 => ⟨((-3913281407/1099511627776), (3191145613/137438953472)), (555/1099511627776), by norm_num⟩
  | 7 => ⟨((2456673739/2199023255552), (-8013329795/1099511627776)), (175/1099511627776), by norm_num⟩
  | 8 => ⟨((-2698931959/8796093022208), (4401771293/2199023255552)), (387/8796093022208), by norm_num⟩
  | 9 => ⟨((2635626503/35184372088832), (-4298524475/8796093022208)), (95/8796093022208), by norm_num⟩
  | 10 => ⟨((-579106333/35184372088832), (3777929449/35184372088832)), (21/8796093022208), by norm_num⟩
  | 11 => ⟨((925401213/281474976710656), (-12074122817/562949953421312)), (539/1125899906842624), by norm_num⟩
  | 12 => ⟨((-2711085719/4503599627370496), (17686372935/4503599627370496)), (397/4503599627370496), by norm_num⟩
  | 13 => ⟨((458220321/4503599627370496), (-11957210245/18014398509481984)), (539/36028797018963968), by norm_num⟩
  | 14 => ⟨((-2301286745/144115188075855872), (3753239461/36028797018963968)), (341/144115188075855872), by norm_num⟩
  | 15 => ⟨((337096253/144115188075855872), (-4398245327/288230376151711744)), (201/576460752303423488), by norm_num⟩
  | 16 => ⟨((-185169043/576460752303423488), (19327865459/9223372036854775808)), (443/9223372036854775808), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (35066694167/158456325028528675187087900672)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779042083009253/633825300114114700748351602688), (166047616751/39614081257132168796771975168)), (11559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945024554652935/19807040628566084398385987584), (747088656989/9903520314283042199192993792)), (13005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889843111840789/2475880078570760549798248448), (1587256171905/1237940039285380274899124224)), (13821/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110719315795747/9671406556917033397649408), (1586910614539/77371252455336267181195264)), (27/302231454903657293676544), by norm_num⟩
  | 13 => ⟨((387462891284845/2417851639229258349412352), (1487361623839/4835703278458516698824704)), (12963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157381153544075/75557863725914323419136), (650537215307/151115727451828646838272)), (11345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888214816367377/75557863725914323419136), (4227116055991/75557863725914323419136)), (18441/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297855994801291/4722366482869645213696), (3169133548799/4722366482869645213696)), (3459/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621882486710713/590295810358705651712), (4355603646585/590295810358705651712)), (19031/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824016275281035/73786976294838206464), (340098331065/4611686018427387904)), (23801/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911632223566939/4611686018427387904), (3058870723189/4611686018427387904)), (26791/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797255343908453/576460752303423488), (6112708761847/1152921504606846976)), (26811/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195037442301911/144115188075855872), (5342962460747/144115188075855872)), (11741/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492317343575325/36028797018963968), (4001569218615/18014398509481984)), (8817/9007199254740992), by norm_num⟩
  | 3 => ⟨((745049374526457/4503599627370496), (1248020212485/1125899906842624)), (11041/2251799813685248), by norm_num⟩
  | 2 => ⟨((557400935695365/1125899906842624), (19909130712707/4503599627370496)), (44283/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109260698672131/1125899906842624), (29716033916311/2251799813685248)), (133443/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092653567977489/1125899906842624), (29421667620285/1125899906842624)), (134637/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092653567977489/1125899906842624), (29421667620285/1125899906842624)), (513599400046920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2119240223465331/2251799813685248), (114211538364203/2251799813685248)), (33545/140737488355328), by norm_num⟩
  | 2 => ⟨((497172841702239/562949953421312), (214976202248771/2251799813685248)), (532347/1125899906842624), by norm_num⟩
  | 3 => ⟨((433950496080101/562949953421312), (47464401018605/281474976710656)), (2083873/2251799813685248), by norm_num⟩
  | 4 => ⟨((637007089181715/1125899906842624), (585407643943895/2251799813685248)), (978877/562949953421312), by norm_num⟩
  | 5 => ⟨((568616272770541/2251799813685248), (82802391444187/281474976710656)), (808307/281474976710656), by norm_num⟩
  | 6 => ⟨((-51281041719087/2251799813685248), (1338173296957193/9007199254740992)), (441893/140737488355328), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-18090439641/268435456)), (1/134217728), by norm_num⟩, -11, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-533107351/268435456), (-18957905839/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((76758357999669/9007199254740992), (-1233817591763317/9007199254740992)), (6087615/2251799813685248), by norm_num⟩
  | 1 => ⟨((-674219707/34359738368), (21674880937/68719476736)), (215/34359738368), by norm_num⟩
  | 2 => ⟨((1552448247/68719476736), (-24954128869/68719476736)), (249/34359738368), by norm_num⟩
  | 3 => ⟨((-37235877/2147483648), (9576500857/34359738368)), (3/536870912), by norm_num⟩
  | 4 => ⟨((1371820405/137438953472), (-5512677029/34359738368)), (111/34359738368), by norm_num⟩
  | 5 => ⟨((-631746643/137438953472), (20309452719/274877906944)), (411/274877906944), by norm_num⟩
  | 6 => ⟨((969766935/549755813888), (-31176162051/1099511627776)), (317/549755813888), by norm_num⟩
  | 7 => ⟨((-1275983365/2199023255552), (20510218855/2199023255552)), (105/549755813888), by norm_num⟩
  | 8 => ⟨((734515069/4398046511104), (-11806631047/4398046511104)), (243/4398046511104), by norm_num⟩
  | 9 => ⟨((-1503363065/35184372088832), (12082565621/17592186044416)), (125/8796093022208), by norm_num⟩
  | 10 => ⟨((1384648553/140737488355328), (-22256908387/140737488355328)), (231/70368744177664), by norm_num⟩
  | 11 => ⟨((-1159371315/562949953421312), (18635791079/562949953421312)), (389/562949953421312), by norm_num⟩
  | 12 => ⟨((889850369/2251799813685248), (-28606996489/4503599627370496)), (75/562949953421312), by norm_num⟩
  | 13 => ⟨((-157612015/2251799813685248), (20267705745/18014398509481984)), (427/18014398509481984), by norm_num⟩
  | 14 => ⟨((414760087/36028797018963968), (-26667495495/144115188075855872)), (141/36028797018963968), by norm_num⟩
  | 15 => ⟨((-254672105/144115188075855872), (8187223679/288230376151711744)), (87/144115188075855872), by norm_num⟩
  | 16 => ⟨((1172808385/4611686018427387904), (-4712944799/1152921504606846976)), (201/2305843009213693952), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (-245650465365/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111181427788999/39614081257132168796771975168), (-2326056658101/633825300114114700748351602688)), (11555/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889892543811033/39614081257132168796771975168), (-1308177613859/19807040628566084398385987584)), (13001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472419214750065/618970019642690137449562112), (-2779313892021/2475880078570760549798248448)), (13815/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110708931880397/9671406556917033397649408), (-694670018765/38685626227668133590597632)), (6909/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774847961720727/4835703278458516698824704), (-1302169652723/4835703278458516698824704)), (3239/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78682072427703/37778931862957161709568), (-1139061906797/302231454903657293676544)), (2835/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887993922626359/75557863725914323419136), (-3700689570283/75557863725914323419136)), (18431/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297690516186845/4722366482869645213696), (-693603412465/1180591620717411303424)), (3457/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((3167295439241/1152921504606846976), (-3813026277357/590295810358705651712)), (19019/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823732714530397/73786976294838206464), (-297724712951/4611686018427387904)), (23785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455736520531541/2305843009213693952), (-669418963903/1152921504606846976)), (26771/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797096561453059/576460752303423488), (-2675369234307/576460752303423488)), (26789/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597380235905051/72057594037927936), (-4676710604613/144115188075855872)), (5865/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491903682191045/36028797018963968), (-7004705645883/36028797018963968)), (17615/18014398509481984), by norm_num⟩
  | 3 => ⟨((186198100640165/1125899906842624), (-136527749919/140737488355328)), (22053/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228585224076081/4503599627370496), (-4355332822535/1125899906842624)), (88419/4503599627370496), by norm_num⟩
  | 1 => ⟨((554254235007167/562949953421312), (-25996785994275/2251799813685248)), (66575/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182390892841783/2251799813685248), (-51454769865409/2251799813685248)), (268393/2251799813685248), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182390892841783/2251799813685248), (-51454769865409/2251799813685248)), (1023838051802825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((528486411945567/562949953421312), (-99737481515961/2251799813685248)), (532507/2251799813685248), by norm_num⟩
  | 2 => ⟨((990056622586987/1125899906842624), (-46815799008877/562949953421312)), (1046987/2251799813685248), by norm_num⟩
  | 3 => ⟨((215704174473473/281474976710656), (-329338631746907/2251799813685248)), (503867/562949953421312), by norm_num⟩
  | 4 => ⟨((637122950463621/1125899906842624), (-126191888375597/562949953421312)), (3678597/2251799813685248), by norm_num⟩
  | 5 => ⟨((607919196298697/2251799813685248), (-285637285367231/1125899906842624)), (1453121/562949953421312), by norm_num⟩
  | 6 => ⟨((76758357999669/9007199254740992), (-1233817591763317/9007199254740992)), (6087615/2251799813685248), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-18957905839/268435456)), (1/134217728), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-34698381/16777216), (-19742624467/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-157565344996739/4503599627370496), (1094169314907611/9007199254740992)), (24535951/9007199254740992), by norm_num⟩
  | 1 => ⟨((5765154967/68719476736), (-2502158573/8589934592)), (451/68719476736), by norm_num⟩
  | 2 => ⟨((-6912118921/68719476736), (2999957107/8589934592)), (543/68719476736), by norm_num⟩
  | 3 => ⟨((2762422881/34359738368), (-4795721977/17179869184)), (109/17179869184), by norm_num⟩
  | 4 => ⟨((-25875003/536870912), (22999278117/137438953472)), (525/137438953472), by norm_num⟩
  | 5 => ⟨((1588366013/68719476736), (-11029972055/137438953472)), (253/137438953472), by norm_num⟩
  | 6 => ⟨((-5078313805/549755813888), (17632478567/549755813888)), (407/549755813888), by norm_num⟩
  | 7 => ⟨((6958436953/2199023255552), (-1510029893/137438953472)), (35/137438953472), by norm_num⟩
  | 8 => ⟨((-4171400769/4398046511104), (14483574169/4398046511104)), (337/4398046511104), by norm_num⟩
  | 9 => ⟨((2222796041/8796093022208), (-3858899337/4398046511104)), (361/17592186044416), by norm_num⟩
  | 10 => ⟨((-4264025695/70368744177664), (7402589183/35184372088832)), (87/17592186044416), by norm_num⟩
  | 11 => ⟨((3718068021/281474976710656), (-25819103431/562949953421312)), (305/281474976710656), by norm_num⟩
  | 12 => ⟨((-5943691821/2251799813685248), (20637168689/2251799813685248)), (245/1125899906842624), by norm_num⟩
  | 13 => ⟨((2192669311/4503599627370496), (-15226390537/9007199254740992)), (91/2251799813685248), by norm_num⟩
  | 14 => ⟨((-6008904429/72057594037927936), (20863594223/72057594037927936)), (501/72057594037927936), by norm_num⟩
  | 15 => ⟨((3842326273/288230376151711744), (-6670495195/144115188075855872)), (161/144115188075855872), by norm_num⟩
  | 16 => ⟨((-4606748003/2305843009213693952), (15995148895/2305843009213693952)), (97/576460752303423488), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (150713494443/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778774645530313/633825300114114700748351602688), (1426907832531/316912650057057350374175801344)), (11561/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889748263131763/39614081257132168796771975168), (401244432089/4951760157141521099596496896)), (813/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944761742294933/1237940039285380274899124224), (1704928707919/1237940039285380274899124224)), (13823/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442797362514217/38685626227668133590597632), (3409047310499/154742504910672534362390528)), (6913/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774775981884933/4835703278458516698824704), (1597560658519/4835703278458516698824704)), (6483/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258787103322553/604462909807314587353088), (43669856893/9444732965739290427392)), (2837/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943894456161269/37778931862957161709568), (1135013127993/18889465931478580854784)), (9223/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162192076227365/590295810358705651712), (850907208333/1180591620717411303424)), (865/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810721701218479/295147905179352825856), (1169424599587/147573952589676412928)), (9519/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113966720328861/4611686018427387904), (1460921924187/18446744073709551616)), (11905/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822647248517737/9223372036854775808), (3284713835257/4611686018427387904)), (26803/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593893671148879/1152921504606846976), (1640882565107/288230376151711744)), (26825/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597248879049979/72057594037927936), (5736459649903/144115188075855872)), (2937/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491508229759921/36028797018963968), (8591443960517/36028797018963968)), (8823/9007199254740992), by norm_num⟩
  | 3 => ⟨((372272020624635/2251799813685248), (10716154857205/9007199254740992)), (5525/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113792301098047/2251799813685248), (10681488800351/2251799813685248)), (88655/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107749110647207/1125899906842624), (3983943678615/281474976710656)), (66811/1125899906842624), by norm_num⟩
  | 0 => ⟨((2179283241846661/2251799813685248), (31526954331671/1125899906842624)), (269813/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2179283241846661/2251799813685248), (31526954331671/1125899906842624)), (1029254921920012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1053668186655969/1125899906842624), (122046662982945/2251799813685248)), (33585/140737488355328), by norm_num⟩
  | 2 => ⟨((122845378379095/140737488355328), (114216801414681/1125899906842624)), (532011/1125899906842624), by norm_num⟩
  | 3 => ⟨((1692473165308415/2251799813685248), (398785180864151/2251799813685248)), (259173/281474976710656), by norm_num⟩
  | 4 => ⟨((18772731944035/35184372088832), (599461118375933/2251799813685248)), (1925563/1125899906842624), by norm_num⟩
  | 5 => ⟨((240727462570763/1125899906842624), (1279377430153411/4503599627370496)), (3080005/1125899906842624), by norm_num⟩
  | 6 => ⟨((-157565344996739/4503599627370496), (1094169314907611/9007199254740992)), (24535951/9007199254740992), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-19742624467/268435456)), (1/134217728), by norm_num⟩, -12, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-575319455/268435456), (-10229508223/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((361266644096723/4503599627370496), (-12039971149407/140737488355328)), (7660475/4503599627370496), by norm_num⟩
  | 1 => ⟨((-13698026829/68719476736), (14608498229/68719476736)), (293/68719476736), by norm_num⟩
  | 2 => ⟨((8509579489/34359738368), (-4537594299/17179869184)), (23/4294967296), by norm_num⟩
  | 3 => ⟨((-7048503553/34359738368), (469812427/2147483648)), (307/68719476736), by norm_num⟩
  | 4 => ⟨((8757436675/68719476736), (-145930003/1073741824)), (3/1073741824), by norm_num⟩
  | 5 => ⟨((-2176141263/34359738368), (2320783583/34359738368)), (193/137438953472), by norm_num⟩
  | 6 => ⟨((7210010527/274877906944), (-961155093/34359738368)), (161/274877906944), by norm_num⟩
  | 7 => ⟨((-10237830345/1099511627776), (5459155845/549755813888)), (231/1099511627776), by norm_num⟩
  | 8 => ⟨((795001647/274877906944), (-6782746331/2199023255552)), (289/4398046511104), by norm_num⟩
  | 9 => ⟨((-14048034697/17592186044416), (3745442547/4398046511104)), (161/8796093022208), by norm_num⟩
  | 10 => ⟨((6981610967/35184372088832), (-7445660073/35184372088832)), (161/35184372088832), by norm_num⟩
  | 11 => ⟨((-788575069/17592186044416), (13455832893/281474976710656)), (293/281474976710656), by norm_num⟩
  | 12 => ⟨((5225427821/562949953421312), (-11145496211/1125899906842624)), (245/1125899906842624), by norm_num⟩
  | 13 => ⟨((-7990584825/4503599627370496), (17043395477/9007199254740992)), (377/9007199254740992), by norm_num⟩
  | 14 => ⟨((5673102105/18014398509481984), (-1512544527/4503599627370496)), (269/36028797018963968), by norm_num⟩
  | 15 => ⟨((-15036937755/288230376151711744), (16036403001/288230376151711744)), (359/288230376151711744), by norm_num⟩
  | 16 => ⟨((9341346655/1152921504606846976), (-4981120557/576460752303423488)), (7/36028797018963968), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (-1064952494685/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778662469724689/633825300114114700748351602688), (-157521649541/79228162514264337593543950336)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889622287486199/39614081257132168796771975168), (-708714772197/19807040628566084398385987584)), (12985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944694961518685/1237940039285380274899124224), (-1505689663029/2475880078570760549798248448)), (13797/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442764052944435/38685626227668133590597632), (-1505319417051/154742504910672534362390528)), (13799/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387356849038991/2417851639229258349412352), (-352710922459/2417851639229258349412352)), (6469/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629339224851155/302231454903657293676544), (-617047551509/302231454903657293676544)), (5661/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943806496451465/37778931862957161709568), (-2004667725191/75557863725914323419136)), (18401/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162175654017289/590295810358705651712), (-5870532703/18446744073709551616)), (13803/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810631835134793/295147905179352825856), (-2065380875179/590295810358705651712)), (18983/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823244226662143/73786976294838206464), (-2580157100379/73786976294838206464)), (11867/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822397914074487/9223372036854775808), (-2900520932031/9223372036854775808)), (26707/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199205834800131/144115188075855872), (-2897828513307/1152921504606846976)), (26717/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194284268488355/144115188075855872), (-2532574190787/144115188075855872)), (5847/36028797018963968), by norm_num⟩
  | 4 => ⟨((372798310009003/9007199254740992), (-948204448115/9007199254740992)), (35103/36028797018963968), by norm_num⟩
  | 3 => ⟨((372175873369701/2251799813685248), (-4730464154187/9007199254740992)), (10979/2251799813685248), by norm_num⟩
  | 2 => ⟨((2226842748515547/4503599627370496), (-9429326039293/4503599627370496)), (43973/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214453332709429/2251799813685248), (-14065234810547/2251799813685248)), (33051/562949953421312), by norm_num⟩
  | 0 => ⟨((2177462528244213/2251799813685248), (-3477119606737/281474976710656)), (265551/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2177462528244213/2251799813685248), (-3477119606737/281474976710656)), (1012996682173918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2105235665270241/2251799813685248), (-26898652727045/1125899906842624)), (520131/2251799813685248), by norm_num⟩
  | 2 => ⟨((983462879189759/1125899906842624), (-100591540552653/2251799813685248)), (31169/70368744177664), by norm_num⟩
  | 3 => ⟨((1713597388850945/2251799813685248), (-175731511287661/2251799813685248)), (1831565/2251799813685248), by norm_num⟩
  | 4 => ⟨((1290316496768065/2251799813685248), (-267459884356717/2251799813685248)), (3073479/2251799813685248), by norm_num⟩
  | 5 => ⟨((353801848283309/1125899906842624), (-306517390144335/2251799813685248)), (4252415/2251799813685248), by norm_num⟩
  | 6 => ⟨((361266644096723/4503599627370496), (-12039971149407/140737488355328)), (7660475/4503599627370496), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-10229508223/134217728)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-296925695/134217728), (-21118033183/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1954821698122299/18014398509481984), (128766188400341/9007199254740992)), (41401189/18014398509481984), by norm_num⟩
  | 1 => ⟨((9563481633/34359738368), (-1259913453/34359738368)), (407/68719476736), by norm_num⟩
  | 2 => ⟨((-24529846069/68719476736), (1615807101/34359738368)), (131/17179869184), by norm_num⟩
  | 3 => ⟨((1310787769/4294967296), (-1381487795/34359738368)), (225/34359738368), by norm_num⟩
  | 4 => ⟨((-13448416983/68719476736), (442930779/17179869184)), (145/34359738368), by norm_num⟩
  | 5 => ⟨((27595606799/274877906944), (-1817752027/137438953472)), (597/274877906944), by norm_num⟩
  | 6 => ⟨((-2949222247/68719476736), (777073649/137438953472)), (513/549755813888), by norm_num⟩
  | 7 => ⟨((17290527331/1099511627776), (-1138945461/549755813888)), (377/1099511627776), by norm_num⟩
  | 8 => ⟨((-5543665871/1099511627776), (730334357/1099511627776)), (243/2199023255552), by norm_num⟩
  | 9 => ⟨((25278617269/17592186044416), (-3330258915/17592186044416)), (139/4398046511104), by norm_num⟩
  | 10 => ⟨((-50654979/137438953472), (1708389093/35184372088832)), (573/70368744177664), by norm_num⟩
  | 11 => ⟨((24190129959/281474976710656), (-3186859277/281474976710656)), (537/281474976710656), by norm_num⟩
  | 12 => ⟨((-20682152765/1125899906842624), (2724710885/1125899906842624)), (461/1125899906842624), by norm_num⟩
  | 13 => ⟨((4080667265/1125899906842624), (-1075191605/2251799813685248)), (183/2251799813685248), by norm_num⟩
  | 14 => ⟨((-23923896867/36028797018963968), (1575892581/18014398509481984)), (539/36028797018963968), by norm_num⟩
  | 15 => ⟨((4090905593/36028797018963968), (-2155778487/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 16 => ⟨((-1311620709/72057594037927936), (1382365661/576460752303423488)), (477/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (1960824479127/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444636345732645/158456325028528675187087900672), (2320006664939/316912650057057350374175801344)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944744994722339/19807040628566084398385987584), (5218976959257/39614081257132168796771975168)), (6517/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889248600455751/2475880078570760549798248448), (1385977039551/618970019642690137449562112)), (13853/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221364254939089/19342813113834066795298816), (2771248238271/77371252455336267181195264)), (6929/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549293207496661/9671406556917033397649408), (5194590733803/9671406556917033397649408)), (12997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314640033292637/151115727451828646838272), (4543767402151/604462909807314587353088)), (5689/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887419039810427/75557863725914323419136), (3690405479641/37778931862957161709568)), (9249/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162157286397539/590295810358705651712), (1383287252203/1180591620717411303424)), (6941/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202632403816941/73786976294838206464), (7604084561367/590295810358705651712)), (19101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822985088030859/73786976294838206464), (9499114275493/73786976294838206464)), (2987/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455525364066051/2305843009213693952), (2669566972971/2305843009213693952)), (26911/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593344073979877/1152921504606846976), (10667977128471/1152921504606846976)), (13473/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194012591098649/144115188075855872), (4661454072455/72057594037927936)), (23617/144115188075855872), by norm_num⟩
  | 4 => ⟨((745385983948299/18014398509481984), (13961231732849/36028797018963968)), (35505/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488152922285645/9007199254740992), (8705545557109/4503599627370496)), (44519/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112835015328529/2251799813685248), (8675239057541/1125899906842624)), (44727/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106258300264821/1125899906842624), (6468598783575/281474976710656)), (16903/281474976710656), by norm_num⟩
  | 0 => ⟨((1086443057995327/1125899906842624), (25572386648699/562949953421312)), (34329/281474976710656), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086443057995327/1125899906842624), (25572386648699/562949953421312)), (130954743505382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1046045677127157/1125899906842624), (49352418953055/562949953421312)), (69371/281474976710656), by norm_num⟩
  | 2 => ⟨((120400235738043/140737488355328), (183408433335371/1125899906842624)), (564261/1125899906842624), by norm_num⟩
  | 3 => ⟨((1588274790959953/2251799813685248), (627620085251801/2251799813685248)), (1149281/1125899906842624), by norm_num⟩
  | 4 => ⟨((472668535464439/1125899906842624), (442682850245989/1125899906842624)), (282739/140737488355328), by norm_num⟩
  | 5 => ⟨((48756445132243/2251799813685248), (1486755639497483/4503599627370496)), (14711393/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1954821698122299/18014398509481984), (128766188400341/9007199254740992)), (41401189/18014398509481984), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-21118033183/268435456)), (1/134217728), by norm_num⟩, -13, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-611009281/268435456), (-5432046845/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((171109635896939/2251799813685248), (621952243801499/9007199254740992)), (12815041/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6890382977/34359738368), (-6261320601/34359738368)), (65/17179869184), by norm_num⟩
  | 2 => ⟨((4546028925/17179869184), (8261992013/34359738368)), (87/17179869184), by norm_num⟩
  | 3 => ⟨((-3999076985/17179869184), (-14535913719/68719476736)), (309/68719476736), by norm_num⟩
  | 4 => ⟨((10553793429/68719476736), (9590277411/68719476736)), (103/34359738368), by norm_num⟩
  | 5 => ⟨((-5570413181/68719476736), (-5061858379/68719476736)), (219/137438953472), by norm_num⟩
  | 6 => ⟨((4900213245/137438953472), (4452844819/137438953472)), (195/274877906944), by norm_num⟩
  | 7 => ⟨((-14779364207/1099511627776), (-13430071723/1099511627776)), (37/137438953472), by norm_num⟩
  | 8 => ⟨((9750897359/2199023255552), (138448161/34359738368)), (99/1099511627776), by norm_num⟩
  | 9 => ⟨((-2859241905/2199023255552), (-10392821591/8796093022208)), (117/4398046511104), by norm_num⟩
  | 10 => ⟨((6036562645/17592186044416), (5485450399/17592186044416)), (249/35184372088832), by norm_num⟩
  | 11 => ⟨((-11586061741/140737488355328), (-10528304059/140737488355328)), (241/140737488355328), by norm_num⟩
  | 12 => ⟨((1274011715/70368744177664), (2315399833/140737488355328)), (107/281474976710656), by norm_num⟩
  | 13 => ⟨((-517259993/140737488355328), (-7520582031/2251799813685248)), (175/2251799813685248), by norm_num⟩
  | 14 => ⟨((3120180059/4503599627370496), (11341284075/18014398509481984)), (133/9007199254740992), by norm_num⟩
  | 15 => ⟨((-4391644829/36028797018963968), (-7981413031/72057594037927936)), (377/144115188075855872), by norm_num⟩
  | 16 => ⟨((11589802475/576460752303423488), (658231455/36028797018963968)), (125/288230376151711744), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (960810708695/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778457713778577/633825300114114700748351602688), (1136691261901/633825300114114700748351602688)), (2885/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889391990504111/39614081257132168796771975168), (1278524447333/39614081257132168796771975168)), (12983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889145299323189/2475880078570760549798248448), (679058441719/1237940039285380274899124224)), (3449/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885405831606925/77371252455336267181195264), (1357762266735/154742504910672534362390528)), (3449/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774599105847777/4835703278458516698824704), (9941605245/75557863725914323419136)), (1617/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629238996542559/302231454903657293676544), (1113083276131/604462909807314587353088)), (1415/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471821850107233/18889465931478580854784), (1808054667469/75557863725914323419136)), (18397/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324290292137871/1180591620717411303424), (1355423853701/4722366482869645213696)), (1725/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810464147603599/295147905179352825856), (1862705501649/590295810358705651712)), (9489/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911412663080887/36893488147419103232), (1163439711037/36893488147419103232)), (23727/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227740886043003/1152921504606846976), (2615675083105/9223372036854775808)), (6675/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593176398784589/1152921504606846976), (2613097160973/1152921504606846976)), (6677/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193873387444567/144115188075855872), (2283563165651/144115188075855872)), (5845/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490578143819717/36028797018963968), (854889829663/9007199254740992)), (35089/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487936763319447/9007199254740992), (266521451729/562949953421312)), (43895/9007199254740992), by norm_num⟩
  | 2 => ⟨((556328922889821/1125899906842624), (8498442883493/4503599627370496)), (21973/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106089348211859/1125899906842624), (6336157224939/1125899906842624)), (132095/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172976697837577/2251799813685248), (12522389422441/1125899906842624)), (66307/562949953421312), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2172976697837577/2251799813685248), (12522389422441/1125899906842624)), (252941133739280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2096634194436269/2251799813685248), (1510506187697/70368744177664)), (129447/562949953421312), by norm_num⟩
  | 2 => ⟨((1951123066331259/2251799813685248), (45005477375541/1125899906842624)), (61653/140737488355328), by norm_num⟩
  | 3 => ⟨((843498437318389/1125899906842624), (155984070138025/2251799813685248)), (447081/562949953421312), by norm_num⟩
  | 4 => ⟨((78315893350873/140737488355328), (116859694728065/1125899906842624)), (2927301/2251799813685248), by norm_num⟩
  | 5 => ⟨((673026216862673/2251799813685248), (65028667885789/562949953421312)), (3865561/2251799813685248), by norm_num⟩
  | 6 => ⟨((171109635896939/2251799813685248), (621952243801499/9007199254740992)), (12815041/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-5432046845/67108864)), (1/134217728), by norm_num⟩, -13, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-39186431/16777216), (-22296227347/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((333049596648225/18014398509481984), (-1710654533141073/18014398509481984)), (33014861/18014398509481984), by norm_num⟩
  | 1 => ⟨((-860133197/17179869184), (8835865693/34359738368)), (343/68719476736), by norm_num⟩
  | 2 => ⟨((2329283877/34359738368), (-23927967867/68719476736)), (467/68719476736), by norm_num⟩
  | 3 => ⟨((-4205211781/68719476736), (10799689699/34359738368)), (423/68719476736), by norm_num⟩
  | 4 => ⟨((88968161/2147483648), (-7311525465/34359738368)), (9/2147483648), by norm_num⟩
  | 5 => ⟨((-192744197/8589934592), (3959995601/34359738368)), (157/68719476736), by norm_num⟩
  | 6 => ⟨((5567583589/549755813888), (-7149244589/137438953472)), (569/549755813888), by norm_num⟩
  | 7 => ⟨((-134618713/34359738368), (22126300853/1099511627776)), (443/1099511627776), by norm_num⟩
  | 8 => ⟨((1458216931/1099511627776), (-1872472921/274877906944)), (151/1099511627776), by norm_num⟩
  | 9 => ⟨((-3510155247/8796093022208), (4507333929/2199023255552)), (365/8796093022208), by norm_num⟩
  | 10 => ⟨((3802270649/35184372088832), (-4882434621/8796093022208)), (397/35184372088832), by norm_num⟩
  | 11 => ⟨((-3744269017/140737488355328), (4807955657/35184372088832)), (393/140737488355328), by norm_num⟩
  | 12 => ⟨((211243093/35184372088832), (-17360247045/562949953421312)), (89/140737488355328), by norm_num⟩
  | 13 => ⟨((-2816280125/2251799813685248), (7232680077/1125899906842624)), (149/1125899906842624), by norm_num⟩
  | 14 => ⟨((4358073119/18014398509481984), (-5596131639/4503599627370496)), (463/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1573584105/36028797018963968), (8082456219/36028797018963968)), (337/72057594037927936), by norm_num⟩
  | 16 => ⟨((266334047/36028797018963968), (-21887697189/576460752303423488)), (229/288230376151711744), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (-897831876373/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889182145081965/316912650057057350374175801344), (-2124159066159/633825300114114700748351602688)), (361/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889286813676233/39614081257132168796771975168), (-2389191744797/39614081257132168796771975168)), (6499/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472258362026169/618970019642690137449562112), (-2537911296611/2475880078570760549798248448)), (3453/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885349849340059/77371252455336267181195264), (-634307748385/38685626227668133590597632)), (6907/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774546562323113/4835703278458516698824704), (-2377931462891/9671406556917033397649408)), (12953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258385921728855/604462909807314587353088), (-2079967693489/604462909807314587353088)), (1417/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887137559357719/75557863725914323419136), (-3378593666865/75557863725914323419136)), (18425/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297048591005667/4722366482869645213696), (-633190297555/1180591620717411303424)), (27/9223372036854775808), by norm_num⟩
  | 9 => ⟨((810386590907969/295147905179352825856), (-435077945247/73786976294838206464)), (19013/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911315478147203/36893488147419103232), (-4347896629603/73786976294838206464)), (23775/73786976294838206464), by norm_num⟩
  | 7 => ⟨((444752872575/2251799813685248), (-4887422732259/9223372036854775808)), (26759/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398239064540181/288230376151711744), (-4882475867289/1152921504606846976)), (26775/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298419961582377/36028797018963968), (-2133303572069/72057594037927936)), (23447/144115188075855872), by norm_num⟩
  | 4 => ⟨((745143001212247/18014398509481984), (-1597201795109/9007199254740992)), (17603/18014398509481984), by norm_num⟩
  | 3 => ⟨((371892099740541/2251799813685248), (-7966611370987/9007199254740992)), (44071/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224569457440635/4503599627370496), (-15875164059111/4503599627370496)), (88331/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211035781998321/2251799813685248), (-23668067934163/2251799813685248)), (132975/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170597811494881/2251799813685248), (-46760227334195/2251799813685248)), (8371/70368744177664), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2170597811494881/2251799813685248), (-46760227334195/2251799813685248)), (31932831078982331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((522838254957805/562949953421312), (-90148019819309/2251799813685248)), (527551/2251799813685248), by norm_num⟩
  | 2 => ⟨((969364763587737/1125899906842624), (-83724730917519/1125899906842624)), (255541/562949953421312), by norm_num⟩
  | 3 => ⟨((828366898913567/1125899906842624), (-288337545812239/2251799813685248)), (1912125/2251799813685248), by norm_num⟩
  | 4 => ⟨((1182000424887561/2251799813685248), (-106070387435523/562949953421312)), (3303331/2251799813685248), by norm_num⟩
  | 5 => ⟨((1081010988264473/4503599627370496), (-890844681697277/4503599627370496)), (4712747/2251799813685248), by norm_num⟩
  | 6 => ⟨((333049596648225/18014398509481984), (-1710654533141073/18014398509481984)), (33014861/18014398509481984), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-22296227347/268435456)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile057Terms1
