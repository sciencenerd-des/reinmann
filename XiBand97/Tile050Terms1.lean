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
namespace Reinmann.XiBand97.Tile050Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨50,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76013/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (76013/2560))
  have he : value ((69/80), (76013/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-15897303/8388608), (-4378267007/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1006846140694087/9007199254740992), (-113126349818981/1125899906842624)), (30702585/9007199254740992), by norm_num⟩
  | 1 => ⟨((16878258407/68719476736), (1896392793/8589934592)), (517/68719476736), by norm_num⟩
  | 2 => ⟨((-1158916381/4294967296), (-4166800853/17179869184)), (143/17179869184), by norm_num⟩
  | 3 => ⟨((13580797629/68719476736), (3051799081/17179869184)), (421/68719476736), by norm_num⟩
  | 4 => ⟨((-14920031165/137438953472), (-3352743973/34359738368)), (465/137438953472), by norm_num⟩
  | 5 => ⟨((3278265917/68719476736), (5893385167/137438953472)), (411/274877906944), by norm_num⟩
  | 6 => ⟨((-4802057629/274877906944), (-8632727155/549755813888)), (303/549755813888), by norm_num⟩
  | 7 => ⟨((12058513193/2199023255552), (10838880157/2199023255552)), (383/2199023255552), by norm_num⟩
  | 8 => ⟨((-13247630777/8796093022208), (-1488465867/1099511627776)), (423/8796093022208), by norm_num⟩
  | 9 => ⟨((12936897749/35184372088832), (2907105587/8796093022208)), (13/1099511627776), by norm_num⟩
  | 10 => ⟨((-11370107875/140737488355328), (-10220102151/140737488355328)), (23/8796093022208), by norm_num⟩
  | 11 => ⟨((1135576385/70368744177664), (4082883569/281474976710656)), (37/70368744177664), by norm_num⟩
  | 12 => ⟨((-1663410895/562949953421312), (-11961349499/4503599627370496)), (109/1125899906842624), by norm_num⟩
  | 13 => ⟨((8996645663/18014398509481984), (8086698799/18014398509481984)), (37/2251799813685248), by norm_num⟩
  | 14 => ⟨((-11295800551/144115188075855872), (-5076655243/72057594037927936)), (373/144115188075855872), by norm_num⟩
  | 15 => ⟨((6618509491/576460752303423488), (371818389/36028797018963968)), (55/144115188075855872), by norm_num⟩
  | 16 => ⟨((-14542351719/9223372036854775808), (-6535748021/4611686018427387904)), (243/4611686018427387904), by norm_num⟩
  | _ => zero

private def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395376794923715/2535301200456458802993406410752), (-3138524689305/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779038474276147/633825300114114700748351602688), (-3715381198265/633825300114114700748351602688)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945022421985621/19807040628566084398385987584), (-4179092666607/39614081257132168796771975168)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472459578636903/618970019642690137449562112), (-2219712838425/1237940039285380274899124224)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221437994636181/19342813113834066795298816), (-2219228965073/77371252455336267181195264)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549846471163263/9671406556917033397649408), (-2080013109013/4835703278458516698824704)), (12981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259044454520117/604462909807314587353088), (-3638995005867/604462909807314587353088)), (11363/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944103232849933/37778931862957161709568), (-5911439839483/75557863725914323419136)), (18471/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297849213201085/4722366482869645213696), (-4431894048279/4722366482869645213696)), (3465/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810936160056727/295147905179352825856), (-1522778866351/147573952589676412928)), (4767/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824002305636091/73786976294838206464), (-1902446787429/18446744073709551616)), (23851/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823246999210705/9223372036854775808), (-8555364948067/9223372036854775808)), (26855/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594491078325779/1152921504606846976), (-8548310626373/1152921504606846976)), (26883/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597508928536585/72057594037927936), (-1867959841271/36028797018963968)), (11777/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492283123972297/36028797018963968), (-11191903391535/36028797018963968)), (17697/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490047528635105/9007199254740992), (-13962152598083/9007199254740992)), (44353/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114738036352557/2251799813685248), (-3480151058951/562949953421312)), (44519/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109133599076601/1125899906842624), (-20777181432575/1125899906842624)), (67195/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092275114788821/1125899906842624), (-20570171077095/562949953421312)), (136059/1125899906842624), by norm_num⟩
  | _ => zero

private def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092275114788821/1125899906842624), (-20570171077095/562949953421312)), (519023899558639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058151254293421/1125899906842624), (-9977923365083/140737488355328)), (273935/1125899906842624), by norm_num⟩
  | 2 => ⟨((988819962677971/1125899906842624), (-75020182947627/562949953421312)), (553747/1125899906842624), by norm_num⟩
  | 3 => ⟨((1696869857412655/2251799813685248), (-527090936247753/2251799813685248)), (1120243/1125899906842624), by norm_num⟩
  | 4 => ⟨((144414616816197/281474976710656), (-397195486205527/1125899906842624)), (4425575/2251799813685248), by norm_num⟩
  | 5 => ⟨((312505666749735/2251799813685248), (-815146477485403/2251799813685248)), (7663719/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1006846140694087/9007199254740992), (-113126349818981/1125899906842624)), (30702585/9007199254740992), by norm_num⟩
  | _ => zero

private def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/8388608), (-4378267007/67108864)), (1/134217728), by norm_num⟩, -10, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-533107351/268435456), (-18352848311/268435456)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((227105977607585/2251799813685248), (838429301865027/9007199254740992)), (1070803/1125899906842624), by norm_num⟩
  | 1 => ⟨((-249352855/1073741824), (-14728964325/68719476736)), (153/68719476736), by norm_num⟩
  | 2 => ⟨((9186498669/34359738368), (4239336711/17179869184)), (45/17179869184), by norm_num⟩
  | 3 => ⟨((-7050898297/34359738368), (-6507622343/34359738368)), (141/68719476736), by norm_num⟩
  | 4 => ⟨((16235293311/137438953472), (7492177099/68719476736)), (165/137438953472), by norm_num⟩
  | 5 => ⟨((-14953257743/274877906944), (-6900550121/137438953472)), (77/137438953472), by norm_num⟩
  | 6 => ⟨((11477049457/549755813888), (10592735895/549755813888)), (121/549755813888), by norm_num⟩
  | 7 => ⟨((-15101075995/2199023255552), (-13937529009/2199023255552)), (81/1099511627776), by norm_num⟩
  | 8 => ⟨((17385756237/8796093022208), (1002885829/549755813888)), (189/8796093022208), by norm_num⟩
  | 9 => ⟨((-4448020349/8796093022208), (-16421190825/35184372088832)), (49/8796093022208), by norm_num⟩
  | 10 => ⟨((8193556279/70368744177664), (15124475681/140737488355328)), (183/140737488355328), by norm_num⟩
  | 11 => ⟨((-857561843/35184372088832), (-12663778997/562949953421312)), (155/562949953421312), by norm_num⟩
  | 12 => ⟨((10531248619/2251799813685248), (2429952395/562949953421312)), (121/2251799813685248), by norm_num⟩
  | 13 => ⟨((-14922520665/18014398509481984), (-6886365737/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 14 => ⟨((9817249609/72057594037927936), (9060824623/72057594037927936)), (29/18014398509481984), by norm_num⟩
  | 15 => ⟨((-12056028055/576460752303423488), (-2781775961/144115188075855872)), (145/576460752303423488), by norm_num⟩
  | 16 => ⟨((1735001905/576460752303423488), (12810551719/4611686018427387904)), (169/4611686018427387904), by norm_num⟩
  | _ => zero

private def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388806884961/10141204801825835211973625643008), (485451198647/5070602400912917605986812821504)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905033266603/633825300114114700748351602688), (1149180596013/633825300114114700748351602688)), (5771/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472473782522491/9903520314283042199192993792), (323150809233/9903520314283042199192993792)), (1623/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889679767811655/2475880078570760549798248448), (1373112712213/2475880078570760549798248448)), (3449/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885672999879339/77371252455336267181195264), (686399905625/77371252455336267181195264)), (6899/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774849506028481/4835703278458516698824704), (80416716377/604462909807314587353088)), (6469/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629458026648909/302231454903657293676544), (562750888283/302231454903657293676544)), (5661/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471999746419455/18889465931478580854784), (1828317643143/75557863725914323419136)), (9199/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297694627813331/4722366482869645213696), (1370693561517/4722366482869645213696)), (6901/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405415357163273/147573952589676412928), (941909493977/295147905179352825856)), (4745/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823741183729527/73786976294838206464), (588361875015/18446744073709551616)), (1483/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822956659671541/9223372036854775808), (661451522201/2305843009213693952)), (13351/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797102505171877/576460752303423488), (2643529987835/1152921504606846976)), (13355/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194772343886877/144115188075855872), (577632661683/36028797018963968)), (11691/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491924423805455/36028797018963968), (3460686080859/36028797018963968)), (17545/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489615848607907/9007199254740992), (2158464721663/4503599627370496)), (21949/9007199254740992), by norm_num⟩
  | 2 => ⟨((557165647997815/1125899906842624), (4303565459597/2251799813685248)), (10987/1125899906842624), by norm_num⟩
  | 1 => ⟨((2217170955337403/2251799813685248), (3211018458857/562949953421312)), (16513/562949953421312), by norm_num⟩
  | 0 => ⟨((2182849349308931/2251799813685248), (25422838595109/2251799813685248)), (8289/140737488355328), by norm_num⟩
  | _ => zero

private def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2182849349308931/2251799813685248), (25422838595109/2251799813685248)), (31620026171636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2115723134934995/2251799813685248), (12322193639873/562949953421312)), (130061/1125899906842624), by norm_num⟩
  | 2 => ⟨((496697683028023/562949953421312), (92620489613993/2251799813685248)), (250097/1125899906842624), by norm_num⟩
  | 3 => ⟨((1749160309088079/2251799813685248), (81720199660025/1125899906842624)), (923803/2251799813685248), by norm_num⟩
  | 4 => ⟨((1346855526111671/2251799813685248), (126957759590657/1125899906842624)), (784647/1125899906842624), by norm_num⟩
  | 5 => ⟨((388477409648853/1125899906842624), (151872967613039/1125899906842624)), (278897/281474976710656), by norm_num⟩
  | 6 => ⟨((227105977607585/2251799813685248), (838429301865027/9007199254740992)), (1070803/1125899906842624), by norm_num⟩
  | _ => zero

private def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-533107351/268435456), (-18352848311/268435456)), (1/268435456), by norm_num⟩, -11, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-34698381/16777216), (-19112521983/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-559690627590349/9007199254740992), (-247898699427895/2251799813685248)), (12723065/4503599627370496), by norm_num⟩
  | 1 => ⟨((10239254075/68719476736), (18140720199/68719476736)), (117/17179869184), by norm_num⟩
  | 2 => ⟨((-11988603/67108864), (-21749773605/68719476736)), (141/17179869184), by norm_num⟩
  | 3 => ⟨((9812450803/68719476736), (17384559771/68719476736)), (453/68719476736), by norm_num⟩
  | 4 => ⟨((-5882307349/68719476736), (-20843176847/137438953472)), (273/68719476736), by norm_num⟩
  | 5 => ⟨((2821031397/68719476736), (19991902093/274877906944)), (263/137438953472), by norm_num⟩
  | 6 => ⟨((-4509691901/274877906944), (-15979495841/549755813888)), (423/549755813888), by norm_num⟩
  | 7 => ⟨((12358593019/2199023255552), (10947759297/1099511627776)), (291/1099511627776), by norm_num⟩
  | 8 => ⟨((-7408652945/4398046511104), (-13125790133/4398046511104)), (351/4398046511104), by norm_num⟩
  | 9 => ⟨((7895632833/17592186044416), (6994282247/8796093022208)), (47/2199023255552), by norm_num⟩
  | 10 => ⟨((-3786580129/35184372088832), (-13417245069/70368744177664)), (363/70368744177664), by norm_num⟩
  | 11 => ⟨((6603507339/281474976710656), (731207921/17592186044416)), (319/281474976710656), by norm_num⟩
  | 12 => ⟨((-10556346021/2251799813685248), (-9351253425/1125899906842624)), (513/2251799813685248), by norm_num⟩
  | 13 => ⟨((7788619145/9007199254740992), (6899485041/4503599627370496)), (381/9007199254740992), by norm_num⟩
  | 14 => ⟨((-10672167445/72057594037927936), (-4726926447/18014398509481984)), (525/72057594037927936), by norm_num⟩
  | 15 => ⟨((3412098649/144115188075855872), (6045159777/144115188075855872)), (169/144115188075855872), by norm_num⟩
  | 16 => ⟨((-8181855221/2305843009213693952), (-14495660053/2305843009213693952)), (407/2305843009213693952), by norm_num⟩
  | _ => zero

private def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581281725653757/10141204801825835211973625643008), (-1357747517595/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778773476764595/633825300114114700748351602688), (-803420330167/158456325028528675187087900672)), (11565/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944873441152091/19807040628566084398385987584), (-1807363949155/19807040628566084398385987584)), (6507/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889521931581501/2475880078570760549798248448), (-1919918516283/1237940039285380274899124224)), (6915/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110699237531787/9671406556917033397649408), (-3838924423423/154742504910672534362390528)), (13833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549550314809927/9671406556917033397649408), (-899505550955/2417851639229258349412352)), (3243/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314696389511883/151115727451828646838272), (-1573650107305/302231454903657293676544)), (5677/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943893104670341/37778931862957161709568), (-2556273030243/37778931862957161709568)), (2307/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297534414817061/4722366482869645213696), (-119775635723/147573952589676412928)), (1731/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810720055991179/295147905179352825856), (-1316886608063/147573952589676412928)), (9525/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823463004213353/73786976294838206464), (-205642572831/2305843009213693952)), (5957/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113915100137143/576460752303423488), (-3698906497723/4611686018427387904)), (26825/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593887325887525/1152921504606846976), (-461947960093/72057594037927936)), (26849/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194491421397199/144115188075855872), (-3229900232225/72057594037927936)), (735/4503599627370496), by norm_num⟩
  | 4 => ⟨((745748579883757/18014398509481984), (-9674772146463/36028797018963968)), (35335/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489071515936245/9007199254740992), (-377105324323/281474976710656)), (5533/1125899906842624), by norm_num⟩
  | 2 => ⟨((556885830016031/1125899906842624), (-24056576975873/4503599627370496)), (88815/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107708029489373/1125899906842624), (-17944939115449/1125899906842624)), (133943/2251799813685248), by norm_num⟩
  | 0 => ⟨((544759689633113/562949953421312), (-71002340840053/2251799813685248)), (270779/2251799813685248), by norm_num⟩
  | _ => zero

private def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544759689633113/562949953421312), (-71002340840053/2251799813685248)), (1032939919478606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2106389986336891/2251799813685248), (-68708084838057/1125899906842624)), (33821/140737488355328), by norm_num⟩
  | 2 => ⟨((1961984162180685/2251799813685248), (-257085058811535/2251799813685248)), (1078431/2251799813685248), by norm_num⟩
  | 3 => ⟨((840058939118585/1125899906842624), (-6999911951765/35184372088832)), (2125513/2251799813685248), by norm_num⟩
  | 4 => ⟨((1164445044289765/2251799813685248), (-668517101089857/2251799813685248)), (4017525/2251799813685248), by norm_num⟩
  | 5 => ⟨((100921176606917/562949953421312), (-1382807513627149/4503599627370496)), (13081041/4503599627370496), by norm_num⟩
  | 6 => ⟨((-559690627590349/9007199254740992), (-247898699427895/2251799813685248)), (12723065/4503599627370496), by norm_num⟩
  | _ => zero

private def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34698381/16777216), (-19112521983/268435456)), (1/134217728), by norm_num⟩, -11, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-575319455/268435456), (-19806049709/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-93227081289877/18014398509481984), (527646045753473/4503599627370496)), (43070019/18014398509481984), by norm_num⟩
  | 1 => ⟨((883715035/68719476736), (-20006579099/68719476736)), (205/34359738368), by norm_num⟩
  | 2 => ⟨((-1097974683/68719476736), (24857240721/68719476736)), (1/134217728), by norm_num⟩
  | 3 => ⟨((56840929/4294967296), (-5147326897/17179869184)), (213/34359738368), by norm_num⟩
  | 4 => ⟨((-282488805/34359738368), (12790626835/68719476736)), (133/34359738368), by norm_num⟩
  | 5 => ⟨((70195831/17179869184), (-12713405471/137438953472)), (531/274877906944), by norm_num⟩
  | 6 => ⟨((-930293799/549755813888), (2632635483/68719476736)), (221/274877906944), by norm_num⟩
  | 7 => ⟨((660483785/1099511627776), (-14952807813/1099511627776)), (315/1099511627776), by norm_num⟩
  | 8 => ⟨((-820620275/4398046511104), (2322270723/549755813888)), (393/4398046511104), by norm_num⟩
  | 9 => ⟨((906295457/17592186044416), (-20517781199/17592186044416)), (109/4398046511104), by norm_num⟩
  | 10 => ⟨((-900823843/70368744177664), (2549238547/8796093022208)), (435/70368744177664), by norm_num⟩
  | 11 => ⟨((813986603/281474976710656), (-18427984923/281474976710656)), (395/281474976710656), by norm_num⟩
  | 12 => ⟨((-1348453815/2251799813685248), (15263940759/1125899906842624)), (657/2251799813685248), by norm_num⟩
  | 13 => ⟨((1031009801/9007199254740992), (-5835302753/2251799813685248)), (505/9007199254740992), by norm_num⟩
  | 14 => ⟨((-182997365/9007199254740992), (8285818637/18014398509481984)), (45/4503599627370496), by norm_num⟩
  | 15 => ⟨((242523397/72057594037927936), (-21962118219/288230376151711744)), (479/288230376151711744), by norm_num⟩
  | 16 => ⟨((-301324001/576460752303423488), (27286906803/2305843009213693952)), (597/2305843009213693952), by norm_num⟩
  | _ => zero

private def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581183968152831/10141204801825835211973625643008), (525909541667/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778660002348531/633825300114114700748351602688), (2489264493617/633825300114114700748351602688)), (2889/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944809686484833/19807040628566084398385987584), (2799894604701/39614081257132168796771975168)), (13003/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889386645117419/2475880078570760549798248448), (2974237228219/2475880078570760549798248448)), (6909/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110690795633165/9671406556917033397649408), (2973505296639/154742504910672534362390528)), (3455/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549423915793985/9671406556917033397649408), (2786883745465/9671406556917033397649408)), (405/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258675188227869/604462909807314587353088), (304718255019/75557863725914323419136)), (11343/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235950911006413/9444732965739290427392), (3959880490643/75557863725914323419136)), (4609/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324350149875803/1180591620717411303424), (2968636141339/4722366482869645213696)), (1729/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621256725788901/590295810358705651712), (4079805003679/590295810358705651712)), (9513/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911617342631715/36893488147419103232), (5096653341407/73786976294838206464)), (1487/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822385998211195/9223372036854775808), (2864735569727/4611686018427387904)), (13391/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398408322002117/288230376151711744), (357759078413/72057594037927936)), (1675/72057594037927936), by norm_num⟩
  | 5 => ⟨((597135448383869/72057594037927936), (5002640908631/144115188075855872)), (23471/144115188075855872), by norm_num⟩
  | 4 => ⟨((372792470370429/9007199254740992), (468250159625/2251799813685248)), (35249/36028797018963968), by norm_num⟩
  | 3 => ⟨((744334269711625/4503599627370496), (9344105783441/9007199254740992)), (44135/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226755655973571/4503599627370496), (18625641243775/4503599627370496)), (88493/4503599627370496), by norm_num⟩
  | 1 => ⟨((34598125358525/35184372088832), (27782462171591/2251799813685248)), (66649/1125899906842624), by norm_num⟩
  | 0 => ⟨((1088473479148525/1125899906842624), (27471738921623/1125899906842624)), (268839/2251799813685248), by norm_num⟩
  | _ => zero

private def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1088473479148525/1125899906842624), (27471738921623/1125899906842624)), (1025539406783293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1051620851173777/1125899906842624), (106234165437083/2251799813685248)), (532925/2251799813685248), by norm_num⟩
  | 2 => ⟨((1959472566687259/2251799813685248), (198451146148459/2251799813685248)), (522909/1125899906842624), by norm_num⟩
  | 3 => ⟨((1687605558494595/2251799813685248), (172688342161797/1125899906842624)), (1002219/1125899906842624), by norm_num⟩
  | 4 => ⟨((1211798424710639/2251799813685248), (517683329305401/2251799813685248)), (904829/562949953421312), by norm_num⟩
  | 5 => ⟨((1066222126313987/4503599627370496), (139294763046581/562949953421312)), (2779795/1125899906842624), by norm_num⟩
  | 6 => ⟨((-93227081289877/18014398509481984), (527646045753473/4503599627370496)), (43070019/18014398509481984), by norm_num⟩
  | _ => zero

private def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-575319455/268435456), (-19806049709/268435456)), (1/134217728), by norm_num⟩, -12, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-296925695/134217728), (-5111008343/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((356702191169901/4503599627370496), (-170104175139081/2251799813685248)), (432785/281474976710656), by norm_num⟩
  | 1 => ⟨((-218134655/1073741824), (6657540813/34359738368)), (273/68719476736), by norm_num⟩
  | 2 => ⟨((8952069491/34359738368), (-8538127515/34359738368)), (177/34359738368), by norm_num⟩
  | 3 => ⟨((-956733537/4294967296), (14599909789/68719476736)), (305/68719476736), by norm_num⟩
  | 4 => ⟨((2453973071/17179869184), (-2340501827/17179869184)), (197/68719476736), by norm_num⟩
  | 5 => ⟨((-10070906643/137438953472), (2401307463/34359738368)), (51/34359738368), by norm_num⟩
  | 6 => ⟨((4305227587/137438953472), (-8212309379/274877906944)), (351/549755813888), by norm_num⟩
  | 7 => ⟨((-3155054495/274877906944), (12036661523/1099511627776)), (65/274877906944), by norm_num⟩
  | 8 => ⟨((16185109999/4398046511104), (-15436713619/4398046511104)), (21/274877906944), by norm_num⟩
  | 9 => ⟨((-4612665277/4398046511104), (8798753039/8796093022208)), (97/4398046511104), by norm_num⟩
  | 10 => ⟨((9465002271/35184372088832), (-9027342381/35184372088832)), (201/35184372088832), by norm_num⟩
  | 11 => ⟨((-2207022863/35184372088832), (2104970549/35184372088832)), (189/140737488355328), by norm_num⟩
  | 12 => ⟨((15095738331/1125899906842624), (-14397714285/1125899906842624)), (163/562949953421312), by norm_num⟩
  | 13 => ⟨((-2978446487/1125899906842624), (5681447385/2251799813685248)), (259/4503599627370496), by norm_num⟩
  | 14 => ⟨((4365465373/9007199254740992), (-16654428365/36028797018963968)), (191/18014398509481984), by norm_num⟩
  | 15 => ⟨((-2985919361/36028797018963968), (11391404089/144115188075855872)), (33/18014398509481984), by norm_num⟩
  | 16 => ⟨((15317463893/1152921504606846976), (-14609187299/1152921504606846976)), (341/1152921504606846976), by norm_num⟩
  | _ => zero

private def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790547019981883/5070602400912917605986812821504), (-992245531735/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444639043659097/158456325028528675187087900672), (-587002118595/316912650057057350374175801344)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944751367325757/19807040628566084398385987584), (-660250076591/19807040628566084398385987584)), (1623/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889262934644915/2475880078570760549798248448), (-1402714845149/2475880078570760549798248448)), (3449/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770929264422911/154742504910672534362390528), (-43823713875/4835703278458516698824704)), (6899/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549308426596947/9671406556917033397649408), (-1314333287937/9671406556917033397649408)), (1617/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629287197452959/302231454903657293676544), (-287415909233/151115727451828646838272)), (11321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943721992754631/37778931862957161709568), (-233436871563/9444732965739290427392)), (9199/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162159818499773/590295810358705651712), (-1400001640185/4722366482869645213696)), (13801/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621089595537079/590295810358705651712), (-480998993269/147573952589676412928)), (18979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823026807058825/73786976294838206464), (-2403486505455/73786976294838206464)), (23729/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822153555804941/9223372036854775808), (-2701849747685/9223372036854775808)), (13351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398350654575097/288230376151711744), (-2699261376249/1152921504606846976)), (26711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597035525456305/72057594037927936), (-1179472501929/72057594037927936)), (23383/144115188075855872), by norm_num⟩
  | 4 => ⟨((372718520657303/9007199254740992), (-441576017445/4503599627370496)), (35093/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488305714995691/9007199254740992), (-4405611835705/9007199254740992)), (21951/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226050686797357/4503599627370496), (-8780850736631/4503599627370496)), (21977/1125899906842624), by norm_num⟩
  | 1 => ⟨((2213273944809849/2251799813685248), (-6547797740969/1125899906842624)), (4129/70368744177664), by norm_num⟩
  | 0 => ⟨((1087569185574379/1125899906842624), (-25889974195603/2251799813685248)), (66331/562949953421312), by norm_num⟩
  | _ => zero

private def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1087569185574379/1125899906842624), (-25889974195603/2251799813685248)), (253032686473655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2100789161687465/2251799813685248), (-6252140616437/281474976710656)), (129671/562949953421312), by norm_num⟩
  | 2 => ⟨((979397316375665/1125899906842624), (-2916429152479/70368744177664)), (990843/2251799813685248), by norm_num⟩
  | 3 => ⟨((425011883562249/562949953421312), (-162364295041339/2251799813685248)), (225745/281474976710656), by norm_num⟩
  | 4 => ⟨((1271782436874345/2251799813685248), (-245161241916407/2251799813685248)), (2987337/2251799813685248), by norm_num⟩
  | 5 => ⟨((1383183818330071/4503599627370496), (-138463357078495/1125899906842624)), (8049779/4503599627370496), by norm_num⟩
  | 6 => ⟨((356702191169901/4503599627370496), (-170104175139081/2251799813685248)), (432785/281474976710656), by norm_num⟩
  | _ => zero

private def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-296925695/134217728), (-5111008343/67108864)), (1/134217728), by norm_num⟩, -12, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-611009281/268435456), (-164333703/2097152)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-113746426779797/1125899906842624), (-330046898408673/18014398509481984)), (19690037/9007199254740992), by norm_num⟩
  | 1 => ⟨((18321737141/68719476736), (3322649713/68719476736)), (199/34359738368), by norm_num⟩
  | 2 => ⟨((-24176057347/68719476736), (-4384331539/68719476736)), (33/4294967296), by norm_num⟩
  | 3 => ⟨((21267333781/68719476736), (1928417047/34359738368)), (467/68719476736), by norm_num⟩
  | 4 => ⟨((-7015714137/34359738368), (-2544601571/68719476736)), (619/137438953472), by norm_num⟩
  | 5 => ⟨((14811897453/137438953472), (2686139771/137438953472)), (329/137438953472), by norm_num⟩
  | 6 => ⟨((-13029815513/274877906944), (-4725917901/549755813888)), (581/549755813888), by norm_num⟩
  | 7 => ⟨((2456173581/137438953472), (3563419507/1099511627776)), (55/137438953472), by norm_num⟩
  | 8 => ⟨((-25927931567/4398046511104), (-587754273/549755813888)), (583/4398046511104), by norm_num⟩
  | 9 => ⟨((15205621743/8796093022208), (86173179/274877906944)), (43/1099511627776), by norm_num⟩
  | 10 => ⟨((-16051403005/35184372088832), (-727731071/8796093022208)), (365/35184372088832), by norm_num⟩
  | 11 => ⟨((15403844637/140737488355328), (2793489479/140737488355328)), (11/4398046511104), by norm_num⟩
  | 12 => ⟨((-13550543031/562949953421312), (-4914785923/1125899906842624)), (311/562949953421312), by norm_num⟩
  | 13 => ⟨((11003279971/2251799813685248), (1995446433/2251799813685248)), (507/4503599627370496), by norm_num⟩
  | 14 => ⟨((-16593306661/18014398509481984), (-3009198591/18014398509481984)), (3/140737488355328), by norm_num⟩
  | 15 => ⟨((23355033369/144115188075855872), (4235438719/144115188075855872)), (543/144115188075855872), by norm_num⟩
  | 16 => ⟨((-15408817999/576460752303423488), (-2794391399/576460752303423488)), (45/72057594037927936), by norm_num⟩
  | _ => zero

private def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581010779469609/10141204801825835211973625643008), (-964646533819/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444611810969851/158456325028528675187087900672), (-2282458502787/316912650057057350374175801344)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889379627317539/39614081257132168796771975168), (-320905275709/2475880078570760549798248448)), (13033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944565697442309/1237940039285380274899124224), (-2727059883665/1237940039285380274899124224)), (3463/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110674805931417/9671406556917033397649408), (-681586398893/19342813113834066795298816)), (13857/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774591724590863/4835703278458516698824704), (-5110380364023/9671406556917033397649408)), (3249/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258464159386073/604462909807314587353088), (-4470065454031/604462909807314587353088)), (711/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887263203766411/75557863725914323419136), (-1815252966013/18889465931478580854784)), (18495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648570760149877/2361183241434822606848), (-2721635260877/2361183241434822606848)), (1735/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620898843008975/590295810358705651712), (-1870113601781/147573952589676412928)), (9549/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911392431081325/36893488147419103232), (-9344506009927/73786976294838206464)), (5973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821876557473695/9223372036854775808), (-10504237008491/9223372036854775808)), (13453/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593119619055961/1152921504606846976), (-10493826192729/1152921504606846976)), (26941/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193816692014617/144115188075855872), (-9170391948577/144115188075855872)), (5903/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490479116277803/36028797018963968), (-13732191507007/36028797018963968)), (4437/4503599627370496), by norm_num⟩
  | 3 => ⟨((1487788600398885/9007199254740992), (-2140541333503/1125899906842624)), (44505/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112473303126313/2251799813685248), (-4265759455909/562949953421312)), (22355/1125899906842624), by norm_num⟩
  | 1 => ⟨((552861120571279/562949953421312), (-12720785672561/562949953421312)), (67579/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085396885631647/1125899906842624), (-12568172187725/281474976710656)), (137217/1125899906842624), by norm_num⟩
  | _ => zero

private def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1085396885631647/1125899906842624), (-12568172187725/281474976710656)), (523441318992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((65256636544699/70368744177664), (-12116045900469/140737488355328)), (17301/70368744177664), by norm_num⟩
  | 2 => ⟨((119988754109425/140737488355328), (-179773543024065/1125899906842624)), (561075/1125899906842624), by norm_num⟩
  | 3 => ⟨((1579374399162649/2251799813685248), (-306539553908105/1125899906842624)), (2271777/2251799813685248), by norm_num⟩
  | 4 => ⟨((470414263162779/1125899906842624), (-860006685906711/2251799813685248)), (4423809/2251799813685248), by norm_num⟩
  | 5 => ⟨((32317885288719/1125899906842624), (-1437283755002273/4503599627370496)), (7075719/2251799813685248), by norm_num⟩
  | 6 => ⟨((-113746426779797/1125899906842624), (-330046898408673/18014398509481984)), (19690037/9007199254740992), by norm_num⟩
  | _ => zero

private def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-611009281/268435456), (-164333703/2097152)), (1/134217728), by norm_num⟩, -12, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-39186431/16777216), (-21584624477/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((512326197711275/18014398509481984), (416441985209393/4503599627370496)), (15846823/9007199254740992), by norm_num⟩
  | 1 => ⟨((-5292530299/68719476736), (-17208035305/68719476736)), (329/68719476736), by norm_num⟩
  | 2 => ⟨((3583109435/34359738368), (11650055867/34359738368)), (7/1073741824), by norm_num⟩
  | 3 => ⟨((-6468826817/68719476736), (-21032624089/68719476736)), (407/68719476736), by norm_num⟩
  | 4 => ⟨((4379476941/68719476736), (14239350473/68719476736)), (139/34359738368), by norm_num⟩
  | 5 => ⟨((-1185984341/34359738368), (-15424350365/137438953472)), (303/137438953472), by norm_num⟩
  | 6 => ⟨((4282273511/274877906944), (3480826259/68719476736)), (275/274877906944), by norm_num⟩
  | 7 => ⟨((-828329403/137438953472), (-10772859715/549755813888)), (107/274877906944), by norm_num⟩
  | 8 => ⟨((4486315213/2199023255552), (14586722459/2199023255552)), (73/549755813888), by norm_num⟩
  | 9 => ⟨((-5399629695/8796093022208), (-8778128153/4398046511104)), (177/4398046511104), by norm_num⟩
  | 10 => ⟨((365561707/2199023255552), (2377161171/4398046511104)), (193/17592186044416), by norm_num⟩
  | 11 => ⟨((-5759764097/140737488355328), (-18727190653/140737488355328)), (191/70368744177664), by norm_num⟩
  | 12 => ⟨((324952715/35184372088832), (8452362069/281474976710656)), (347/562949953421312), by norm_num⟩
  | 13 => ⟨((-4332249921/2251799813685248), (-1760724677/281474976710656)), (291/2251799813685248), by norm_num⟩
  | 14 => ⟨((6703971583/18014398509481984), (21797169443/18014398509481984)), (453/18014398509481984), by norm_num⟩
  | 15 => ⟨((-1210312773/18014398509481984), (-15740754425/72057594037927936)), (329/72057594037927936), by norm_num⟩
  | 16 => ⟨((6555175497/576460752303423488), (21313376593/576460752303423488)), (7/9007199254740992), by norm_num⟩
  | _ => zero

private def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580933265800919/10141204801825835211973625643008), (828732495675/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778364647932353/633825300114114700748351602688), (1960678486067/633825300114114700748351602688)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889287236078079/39614081257132168796771975168), (2205314033237/39614081257132168796771975168)), (12995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889033923163711/2475880078570760549798248448), (2342587836687/2475880078570760549798248448)), (13809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442675050812465/38685626227668133590597632), (146372497293/9671406556917033397649408)), (13811/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774546814506515/4835703278458516698824704), (274365068973/1208925819614629174706176)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258386394357205/604462909807314587353088), (1919888816961/604462909807314587353088)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887138386026481/75557863725914323419136), (1559284921321/37778931862957161709568)), (18421/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324262315567583/1180591620717411303424), (2337834596011/4722366482869645213696)), (13819/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810387094003445/295147905179352825856), (803186938589/147573952589676412928)), (19007/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822632338660465/73786976294838206464), (2006637076435/36893488147419103232)), (23767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455427373076615/2305843009213693952), (2255638955995/4611686018427387904)), (13375/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592958197819543/1152921504606846976), (2253356310215/576460752303423488)), (26765/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596840891520693/72057594037927936), (3938243216903/144115188075855872)), (5859/36028797018963968), by norm_num⟩
  | 4 => ⟨((745144692524633/18014398509481984), (2948559113201/18014398509481984)), (17593/18014398509481984), by norm_num⟩
  | 3 => ⟨((743786729840635/4503599627370496), (1838374453497/2251799813685248)), (22021/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224582063082941/4503599627370496), (14653421837345/4503599627370496)), (88259/4503599627370496), by norm_num⟩
  | 1 => ⟨((552765213811659/562949953421312), (21846638787097/2251799813685248)), (66415/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085336172030701/1125899906842624), (21580968778583/1125899906842624)), (133717/1125899906842624), by norm_num⟩
  | _ => zero

private def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1085336172030701/1125899906842624), (21580968778583/1125899906842624)), (510089878562545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((32681881315245/35184372088832), (83213812881629/2251799813685248)), (525851/2251799813685248), by norm_num⟩
  | 2 => ⟨((969898615138721/1125899906842624), (77295224980003/1125899906842624)), (507883/1125899906842624), by norm_num⟩
  | 3 => ⟨((1660411846848041/2251799813685248), (33292715990703/281474976710656)), (1889519/2251799813685248), by norm_num⟩
  | 4 => ⟨((1192836756089351/2251799813685248), (392785324583475/2251799813685248)), (3233537/2251799813685248), by norm_num⟩
  | 5 => ⟨((140840585357529/562949953421312), (26008571541761/140737488355328)), (284615/140737488355328), by norm_num⟩
  | 6 => ⟨((512326197711275/18014398509481984), (416441985209393/4503599627370496)), (15846823/9007199254740992), by norm_num⟩
  | _ => zero

private def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39186431/16777216), (-21584624477/268435456)), (1/134217728), by norm_num⟩, -13, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 16 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 16 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 16 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 16 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 16 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 16 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiBand97.Tile050Terms1
