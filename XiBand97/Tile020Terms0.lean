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
namespace Reinmann.XiBand97.Tile020Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (27893/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (27893/1280))
  have he : value ((69/80), (27893/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-2027312047/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-509923003201861/1125899906842624), (-702683322453521/2251799813685248)), (54800069/2251799813685248), by norm_num⟩
  | 1 => ⟨((674155601/2147483648), (464499439/2147483648)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((-233644527/2147483648), (-643932953/8589934592)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((431866787/17179869184), (297560207/17179869184)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((-1197388983/274877906944), (-412506037/137438953472)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((331986719/549755813888), (228741917/549755813888)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((-1227283511/17592186044416), (-845609679/17592186044416)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((486107489/70368744177664), (669865103/140737488355328)), (69/140737488355328), by norm_num⟩
  | 8 => ⟨((-673888071/1125899906842624), (-116078777/281474976710656)), (25/562949953421312), by norm_num⟩
  | 9 => ⟨((830406429/18014398509481984), (572157703/18014398509481984)), (63/18014398509481984), by norm_num⟩
  | 10 => ⟨((-115118775/36028797018963968), (-317271599/144115188075855872)), (9/36028797018963968), by norm_num⟩
  | 11 => ⟨((928514959/4611686018427387904), (639755387/4611686018427387904)), (75/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-858130035/73786976294838206464), (-147814881/18446744073709551616)), (71/73786976294838206464), by norm_num⟩
  | 13 => ⟨((183018589/295147905179352825856), (126101499/295147905179352825856)), (31/590295810358705651712), by norm_num⟩
  | 14 => ⟨((-1159852059/37778931862957161709568), (-399574393/18889465931478580854784)), (25/9444732965739290427392), by norm_num⟩
  | 15 => ⟨((428772365/302231454903657293676544), (590856243/604462909807314587353088)), (19/151115727451828646838272), by norm_num⟩
  | 16 => ⟨((-74300589/1208925819614629174706176), (-409550339/9671406556917033397649408)), (27/4835703278458516698824704), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1653197323271/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781040228048639/633825300114114700748351602688), (-3922482913979/633825300114114700748351602688)), (23147/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892296490694495/39614081257132168796771975168), (-4412535047863/39614081257132168796771975168)), (13023/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473057580370789/618970019642690137449562112), (-2344014938925/1237940039285380274899124224)), (27681/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443473887522073/38685626227668133590597632), (-4687705016775/154742504910672534362390528)), (13845/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((97005509351493/604462909807314587353088), (-1098594533057/2417851639229258349412352)), (25967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157625685376041/75557863725914323419136), (-1922367684601/302231454903657293676544)), (11365/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891392311282863/75557863725914323419136), (-6247046796241/75557863725914323419136)), (4619/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((325059468622751/1180591620717411303424), (-2342358784103/2361183241434822606848)), (27729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406288888482137/147573952589676412928), (-6440563723443/590295810358705651712)), (38149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828104583406095/73786976294838206464), (-8049319033845/73786976294838206464)), (47721/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456964908347393/2305843009213693952), (-9053576701905/9223372036854775808)), (13433/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399775168482869/288230376151711744), (-70712419655/9007199254740992)), (53791/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599523915234251/72057594037927936), (-1979275389849/36028797018963968)), (23567/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498321227667939/36028797018963968), (-5935131630283/18014398509481984)), (70833/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497583135177225/9007199254740992), (-14828375283467/9007199254740992)), (88773/9007199254740992), by norm_num⟩
  | 2 => ⟨((280563889937019/562949953421312), (-1851768608513/281474976710656)), (44561/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120364507497149/1125899906842624), (-22185497591401/1125899906842624)), (134557/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114554420492945/1125899906842624), (-11056784321557/281474976710656)), (272615/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114554420492945/1125899906842624), (-11056784321557/281474976710656)), (1039943699363326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1101585948297971/1125899906842624), (-21890734277769/281474976710656)), (561155/1125899906842624), by norm_num⟩
  | 2 => ⟨((267746787748107/281474976710656), (-171344007628101/1125899906842624)), (592679/562949953421312), by norm_num⟩
  | 3 => ⟨((992676792891007/1125899906842624), (-325974324101077/1125899906842624)), (2615877/1125899906842624), by norm_num⟩
  | 4 => ⟨((195210060376643/281474976710656), (-287403120514425/562949953421312)), (3063709/562949953421312), by norm_num⟩
  | 5 => ⟨((248076464286773/1125899906842624), (-199321378986129/281474976710656)), (29511017/2251799813685248), by norm_num⟩
  | 6 => ⟨((-509923003201861/1125899906842624), (-702683322453521/2251799813685248)), (54800069/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-2027312047/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-803303393/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((322483851970771/2251799813685248), (811250723713473/2251799813685248)), (60082151/2251799813685248), by norm_num⟩
  | 1 => ⟨((-337872241/2147483648), (-106245281/268435456)), (65/2147483648), by norm_num⟩
  | 2 => ⟨((92797649/1073741824), (933778971/4294967296)), (73/4294967296), by norm_num⟩
  | 3 => ⟨((-543726067/17179869184), (-1367814737/17179869184)), (109/17179869184), by norm_num⟩
  | 4 => ⟨((597344139/68719476736), (1502698079/68719476736)), (61/34359738368), by norm_num⟩
  | 5 => ⟨((-524999689/274877906944), (-1320706061/274877906944)), (55/137438953472), by norm_num⟩
  | 6 => ⟨((384514073/1099511627776), (967295939/1099511627776)), (83/1099511627776), by norm_num⟩
  | 7 => ⟨((-241389649/4398046511104), (-303623773/2199023255552)), (53/4398046511104), by norm_num⟩
  | 8 => ⟨((265193635/35184372088832), (1334259233/70368744177664)), (119/70368744177664), by norm_num⟩
  | 9 => ⟨((-258973321/281474976710656), (-1302963191/562949953421312)), (119/562949953421312), by norm_num⟩
  | 10 => ⟨((455218037/4503599627370496), (1145161099/4503599627370496)), (107/4503599627370496), by norm_num⟩
  | 11 => ⟨((-363715003/36028797018963968), (-228743283/9007199254740992)), (11/4503599627370496), by norm_num⟩
  | 12 => ⟨((33298481/36028797018963968), (335066909/144115188075855872)), (131/576460752303423488), by norm_num⟩
  | 13 => ⟨((-180096593/2305843009213693952), (-1769753/9007199254740992)), (91/4611686018427387904), by norm_num⟩
  | 14 => ⟨((452243041/73786976294838206464), (71104819/4611686018427387904)), (117/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-529962413/1180591620717411303424), (-666595225/590295810358705651712)), (35/295147905179352825856), by norm_num⟩
  | 16 => ⟨((145555805/4722366482869645213696), (366164853/4722366482869645213696)), (157/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (776639559185/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890253173796369/316912650057057350374175801344), (460411078871/158456325028528675187087900672)), (46191/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891696307217455/39614081257132168796771975168), (2071672073825/39614081257132168796771975168)), (51971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891593150299707/2475880078570760549798248448), (1100469232387/1237940039285380274899124224)), (27613/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886629484047015/77371252455336267181195264), (1100349361957/77371252455336267181195264)), (55233/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193936497490351/1208925819614629174706176), (2062900346557/9671406556917033397649408)), (51789/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315121115082913/151115727451828646838272), (1804783115865/604462909807314587353088)), (11331/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890546822603301/75557863725914323419136), (183268441651/4722366482869645213696)), (73665/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81225299017371/295147905179352825856), (2198803532025/4722366482869645213696)), (27631/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406071680547817/147573952589676412928), (3022676062595/590295810358705651712)), (76007/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913510521973187/36893488147419103232), (3777327025135/73786976294838206464)), (1485/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1826644088074185/9223372036854775808), (4248093304265/9223372036854775808)), (106965/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798944711256579/576460752303423488), (2123172070837/576460752303423488)), (26755/288230376151711744), by norm_num⟩
  | 5 => ⟨((299498203400079/36028797018963968), (3713583778539/144115188075855872)), (93705/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496748352322595/36028797018963968), (1391610533483/9007199254740992)), (140681/36028797018963968), by norm_num⟩
  | 3 => ⟨((747816957121037/4503599627370496), (3475585794193/4503599627370496)), (176069/9007199254740992), by norm_num⟩
  | 2 => ⟨((280082905063899/562949953421312), (6940855185497/2251799813685248)), (44099/562949953421312), by norm_num⟩
  | 1 => ⟨((558770851025941/562949953421312), (10385510048917/1125899906842624)), (132707/562949953421312), by norm_num⟩
  | 0 => ⟨((138645077919783/140737488355328), (20668039032129/1125899906842624)), (133527/281474976710656), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((138645077919783/140737488355328), (20668039032129/1125899906842624)), (509365082860851199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((136536351177503/140737488355328), (2545094696823/70368744177664)), (1071945/1125899906842624), by norm_num⟩
  | 2 => ⟨((264553039596695/281474976710656), (79011884578319/1125899906842624)), (2157435/1125899906842624), by norm_num⟩
  | 3 => ⟨((247262231634735/281474976710656), (74261785092693/562949953421312)), (4358269/1125899906842624), by norm_num⟩
  | 4 => ⟨((1698478741096239/2251799813685248), (521883257169929/2251799813685248)), (4403453/562949953421312), by norm_num⟩
  | 5 => ⟨((4531909396091/8796093022208), (196822029260787/562949953421312)), (17367903/1125899906842624), by norm_num⟩
  | 6 => ⟨((322483851970771/2251799813685248), (811250723713473/2251799813685248)), (60082151/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-803303393/33554432)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-2027312047/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((485231432921453/4503599627370496), (1272988434967287/4503599627370496)), (23675817/1125899906842624), by norm_num⟩
  | 1 => ⟨((-40094471/268435456), (-210373007/536870912)), (1/33554432), by norm_num⟩
  | 2 => ⟨((444661913/4294967296), (1166555653/4294967296)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((-102738717/2147483648), (-1078126349/8589934592)), (43/4294967296), by norm_num⟩
  | 4 => ⟨((17803263/1073741824), (747300239/17179869184)), (61/17179869184), by norm_num⟩
  | 5 => ⟨((-39488901/8589934592), (-414391243/34359738368)), (69/68719476736), by norm_num⟩
  | 6 => ⟨((291963951/274877906944), (382978829/137438953472)), (65/274877906944), by norm_num⟩
  | 7 => ⟨((-462569119/2199023255552), (-75845913/137438953472)), (105/2199023255552), by norm_num⟩
  | 8 => ⟨((320628481/8796093022208), (210289523/2199023255552)), (37/4398046511104), by norm_num⟩
  | 9 => ⟨((-197549091/35184372088832), (-518263431/35184372088832)), (93/70368744177664), by norm_num⟩
  | 10 => ⟨((438177905/562949953421312), (1149545075/562949953421312)), (105/562949953421312), by norm_num⟩
  | 11 => ⟨((-220888567/2251799813685248), (-1158987531/4503599627370496)), (27/1125899906842624), by norm_num⟩
  | 12 => ⟨((408288767/36028797018963968), (1071131919/36028797018963968)), (51/18014398509481984), by norm_num⟩
  | 13 => ⟨((-348312871/288230376151711744), (-913787163/288230376151711744)), (89/288230376151711744), by norm_num⟩
  | 14 => ⟨((551844765/4611686018427387904), (361936569/1152921504606846976)), (143/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-204005143/18446744073709551616), (-1070401333/36893488147419103232)), (27/9223372036854775808), by norm_num⟩
  | 16 => ⟨((565622359/590295810358705651712), (370972833/147573952589676412928)), (19/73786976294838206464), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (785880545401/5070602400912917605986812821504)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445030791765617/158456325028528675187087900672), (1862795745413/633825300114114700748351602688)), (2887/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472816317273659/9903520314283042199192993792), (523855012687/9903520314283042199192993792)), (12993/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891135219333909/2475880078570760549798248448), (2226111911293/2475880078570760549798248448)), (55227/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886400545027499/77371252455336267181195264), (278225758135/19342813113834066795298816)), (55235/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551062775499509/9671406556917033397649408), (1043184131911/4835703278458516698824704)), (51791/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260108962703613/604462909807314587353088), (912623676489/302231454903657293676544)), (45325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889936744420747/75557863725914323419136), (2965417896785/75557863725914323419136)), (18417/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324786829482435/1180591620717411303424), (555882649113/1180591620717411303424)), (55265/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623657855947737/590295810358705651712), (3056488904263/590295810358705651712)), (38005/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826235186147865/73786976294838206464), (3819312940615/73786976294838206464)), (95045/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912880153739715/4611686018427387904), (4294942549587/9223372036854775808)), (53485/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597006028772055/1152921504606846976), (4292712667215/1152921504606846976)), (53513/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197220279380259/144115188075855872), (3753616002057/144115188075855872)), (93711/144115188075855872), by norm_num⟩
  | 4 => ⟨((373897605457709/9007199254740992), (5625411429391/36028797018963968)), (35173/9007199254740992), by norm_num⟩
  | 3 => ⟨((373547006403071/2251799813685248), (3511499054971/4503599627370496)), (88043/4503599627370496), by norm_num⟩
  | 2 => ⟨((2237776038762403/4503599627370496), (14019720998559/4503599627370496)), (176417/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230764047385127/2251799813685248), (20963975027893/2251799813685248)), (265455/1125899906842624), by norm_num⟩
  | 0 => ⟨((552432089778667/562949953421312), (41666013687785/2251799813685248)), (133559/281474976710656), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552432089778667/562949953421312), (41666013687785/2251799813685248)), (509487153173351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2167671981636131/2251799813685248), (81775095190613/2251799813685248)), (133535/140737488355328), by norm_num⟩
  | 2 => ⟨((1041858744560837/1125899906842624), (78719956171511/1125899906842624)), (266791/140737488355328), by norm_num⟩
  | 3 => ⟨((1917173641384975/2251799813685248), (145688038892783/1125899906842624)), (2124241/562949953421312), by norm_num⟩
  | 4 => ⟨((398642757972259/562949953421312), (124038232143381/562949953421312)), (2083441/281474976710656), by norm_num⟩
  | 5 => ⟨((509923003201869/1125899906842624), (702683322453491/2251799813685248)), (7737633/562949953421312), by norm_num⟩
  | 6 => ⟨((485231432921453/4503599627370496), (1272988434967287/4503599627370496)), (23675817/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-2027312047/67108864)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-147102275/4194304)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-244597383143953/1125899906842624), (552931631164337/4503599627370496)), (24998911/1125899906842624), by norm_num⟩
  | 1 => ⟨((187713767/536870912), (-424341741/2147483648)), (39/1073741824), by norm_num⟩
  | 2 => ⟨((-1208454613/4294967296), (341475843/2147483648)), (1/33554432), by norm_num⟩
  | 3 => ⟨((324155445/2147483648), (-732778891/8589934592)), (139/8589934592), by norm_num⟩
  | 4 => ⟨((-521708063/8589934592), (73710133/2147483648)), (57/8589934592), by norm_num⟩
  | 5 => ⟨((671725389/34359738368), (-759244049/68719476736)), (149/68719476736), by norm_num⟩
  | 6 => ⟨((-720733539/137438953472), (407318719/137438953472)), (41/68719476736), by norm_num⟩
  | 7 => ⟨((1325686723/1099511627776), (-749204787/1099511627776)), (153/1099511627776), by norm_num⟩
  | 8 => ⟨((-266701309/1099511627776), (301449647/2199023255552)), (125/4398046511104), by norm_num⟩
  | 9 => ⟨((190772977/4398046511104), (-431257325/17592186044416)), (91/17592186044416), by norm_num⟩
  | 10 => ⟨((-491259619/70368744177664), (555265511/140737488355328)), (119/140737488355328), by norm_num⟩
  | 11 => ⟨((1150039063/1125899906842624), (-649938447/1125899906842624)), (141/1125899906842624), by norm_num⟩
  | 12 => ⟨((-1233944313/9007199254740992), (174339263/2251799813685248)), (77/4503599627370496), by norm_num⟩
  | 13 => ⟨((1222127237/72057594037927936), (-345339347/36028797018963968)), (155/72057594037927936), by norm_num⟩
  | 14 => ⟨((-140495565/72057594037927936), (635202557/576460752303423488)), (145/576460752303423488), by norm_num⟩
  | 15 => ⟨((482386963/2305843009213693952), (-545236841/4611686018427387904)), (63/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-776371867/36893488147419103232), (219381211/18446744073709551616)), (103/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (3422216710607/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444954790643267/158456325028528675187087900672), (2027301995561/316912650057057350374175801344)), (11575/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945461449299153/19807040628566084398385987584), (2280422966601/19807040628566084398385987584)), (13025/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472692746729763/618970019642690137449562112), (2422604903431/1237940039285380274899124224)), (55371/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886218168074461/77371252455336267181195264), (4844434573707/154742504910672534362390528)), (13847/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387680066221919/2417851639229258349412352), (141901052997/302231454903657293676544)), (6493/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259808712385129/604462909807314587353088), (993101432803/151115727451828646838272)), (45469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236180975049811/9444732965739290427392), (6453614701223/75557863725914323419136)), (1155/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((649389851467481/2361183241434822606848), (1209714853771/1180591620717411303424)), (55469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405787728163111/147573952589676412928), (3325617593803/295147905179352825856)), (19079/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912799650022733/36893488147419103232), (2077687244457/18446744073709551616)), (47733/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825041904314939/9223372036854775808), (9345061571317/9223372036854775808)), (107497/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596283841436153/1152921504606846976), (9339397198311/1152921504606846976)), (26905/288230376151711744), by norm_num⟩
  | 5 => ⟨((299146028769057/36028797018963968), (8165599329371/144115188075855872)), (2947/4503599627370496), by norm_num⟩
  | 4 => ⟨((1494627691617093/36028797018963968), (6117825290045/18014398509481984)), (141731/36028797018963968), by norm_num⟩
  | 3 => ⟨((746484902264341/4503599627370496), (7636124559481/4503599627370496)), (88823/4503599627370496), by norm_num⟩
  | 2 => ⟨((558823831147603/1125899906842624), (15238769354941/2251799813685248)), (89185/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113466415498495/1125899906842624), (11387212609077/562949953421312)), (269367/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100814275848139/1125899906842624), (5651720555299/140737488355328)), (546005/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100814275848139/1125899906842624), (5651720555299/140737488355328)), (2082843784812545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((537235938143259/562949953421312), (44206378436069/562949953421312)), (555767/562949953421312), by norm_num⟩
  | 2 => ⟨((1018450210701739/1125899906842624), (168748607556903/1125899906842624)), (1148047/562949953421312), by norm_num⟩
  | 3 => ⟨((55997691990385/70368744177664), (305288336693993/1125899906842624)), (151319/35184372088832), by norm_num⟩
  | 4 => ⟨((157551495758717/281474976710656), (971763384225549/2251799813685248)), (1291569/140737488355328), by norm_num⟩
  | 5 => ⟨((286133005862459/2251799813685248), (1087860643936893/2251799813685248)), (1280313/70368744177664), by norm_num⟩
  | 6 => ⟨((-244597383143953/1125899906842624), (552931631164337/4503599627370496)), (24998911/1125899906842624), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-147102275/4194304)), (1/33554432), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1310131405/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((107100318599125/2251799813685248), (-58506246353651/281474976710656)), (17749293/1125899906842624), by norm_num⟩
  | 1 => ⟨((-366016407/4294967296), (399891361/1073741824)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((163953341/2147483648), (-716509133/2147483648)), (7/268435456), by norm_num⟩
  | 3 => ⟨((-195843301/4294967296), (1711749365/8589934592)), (17/1073741824), by norm_num⟩
  | 4 => ⟨((350904089/17179869184), (-1533521567/17179869184)), (31/4294967296), by norm_num⟩
  | 5 => ⟨((-125747145/17179869184), (274770179/8589934592)), (91/34359738368), by norm_num⟩
  | 6 => ⟨((300411517/137438953472), (-656429427/68719476736)), (55/68719476736), by norm_num⟩
  | 7 => ⟨((-307580103/549755813888), (1344187019/549755813888)), (57/274877906944), by norm_num⟩
  | 8 => ⟨((275554781/2199023255552), (-602114955/1099511627776)), (13/274877906944), by norm_num⟩
  | 9 => ⟨((-219434617/8796093022208), (958973487/8796093022208)), (21/2199023255552), by norm_num⟩
  | 10 => ⟨((157269621/35184372088832), (-1374599861/70368744177664)), (61/35184372088832), by norm_num⟩
  | 11 => ⟨((-204937697/281474976710656), (895619025/281474976710656)), (81/281474976710656), by norm_num⟩
  | 12 => ⟨((244799373/2251799813685248), (-1069822579/2251799813685248)), (99/2251799813685248), by norm_num⟩
  | 13 => ⟨((-269920981/18014398509481984), (1179609069/18014398509481984)), (111/18014398509481984), by norm_num⟩
  | 14 => ⟨((276361985/144115188075855872), (-603878777/72057594037927936)), (115/144115188075855872), by norm_num⟩
  | 15 => ⟨((-264092909/1152921504606846976), (577069609/576460752303423488)), (7/72057594037927936), by norm_num⟩
  | 16 => ⟨((236595485/9223372036854775808), (-1033969937/9223372036854775808)), (51/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-1753115537877/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889791489691699/316912650057057350374175801344), (-2076533194043/633825300114114700748351602688)), (23101/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945328803699023/19807040628566084398385987584), (-1167889037237/19807040628566084398385987584)), (3249/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((945244817954045/1237940039285380274899124224), (-1240686294027/1237940039285380274899124224)), (55241/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886077785459141/77371252455336267181195264), (-2480932095335/154742504910672534362390528)), (55249/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775228834814749/4835703278458516698824704), (-2325405898777/9671406556917033397649408)), (25903/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259579563403199/604462909807314587353088), (-1017131157041/302231454903657293676544)), (45339/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889076598719519/75557863725914323419136), (-3304799244747/75557863725914323419136)), (73693/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649251160413857/2361183241434822606848), (-2477832242997/4722366482869645213696)), (55285/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622771167275305/590295810358705651712), (-3405773020875/590295810358705651712)), (9505/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1825127098926915/73786976294838206464), (-1063836864029/18446744073709551616)), (47543/36893488147419103232), by norm_num⟩
  | 7 => ⟨((7127008147475/36028797018963968), (-2392348658273/4611686018427387904)), (53511/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595760277799039/1152921504606846976), (-4781488185573/1152921504606846976)), (107085/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299032694306593/36028797018963968), (-2090097033415/72057594037927936)), (46885/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493957229368721/36028797018963968), (-3131540174785/18014398509481984)), (140795/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492148393338187/9007199254740992), (-7816243859887/9007199254740992)), (176239/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233702356920291/4503599627370496), (-487334903539/140737488355328)), (88305/1125899906842624), by norm_num⟩
  | 1 => ⟨((2224667508501697/2251799813685248), (-11648909746017/1125899906842624)), (531685/2251799813685248), by norm_num⟩
  | 0 => ⟨((549397844550257/562949953421312), (-23109820758891/1125899906842624)), (1070811/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549397844550257/562949953421312), (-23109820758891/1125899906842624)), (4084819802291106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1071869617570767/1125899906842624), (-45106978464835/1125899906842624)), (2134025/2251799813685248), by norm_num⟩
  | 2 => ⟨((63664064995643/70368744177664), (-85884721124919/1125899906842624)), (264639/140737488355328), by norm_num⟩
  | 3 => ⟨((457509935114631/562949953421312), (-310806766937589/2251799813685248)), (2076891/562949953421312), by norm_num⟩
  | 4 => ⟨((722187777420681/1125899906842624), (-505185879883657/2251799813685248)), (15796449/2251799813685248), by norm_num⟩
  | 5 => ⟨((50820680169413/140737488355328), (-648084373326955/2251799813685248)), (27352475/2251799813685248), by norm_num⟩
  | 6 => ⟨((107100318599125/2251799813685248), (-58506246353651/281474976710656)), (17749293/1125899906842624), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1310131405/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-711423057/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-3103245333261/2251799813685248), (840719040381951/4503599627370496)), (134684487/4503599627370496), by norm_num⟩
  | 1 => ⟨((11517785/4294967296), (-24377759/67108864)), (251/4294967296), by norm_num⟩
  | 2 => ⟨((-11206287/4294967296), (1517981717/4294967296)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((7268809/4294967296), (-1969237353/8589934592)), (321/8589934592), by norm_num⟩
  | 4 => ⟨((-14144449/17179869184), (478994869/4294967296)), (157/8589934592), by norm_num⟩
  | 5 => ⟨((11009531/34359738368), (-1491329563/34359738368)), (123/17179869184), by norm_num⟩
  | 6 => ⟨((-3570593/34359738368), (967331111/68719476736)), (321/137438953472), by norm_num⟩
  | 7 => ⟨((992579/34359738368), (-1075622529/274877906944)), (45/68719476736), by norm_num⟩
  | 8 => ⟨((-3862939/549755813888), (523266199/549755813888)), (11/68719476736), by norm_num⟩
  | 9 => ⟨((13363435/8796093022208), (-905092451/4398046511104)), (153/4398046511104), by norm_num⟩
  | 10 => ⟨((-5200809/17592186044416), (1408982869/35184372088832)), (15/2199023255552), by norm_num⟩
  | 11 => ⟨((14720447/281474976710656), (-498500739/70368744177664)), (171/140737488355328), by norm_num⟩
  | 12 => ⟨((-4774111/562949953421312), (646691765/562949953421312)), (223/1125899906842624), by norm_num⟩
  | 13 => ⟨((11433835/9007199254740992), (-96800313/562949953421312)), (67/2251799813685248), by norm_num⟩
  | 14 => ⟨((-12713837/72057594037927936), (53818489/2251799813685248)), (75/18014398509481984), by norm_num⟩
  | 15 => ⟨((6597329/288230376151711744), (-1787322777/576460752303423488)), (313/576460752303423488), by norm_num⟩
  | 16 => ⟨((-12837809/4611686018427387904), (869492383/2305843009213693952)), (153/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (2055753769507/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222422124860235/79228162514264337593543950336), (2434468794267/633825300114114700748351602688)), (11555/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((118151616453623/2475880078570760549798248448), (1369183951309/19807040628566084398385987584)), (52005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945121692278029/1237940039285380274899124224), (2909017207069/2475880078570760549798248448)), (1727/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((885954646752657/77371252455336267181195264), (2908456276593/154742504910672534362390528)), (110549/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550226756900563/9671406556917033397649408), (340760234877/1208925819614629174706176)), (25915/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259377487151007/604462909807314587353088), (2384725885681/604462909807314587353088)), (90725/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472187043279375/18889465931478580854784), (3874062776003/75557863725914323419136)), (147467/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649127978240107/2361183241434822606848), (2904570151163/4722366482869645213696)), (110635/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811216171546979/295147905179352825856), (1996098465283/295147905179352825856)), (38045/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824703459172423/73786976294838206464), (2493933235769/36893488147419103232)), (95155/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824037340879573/9223372036854775808), (350504942771/576460752303423488)), (26777/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797641672956139/576460752303423488), (5603992783769/1152921504606846976)), (107181/576460752303423488), by norm_num⟩
  | 5 => ⟨((597856626181575/72057594037927936), (2449449721493/72057594037927936)), (46933/36028797018963968), by norm_num⟩
  | 4 => ⟨((373332631365827/9007199254740992), (458697986937/2251799813685248)), (281929/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491364289584823/9007199254740992), (9157908334187/9007199254740992)), (352989/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232131998538229/4503599627370496), (18267726434517/4503599627370496)), (707717/4503599627370496), by norm_num⟩
  | 1 => ⟨((555576666527919/562949953421312), (27281587922191/2251799813685248)), (532965/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096424453325455/1125899906842624), (13521127864275/562949953421312)), (537333/562949953421312), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096424453325455/1125899906842624), (13521127864275/562949953421312)), (2049762727977561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((133383892625975/140737488355328), (52668608059503/1125899906842624)), (4289375/2251799813685248), by norm_num⟩
  | 2 => ⟨((2017704825790579/2251799813685248), (199666600399505/2251799813685248)), (4265907/1125899906842624), by norm_num⟩
  | 3 => ⟨((447560434569227/562949953421312), (357818897334355/2251799813685248)), (16802739/2251799813685248), by norm_num⟩
  | 4 => ⟨((1366431909035249/2251799813685248), (284475698443113/1125899906842624)), (32057293/2251799813685248), by norm_num⟩
  | 5 => ⟨((685420817885663/2251799813685248), (690499518359215/2251799813685248)), (13776347/562949953421312), by norm_num⟩
  | 6 => ⟨((-3103245333261/2251799813685248), (840719040381951/4503599627370496)), (134684487/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-711423057/16777216)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1520484035/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((354957322285495/9007199254740992), (-1455916457674231/9007199254740992)), (331885527/9007199254740992), by norm_num⟩
  | 1 => ⟨((-175979853/2147483648), (1443621237/4294967296)), (83/1073741824), by norm_num⟩
  | 2 => ⟨((365939817/4294967296), (-1500962985/4294967296)), (87/1073741824), by norm_num⟩
  | 3 => ⟨((-31706269/536870912), (1040388261/4294967296)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((65931333/2147483648), (-1081713285/8589934592)), (1/33554432), by norm_num⟩
  | 5 => ⟨((-54840141/4294967296), (112467977/2147483648)), (215/17179869184), by norm_num⟩
  | 6 => ⟨((304098313/68719476736), (-1247309779/68719476736)), (75/17179869184), by norm_num⟩
  | 7 => ⟨((-361345523/274877906944), (741059363/137438953472)), (359/274877906944), by norm_num⟩
  | 8 => ⟨((187849223/549755813888), (-192623703/137438953472)), (47/137438953472), by norm_num⟩
  | 9 => ⟨((-347219091/4398046511104), (712088409/2199023255552)), (175/2199023255552), by norm_num⟩
  | 10 => ⟨((288808721/17592186044416), (-1184596975/17592186044416)), (293/17592186044416), by norm_num⟩
  | 11 => ⟨((-54596441/17592186044416), (895745513/70368744177664)), (7/2199023255552), by norm_num⟩
  | 12 => ⟨((302746953/562949953421312), (-620883477/281474976710656)), (313/562949953421312), by norm_num⟩
  | 13 => ⟨((-48426507/562949953421312), (1589034947/4503599627370496)), (403/4503599627370496), by norm_num⟩
  | 14 => ⟨((230171635/18014398509481984), (-944087223/18014398509481984)), (241/18014398509481984), by norm_num⟩
  | 15 => ⟨((-7977141/4503599627370496), (1047026235/144115188075855872)), (269/144115188075855872), by norm_num⟩
  | 16 => ⟨((132703987/576460752303423488), (-272153731/288230376151711744)), (141/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-1734633546035/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444800066969669/158456325028528675187087900672), (-1026900487227/316912650057057350374175801344)), (138603/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890227124682197/39614081257132168796771975168), (-2310159354083/39614081257132168796771975168)), (38987/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472508082419313/618970019642690137449562112), (-2454094945835/2475880078570760549798248448)), (82859/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771698356544277/154742504910672534362390528), (-1226794762225/77371252455336267181195264)), (165743/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550029128740853/9671406556917033397649408), (-1149851644725/4835703278458516698824704)), (77705/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629602343850189/302231454903657293676544), (-2011703624079/604462909807314587353088)), (34003/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888467608629043/75557863725914323419136), (-817003065743/18889465931478580854784)), (55267/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649022869147295/2361183241434822606848), (-1225064562363/2361183241434822606848)), (82923/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811071813149911/295147905179352825856), (-3367497968323/590295810358705651712)), (114055/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912171531316645/36893488147419103232), (-1051807259309/18446744073709551616)), (285245/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113977036308243/576460752303423488), (-1182546748417/2305843009213693952)), (321049/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594879442778961/1152921504606846976), (-4726507201677/1152921504606846976)), (321235/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597680399911345/72057594037927936), (-2065778597927/72057594037927936)), (140645/72057594037927936), by norm_num⟩
  | 4 => ⟨((373200942254977/9007199254740992), (-6189070479043/36028797018963968)), (26397/2251799813685248), by norm_num⟩
  | 3 => ⟨((1490709201350801/9007199254740992), (-3860945776427/4503599627370496)), (264337/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115415933386443/2251799813685248), (-3850128606489/1125899906842624)), (1059551/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110190742481069/1125899906842624), (-11496424008561/1125899906842624)), (1594845/2251799813685248), by norm_num⟩
  | 0 => ⟨((547274509988457/562949953421312), (-45555487805929/2251799813685248)), (802959/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547274509988457/562949953421312), (-45555487805929/2251799813685248)), (3063045503856468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2127220589036785/2251799813685248), (-88573973990957/2251799813685248)), (796845/281474976710656), by norm_num⟩
  | 2 => ⟨((1003024793345343/1125899906842624), (-83673681817219/1125899906842624)), (6272831/1125899906842624), by norm_num⟩
  | 3 => ⟨((1774682536102679/2251799813685248), (-298167810133379/2251799813685248)), (24217699/2251799813685248), by norm_num⟩
  | 4 => ⟨((1359176798198237/2251799813685248), (-469982457815099/2251799813685248)), (44586261/2251799813685248), by norm_num⟩
  | 5 => ⟨((722301355662975/2251799813685248), (-567358828560373/2251799813685248)), (72435723/2251799813685248), by norm_num⟩
  | 6 => ⟨((354957322285495/9007199254740992), (-1455916457674231/9007199254740992)), (331885527/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1520484035/33554432)), (3/33554432), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile020Terms0
