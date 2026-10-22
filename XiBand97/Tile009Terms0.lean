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
namespace Reinmann.XiBand97.Tile009Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (12067/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (12067/640))
  have he : value ((69/80), (12067/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-877050675/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((542632825517875/1125899906842624), (-149174435459355/562949953421312)), (28587279/2251799813685248), by norm_num⟩
  | 1 => ⟨((-717400385/2147483648), (98609771/536870912)), (21/2147483648), by norm_num⟩
  | 2 => ⟨((248632027/2147483648), (-273404339/4294967296)), (31/8589934592), by norm_num⟩
  | 3 => ⟨((-919139139/34359738368), (505358525/34359738368)), (31/34359738368), by norm_num⟩
  | 4 => ⟨((637098703/137438953472), (-350287837/137438953472)), (23/137438953472), by norm_num⟩
  | 5 => ⟨((-44160317/68719476736), (388481643/1099511627776)), (7/274877906944), by norm_num⟩
  | 6 => ⟨((1306009567/17592186044416), (-179516637/4398046511104)), (27/8796093022208), by norm_num⟩
  | 7 => ⟨((-129322407/17592186044416), (568829489/140737488355328)), (45/140737488355328), by norm_num⟩
  | 8 => ⟨((358557847/562949953421312), (-394282557/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 9 => ⟨((-883674171/18014398509481984), (121464819/4503599627370496)), (43/18014398509481984), by norm_num⟩
  | 10 => ⟨((30625813/9007199254740992), (-134708795/72057594037927936)), (25/144115188075855872), by norm_num⟩
  | 11 => ⟨((-988076029/4611686018427387904), (16976913/144115188075855872)), (13/1152921504606846976), by norm_num⟩
  | 12 => ⟨((114147019/9223372036854775808), (-251039987/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 13 => ⟨((-779034431/1180591620717411303424), (214163273/590295810358705651712)), (11/295147905179352825856), by norm_num⟩
  | 14 => ⟨((154281577/4722366482869645213696), (-678613343/37778931862957161709568)), (9/4722366482869645213696), by norm_num⟩
  | 15 => ⟨((-456276651/302231454903657293676544), (31358595/37778931862957161709568)), (55/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1265067497/19342813113834066795298816), (-695555895/19342813113834066795298816)), (39/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-654826613925/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((445262025609843/158456325028528675187087900672), (-776841992357/633825300114114700748351602688)), (11535/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892305827741631/39614081257132168796771975168), (-873899964959/39614081257132168796771975168)), (25955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892240824765015/2475880078570760549798248448), (-464231014033/1237940039285380274899124224)), (13789/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773906708797511/154742504910672534362390528), (-928398261917/154742504910672534362390528)), (6895/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552099307176493/9671406556917033397649408), (-870305623759/9671406556917033397649408)), (25857/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630507970992339/302231454903657293676544), (-380724839669/302231454903657293676544)), (22627/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945705306016167/37778931862957161709568), (-309307181261/18889465931478580854784)), (9193/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((325063185385939/1180591620717411303424), (-927810426729/4722366482869645213696)), (13791/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25393403913599/9223372036854775808), (-1275558792801/590295810358705651712)), (37929/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914067617293785/36893488147419103232), (-1594177712281/73786976294838206464)), (47419/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827897937516283/9223372036854775808), (-1793077666031/9223372036854775808)), (53355/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399785938130531/288230376151711744), (-1792612431351/1152921504606846976)), (53367/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599545446053667/72057594037927936), (-1568012613081/144115188075855872)), (46709/144115188075855872), by norm_num⟩
  | 4 => ⟨((374599136840381/9007199254740992), (-2350972702541/36028797018963968)), (70089/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497696038287037/9007199254740992), (-367110712415/1125899906842624)), (87657/9007199254740992), by norm_num⟩
  | 2 => ⟨((2244793109396271/4503599627370496), (-5868283665655/4503599627370496)), (43863/1125899906842624), by norm_num⟩
  | 1 => ⟨((2241292189705427/2251799813685248), (-2197178994005/562949953421312)), (263521/2251799813685248), by norm_num⟩
  | 0 => ⟨((1115397164723611/1125899906842624), (-17522652701979/2251799813685248)), (132105/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115397164723611/1125899906842624), (-17522652701979/2251799813685248)), (503940584422874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2209848436212599/2251799813685248), (-34718391969733/2251799813685248)), (527603/1125899906842624), by norm_num⟩
  | 2 => ⟨((1084071664501153/1125899906842624), (-34071582978137/1125899906842624)), (1051817/1125899906842624), by norm_num⟩
  | 3 => ⟨((2085532637266255/2251799813685248), (-131223166275511/2251799813685248)), (1044571/562949953421312), by norm_num⟩
  | 4 => ⟨((1923895203919277/2251799813685248), (-243067962231609/2251799813685248)), (4113259/1125899906842624), by norm_num⟩
  | 5 => ⟨((50546937765963/70368744177664), (-103836336587687/562949953421312)), (989573/140737488355328), by norm_num⟩
  | 6 => ⟨((542632825517875/1125899906842624), (-149174435459355/562949953421312)), (28587279/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-877050675/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1390092431/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-505356088966563/4503599627370496), (-1671259856926677/4503599627370496)), (4632545/140737488355328), by norm_num⟩
  | 1 => ⟨((264735417/2147483648), (218876197/536870912)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-145420791/2147483648), (-961840319/4294967296)), (89/4294967296), by norm_num⟩
  | 3 => ⟨((426029515/17179869184), (1408919459/17179869184)), (133/17179869184), by norm_num⟩
  | 4 => ⟨((-468041261/68719476736), (-193482029/8589934592)), (149/68719476736), by norm_num⟩
  | 5 => ⟨((411356705/274877906944), (680197551/137438953472)), (133/274877906944), by norm_num⟩
  | 6 => ⟨((-301281021/1099511627776), (-498182259/549755813888)), (99/1099511627776), by norm_num⟩
  | 7 => ⟨((378275465/8796093022208), (1250992347/8796093022208)), (127/8796093022208), by norm_num⟩
  | 8 => ⟨((-207789037/35184372088832), (-687177783/35184372088832)), (71/35184372088832), by norm_num⟩
  | 9 => ⟨((405830381/562949953421312), (1342119035/562949953421312)), (141/562949953421312), by norm_num⟩
  | 10 => ⟨((-356680195/4503599627370496), (-294893693/1125899906842624)), (63/2251799813685248), by norm_num⟩
  | 11 => ⟨((284984179/36028797018963968), (471234669/18014398509481984)), (103/36028797018963968), by norm_num⟩
  | 12 => ⟨((-417449495/576460752303423488), (-1380544529/576460752303423488)), (153/576460752303423488), by norm_num⟩
  | 13 => ⟨((282224705/4611686018427387904), (466671749/2305843009213693952)), (53/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-44293647/9223372036854775808), (-1171865871/73786976294838206464)), (17/9223372036854775808), by norm_num⟩
  | 15 => ⟨((415245183/1180591620717411303424), (1373254663/1180591620717411303424)), (81/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-456193461/18889465931478580854784), (-1508674449/18889465931478580854784)), (181/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-2428635361251/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780503734457737/633825300114114700748351602688), (-2879509841171/633825300114114700748351602688)), (23121/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891693211373795/39614081257132168796771975168), (-1619582921595/19807040628566084398385987584)), (52031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891589667927755/2475880078570760549798248448), (-860319979151/618970019642690137449562112)), (55293/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773255268612037/154742504910672534362390528), (-3440904365931/154742504910672534362390528)), (27653/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551488281046321/9671406556917033397649408), (-3225448804199/9671406556917033397649408)), (51861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260480993278283/604462909807314587353088), (-2821868646511/604462909807314587353088)), (2837/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((945270378273277/37778931862957161709568), (-1146197069895/18889465931478580854784)), (9223/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162449982101629/590295810358705651712), (-859484108457/1180591620717411303424)), (55359/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624279333104709/590295810358705651712), (-2363049256653/295147905179352825856)), (9519/73786976294838206464), by norm_num⟩
  | 8 => ⟨((913505443691145/36893488147419103232), (-2953013445209/36893488147419103232)), (11905/9223372036854775808), by norm_num⟩
  | 7 => ⟨((913315698756893/4611686018427387904), (-3321042600789/4611686018427387904)), (53607/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597875152706361/1152921504606846976), (-6639341083017/1152921504606846976)), (107301/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197978552635101/144115188075855872), (-5806335895613/144115188075855872)), (93985/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496723415525687/36028797018963968), (-2175831924647/9007199254740992)), (35293/9007199254740992), by norm_num⟩
  | 3 => ⟨((93474784301735/562949953421312), (-2717087261015/2251799813685248)), (176807/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120284983096809/2251799813685248), (-1356516070487/281474976710656)), (177319/2251799813685248), by norm_num⟩
  | 1 => ⟨((279362159132549/281474976710656), (-16237625685523/1125899906842624)), (66815/281474976710656), by norm_num⟩
  | 0 => ⟨((1108882470548003/1125899906842624), (-8078222102063/281474976710656)), (539657/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108882470548003/1125899906842624), (-8078222102063/281474976710656)), (2058628086570357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((545597438664273/562949953421312), (-31824494620633/562949953421312)), (1093977/1125899906842624), by norm_num⟩
  | 2 => ⟨((1053961421672357/1125899906842624), (-61687056358303/562949953421312)), (1122101/562949953421312), by norm_num⟩
  | 3 => ⟨((973100272969601/1125899906842624), (-230982442481959/1125899906842624)), (4693453/1125899906842624), by norm_num⟩
  | 4 => ⟨((396825351475707/562949953421312), (-199635044344841/562949953421312)), (10038737/1125899906842624), by norm_num⟩
  | 5 => ⟨((208928356647767/562949953421312), (-1125787415489439/2251799813685248)), (42545233/2251799813685248), by norm_num⟩
  | 6 => ⟨((-505356088966563/4503599627370496), (-1671259856926677/4503599627370496)), (4632545/140737488355328), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1390092431/67108864)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-877050675/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((364931790654743/2251799813685248), (-71895330052335/281474976710656)), (43108765/2251799813685248), by norm_num⟩
  | 1 => ⟨((-482466587/2147483648), (380203593/1073741824)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((668840709/4294967296), (-527074097/2147483648)), (21/1073741824), by norm_num⟩
  | 3 => ⟨((-618140069/8589934592), (487119899/4294967296)), (79/8589934592), by norm_num⟩
  | 4 => ⟨((214231023/8589934592), (-675291569/17179869184)), (7/2147483648), by norm_num⟩
  | 5 => ⟨((-475179615/68719476736), (748922315/68719476736)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((219579607/137438953472), (-173037797/68719476736)), (61/274877906944), by norm_num⟩
  | 7 => ⟨((-347887967/1099511627776), (548300165/1099511627776)), (99/2199023255552), by norm_num⟩
  | 8 => ⟨((482275127/8796093022208), (-760105427/8796093022208)), (35/4398046511104), by norm_num⟩
  | 9 => ⟨((-297144573/35184372088832), (936648771/70368744177664)), (11/8796093022208), by norm_num⟩
  | 10 => ⟨((329543877/281474976710656), (-129847091/70368744177664)), (25/140737488355328), by norm_num⟩
  | 11 => ⟨((-332250777/2251799813685248), (261827331/1125899906842624)), (103/4503599627370496), by norm_num⟩
  | 12 => ⟨((307064919/18014398509481984), (-241979835/9007199254740992)), (97/36028797018963968), by norm_num⟩
  | 13 => ⟨((-261958379/144115188075855872), (206434019/72057594037927936)), (85/288230376151711744), by norm_num⟩
  | 14 => ⟨((830060397/4611686018427387904), (-1308243733/4611686018427387904)), (137/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-613710959/36893488147419103232), (60453697/2305843009213693952)), (103/36893488147419103232), by norm_num⟩
  | 16 => ⟨((425392021/295147905179352825856), (-335226477/147573952589676412928)), (73/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-1309653227849/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780123733263745/633825300114114700748351602688), (-776077380679/316912650057057350374175801344)), (46177/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891265939475269/39614081257132168796771975168), (-872993523951/19807040628566084398385987584)), (25977/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891135973391459/2475880078570760549798248448), (-1854884753647/2475880078570760549798248448)), (55207/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772801891094353/154742504910672534362390528), (-1854629992579/154742504910672534362390528)), (55213/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387765894093437/2417851639229258349412352), (-1738444972337/9671406556917033397649408)), (51769/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39378428542119/18889465931478580854784), (-1520868747753/604462909807314587353088)), (45305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889938057697349/75557863725914323419136), (-2470904425049/75557863725914323419136)), (2301/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649574192319117/2361183241434822606848), (-463183632659/1180591620717411303424)), (55235/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623659455435319/590295810358705651712), (-1273394496907/295147905179352825856)), (37983/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456559346127233/18446744073709551616), (-3182405060897/73786976294838206464)), (94985/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912881527014853/4611686018427387904), (-3578719552235/9223372036854775808)), (6681/576460752303423488), by norm_num⟩
  | 6 => ⟨((99813069794715/72057594037927936), (-3576862600171/1152921504606846976)), (53471/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197223364917719/144115188075855872), (-3127666700089/144115188075855872)), (93627/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495595816111275/36028797018963968), (-4687326389381/36028797018963968)), (70273/18014398509481984), by norm_num⟩
  | 3 => ⟨((747098053110371/4503599627370496), (-731482459961/1125899906842624)), (175865/9007199254740992), by norm_num⟩
  | 2 => ⟨((34965565663703/70368744177664), (-730115426647/281474976710656)), (176141/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230804261539177/2251799813685248), (-17468167224617/2251799813685248)), (529807/2251799813685248), by norm_num⟩
  | 0 => ⟨((2209848436212599/2251799813685248), (-34718391969733/2251799813685248)), (266289/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2209848436212599/2251799813685248), (-34718391969733/2251799813685248)), (1015811922313499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1084071664501153/1125899906842624), (-34071582978137/1125899906842624)), (1061735/1125899906842624), by norm_num⟩
  | 2 => ⟨((2085532637266255/2251799813685248), (-131223166275511/2251799813685248)), (4217683/2251799813685248), by norm_num⟩
  | 3 => ⟨((1923895203919277/2251799813685248), (-243067962231609/2251799813685248)), (4152045/1125899906842624), by norm_num⟩
  | 4 => ⟨((50546937765963/70368744177664), (-103836336587687/562949953421312)), (15982467/2251799813685248), by norm_num⟩
  | 5 => ⟨((542632825517875/1125899906842624), (-149174435459355/562949953421312)), (28856843/2251799813685248), by norm_num⟩
  | 6 => ⟨((364931790654743/2251799813685248), (-71895330052335/281474976710656)), (43108765/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-877050675/33554432)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-2036448603/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((269552004088135/2251799813685248), (246519057904783/1125899906842624)), (73661905/4503599627370496), by norm_num⟩
  | 1 => ⟨((-413729873/2147483648), (-756754147/2147483648)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((665872543/4294967296), (1217948815/4294967296)), (97/4294967296), by norm_num⟩
  | 3 => ⟨((-714453677/8589934592), (-653404333/4294967296)), (53/4294967296), by norm_num⟩
  | 4 => ⟨((574934417/17179869184), (525806853/8589934592)), (87/17179869184), by norm_num⟩
  | 5 => ⟨((-370128499/34359738368), (-677002787/34359738368)), (115/68719476736), by norm_num⟩
  | 6 => ⟨((397132559/137438953472), (11349937/2147483648)), (63/137438953472), by norm_num⟩
  | 7 => ⟨((-182617199/274877906944), (-1336101955/1099511627776)), (59/549755813888), by norm_num⟩
  | 8 => ⟨((587822087/4398046511104), (1075186571/4398046511104)), (97/4398046511104), by norm_num⟩
  | 9 => ⟨((-6569883/274877906944), (-769087125/17592186044416)), (71/17592186044416), by norm_num⟩
  | 10 => ⟨((270689761/70368744177664), (495119191/70368744177664)), (93/140737488355328), by norm_num⟩
  | 11 => ⟨((-633684893/1125899906842624), (-1159074323/1125899906842624)), (111/1125899906842624), by norm_num⟩
  | 12 => ⟨((679917661/9007199254740992), (1243638773/9007199254740992)), (121/9007199254740992), by norm_num⟩
  | 13 => ⟨((-673406315/72057594037927936), (-153966107/9007199254740992)), (61/36028797018963968), by norm_num⟩
  | 14 => ⟨((619317517/576460752303423488), (1132794925/576460752303423488)), (57/288230376151711744), by norm_num⟩
  | 15 => ⟨((-531601649/4611686018427387904), (-972353653/4611686018427387904)), (99/4611686018427387904), by norm_num⟩
  | 16 => ⟨((106947481/9223372036854775808), (782471417/36893488147419103232)), (81/36893488147419103232), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (87151040315/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779826484979095/633825300114114700748351602688), (1652089207777/633825300114114700748351602688)), (23091/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945465782088289/19807040628566084398385987584), (929185118705/19807040628566084398385987584)), (6495/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890780733857963/2475880078570760549798248448), (493559638439/618970019642690137449562112)), (55213/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443111672516157/38685626227668133590597632), (493480951439/38685626227668133590597632)), (13805/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((12115082940005/75557863725914323419136), (1850219205199/9671406556917033397649408)), (809/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1259818414215853/604462909807314587353088), (1618607506023/604462909807314587353088)), (177/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((236183096665927/9444732965739290427392), (2629610523899/75557863725914323419136)), (18411/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162349186061889/590295810358705651712), (1971659690033/4722366482869645213696)), (55245/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623171582340725/590295810358705651712), (2710141499657/590295810358705651712)), (75981/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825627706809539/73786976294838206464), (1693170730251/36893488147419103232)), (95005/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114067336980483/576460752303423488), (1903899337571/4611686018427387904)), (13365/1152921504606846976), by norm_num⟩
  | 6 => ⟨((798161867874175/576460752303423488), (3805505429565/1152921504606846976)), (106969/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196623973169671/144115188075855872), (3327238846917/144115188075855872)), (93655/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494697361813193/36028797018963968), (1246426301069/9007199254740992)), (140593/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493074146950125/9007199254740992), (1555780513649/2251799813685248)), (175937/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235555610870309/4503599627370496), (6209624697989/2251799813685248)), (352463/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227451695364385/2251799813685248), (9280752477263/1125899906842624)), (66271/281474976710656), by norm_num⟩
  | 0 => ⟨((275397076473549/281474976710656), (4606779808531/281474976710656)), (1066249/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((275397076473549/281474976710656), (4606779808531/281474976710656)), (4067417153365325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2155000155141053/2251799813685248), (36058443448235/1125899906842624)), (1060677/1125899906842624), by norm_num⟩
  | 2 => ⟨((128753253150269/140737488355328), (138033497920793/2251799813685248)), (4196203/2251799813685248), by norm_num⟩
  | 3 => ⟨((1876170864812611/2251799813685248), (252559031835815/2251799813685248)), (8192215/2251799813685248), by norm_num⟩
  | 4 => ⟨((383718728947919/562949953421312), (210428961889003/1125899906842624)), (3872239/562949953421312), by norm_num⟩
  | 5 => ⟨((967545872363371/2251799813685248), (286865762397349/1125899906842624)), (26904933/2251799813685248), by norm_num⟩
  | 6 => ⟨((269552004088135/2251799813685248), (246519057904783/1125899906842624)), (73661905/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-2036448603/67108864)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1133571553/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-343210479491799/2251799813685248), (-671558843897617/4503599627370496)), (43316629/2251799813685248), by norm_num⟩
  | 1 => ⟨((586462619/2147483648), (286882381/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-1050799951/4294967296), (-514024223/2147483648)), (69/2147483648), by norm_num⟩
  | 3 => ⟨((156898397/1073741824), (614005179/4294967296)), (21/1073741824), by norm_num⟩
  | 4 => ⟨((-562248377/8589934592), (-550074797/8589934592)), (77/8589934592), by norm_num⟩
  | 5 => ⟨((805931083/34359738368), (788481381/34359738368)), (7/2147483648), by norm_num⟩
  | 6 => ⟨((-962689767/137438953472), (-941845987/137438953472)), (17/17179869184), by norm_num⟩
  | 7 => ⟨((246415501/137438953472), (482160419/274877906944)), (141/549755813888), by norm_num⟩
  | 8 => ⟨((-883034615/2199023255552), (-863915497/2199023255552)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((703193615/8796093022208), (687968343/8796093022208)), (13/1099511627776), by norm_num⟩
  | 10 => ⟨((-1007963055/70368744177664), (-986139035/70368744177664)), (151/70368744177664), by norm_num⟩
  | 11 => ⟨((328368609/140737488355328), (321258901/140737488355328)), (25/70368744177664), by norm_num⟩
  | 12 => ⟨((-784476753/2251799813685248), (-767491571/2251799813685248)), (121/2251799813685248), by norm_num⟩
  | 13 => ⟨((216245177/4503599627370496), (423126243/9007199254740992)), (135/18014398509481984), by norm_num⟩
  | 14 => ⟨((-885621357/144115188075855872), (-108305779/18014398509481984)), (35/36028797018963968), by norm_num⟩
  | 15 => ⟨((423152121/576460752303423488), (827980395/1152921504606846976)), (17/144115188075855872), by norm_num⟩
  | 16 => ⟨((-189546705/2305843009213693952), (-741770857/9223372036854775808)), (31/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-385432746897/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889789077798945/316912650057057350374175801344), (-3652304144069/633825300114114700748351602688)), (46281/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118165743812033/2475880078570760549798248448), (-4108265069007/39614081257132168796771975168)), (52077/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890483217535057/2475880078570760549798248448), (-4364341516515/2475880078570760549798248448)), (55345/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772148753013787/154742504910672534362390528), (-4363565114453/154742504910672534362390528)), (865/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((193806356692975/1208925819614629174706176), (-4090017411711/9671406556917033397649408)), (12979/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157446646906879/75557863725914323419136), (-1788970200829/302231454903657293676544)), (45443/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889065423323907/75557863725914323419136), (-726575836887/9444732965739290427392)), (73873/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298493244440267/4722366482869645213696), (-2179050988263/2361183241434822606848)), (55431/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622757559030317/590295810358705651712), (-2995095859201/295147905179352825856)), (76261/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825108397883681/73786976294838206464), (-7484442247285/73786976294838206464)), (95389/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912245362442661/4611686018427387904), (-262983255309/288230376151711744)), (107401/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797867009019399/576460752303423488), (-4204899163293/576460752303423488)), (107511/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196104543975433/144115188075855872), (-7352200642073/144115188075855872)), (23549/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493911380794089/36028797018963968), (-11015558140681/36028797018963968)), (141541/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492079739626625/9007199254740992), (-13747154448625/9007199254740992)), (177361/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116765569656671/2251799813685248), (-6856864066909/1125899906842624)), (178013/2251799813685248), by norm_num⟩
  | 1 => ⟨((556081580470883/562949953421312), (-10243537106277/562949953421312)), (268653/1125899906842624), by norm_num⟩
  | 0 => ⟨((137285878210077/140737488355328), (-20320183457637/562949953421312)), (33991/70368744177664), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137285878210077/140737488355328), (-20320183457637/562949953421312)), (129665375024294831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((534942202248419/562949953421312), (-79287310409529/1125899906842624)), (1100299/1125899906842624), by norm_num⟩
  | 2 => ⟨((1011072258266645/1125899906842624), (-150685254286129/1125899906842624)), (561521/281474976710656), by norm_num⟩
  | 3 => ⟨((221947141904519/281474976710656), (-270634502077201/1125899906842624)), (1158809/281474976710656), by norm_num⟩
  | 4 => ⟨((317490703540271/562949953421312), (-853597075501787/2251799813685248)), (19076525/2251799813685248), by norm_num⟩
  | 5 => ⟨((196326861889137/1125899906842624), (-120352233086587/281474976710656)), (8995059/562949953421312), by norm_num⟩
  | 6 => ⟨((-343210479491799/2251799813685248), (-671558843897617/4503599627370496)), (43316629/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1133571553/33554432)), (1/33554432), by norm_num⟩, -5, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1231096265/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((111863428558925/1125899906842624), (355890502473651/2251799813685248)), (107453261/4503599627370496), by norm_num⟩
  | 1 => ⟨((-207592183/1073741824), (-165112243/536870912)), (101/2147483648), by norm_num⟩
  | 2 => ⟨((50494467/268435456), (642587179/2147483648)), (199/4294967296), by norm_num⟩
  | 3 => ⟨((-131010261/1073741824), (-208402819/1073741824)), (131/4294967296), by norm_num⟩
  | 4 => ⟨((509868393/8589934592), (811066321/8589934592)), (129/8589934592), by norm_num⟩
  | 5 => ⟨((-793726465/34359738368), (-1262609749/34359738368)), (203/34359738368), by norm_num⟩
  | 6 => ⟨((8044377/1073741824), (409487521/34359738368)), (133/68719476736), by norm_num⟩
  | 7 => ⟨((-572475789/274877906944), (-455329099/137438953472)), (75/137438953472), by norm_num⟩
  | 8 => ⟨((69624153/137438953472), (886029515/1099511627776)), (147/1099511627776), by norm_num⟩
  | 9 => ⟨((-7526797/68719476736), (-191570425/1099511627776)), (129/4398046511104), by norm_num⟩
  | 10 => ⟨((374949649/17592186044416), (596446135/17592186044416)), (203/35184372088832), by norm_num⟩
  | 11 => ⟨((-530631511/140737488355328), (-844094973/140737488355328)), (145/140737488355328), by norm_num⟩
  | 12 => ⟨((344187081/562949953421312), (1095021983/1125899906842624)), (95/562949953421312), by norm_num⟩
  | 13 => ⟨((-824316473/9007199254740992), (-655635197/4503599627370496)), (229/9007199254740992), by norm_num⟩
  | 14 => ⟨((458298797/36028797018963968), (729032677/36028797018963968)), (129/36028797018963968), by norm_num⟩
  | 15 => ⟨((-475631083/288230376151711744), (-756603779/288230376151711744)), (135/288230376151711744), by norm_num⟩
  | 16 => ⟨((115691919/576460752303423488), (368070743/1152921504606846976)), (133/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (657547981521/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779378870607059/633825300114114700748351602688), (389341385503/158456325028528675187087900672)), (46177/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945214038364141/19807040628566084398385987584), (1751776122759/39614081257132168796771975168)), (103907/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236280734269857/309485009821345068724781056), (1860943330011/2475880078570760549798248448)), (110413/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221488992253523/19342813113834066795298816), (930292383111/77371252455336267181195264)), (55213/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387557350164633/2417851639229258349412352), (108994833151/604462909807314587353088)), (51769/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259379964861617/604462909807314587353088), (381386718265/151115727451828646838272)), (90609/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888752507486595/75557863725914323419136), (154893743205/4722366482869645213696)), (147265/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81141217289543/295147905179352825856), (464525142231/1180591620717411303424)), (13809/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622437620659497/590295810358705651712), (2553874099889/590295810358705651712)), (151935/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824710711499365/73786976294838206464), (3190822025869/73786976294838206464)), (47493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824046399803203/9223372036854775808), (3587585051221/9223372036854775808)), (106897/4611686018427387904), by norm_num⟩
  | 6 => ⟨((6231615344883/4503599627370496), (1792487267083/576460752303423488)), (1671/9007199254740992), by norm_num⟩
  | 5 => ⟨((1195723423610213/144115188075855872), (195869883953/9007199254740992)), (93629/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493348300124765/36028797018963968), (4695013706517/36028797018963968)), (140549/18014398509481984), by norm_num⟩
  | 3 => ⟨((372847725398285/2251799813685248), (5858518672633/9007199254740992)), (351743/9007199254740992), by norm_num⟩
  | 2 => ⟨((558049588469005/1125899906842624), (5843171313211/2251799813685248)), (352299/2251799813685248), by norm_num⟩
  | 1 => ⟨((138902428361217/140737488355328), (4363238555075/562949953421312)), (1059687/2251799813685248), by norm_num⟩
  | 0 => ⟨((2193242861895669/2251799813685248), (34600730098343/2251799813685248)), (266321/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193242861895669/2251799813685248), (34600730098343/2251799813685248)), (1015933991552257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1067838493347787/1125899906842624), (67401910101745/2251799813685248)), (1053951/562949953421312), by norm_num⟩
  | 2 => ⟨((1011762490236317/1125899906842624), (127852136223457/2251799813685248)), (8249179/2251799813685248), by norm_num⟩
  | 3 => ⟨((905566106070815/1125899906842624), (229782407727935/2251799813685248)), (3940647/562949953421312), by norm_num⟩
  | 4 => ⟨((1433253486984659/2251799813685248), (184814972401315/1125899906842624)), (14286393/1125899906842624), by norm_num⟩
  | 5 => ⟨((851580700115879/2251799813685248), (470533307679159/2251799813685248)), (22876547/1125899906842624), by norm_num⟩
  | 6 => ⟨((111863428558925/1125899906842624), (355890502473651/2251799813685248)), (107453261/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1231096265/33554432)), (1/16777216), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-328894003/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((46939964082461/4503599627370496), (-1495618263949249/9007199254740992)), (58846813/2251799813685248), by norm_num⟩
  | 1 => ⟨((-11635889/536870912), (1482987761/4294967296)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((24196151/1073741824), (-770946589/2147483648)), (31/536870912), by norm_num⟩
  | 3 => ⟨((-67085975/4294967296), (1068758909/4294967296)), (87/2147483648), by norm_num⟩
  | 4 => ⟨((34875341/4294967296), (-1111210837/8589934592)), (183/8589934592), by norm_num⟩
  | 5 => ⟨((-116033973/34359738368), (1848558381/34359738368)), (307/34359738368), by norm_num⟩
  | 6 => ⟨((80428621/68719476736), (-640661515/34359738368)), (215/68719476736), by norm_num⟩
  | 7 => ⟨((-95569495/274877906944), (761267525/137438953472)), (129/137438953472), by norm_num⟩
  | 8 => ⟨((99365589/1099511627776), (-395752829/274877906944)), (135/549755813888), by norm_num⟩
  | 9 => ⟨((-11479163/549755813888), (1463013107/4398046511104)), (63/1099511627776), by norm_num⟩
  | 10 => ⟨((76384795/17592186044416), (-304225023/4398046511104)), (53/4398046511104), by norm_num⟩
  | 11 => ⟨((-115518339/140737488355328), (57510741/4398046511104)), (323/140737488355328), by norm_num⟩
  | 12 => ⟨((80071211/562949953421312), (-1275629055/562949953421312)), (113/281474976710656), by norm_num⟩
  | 13 => ⟨((-6403977/281474976710656), (1632366799/4503599627370496)), (73/1125899906842624), by norm_num⟩
  | 14 => ⟨((121752647/36028797018963968), (-1939663619/36028797018963968)), (175/18014398509481984), by norm_num⟩
  | 15 => ⟨((-67514003/144115188075855872), (1075577895/144115188075855872)), (49/36028797018963968), by norm_num⟩
  | 16 => ⟨((70195711/1152921504606846976), (-559150339/576460752303423488)), (103/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-491119955591/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889599815233365/316912650057057350374175801344), (-2325938284019/633825300114114700748351602688)), (92429/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890226371104759/39614081257132168796771975168), (-2616264293699/39614081257132168796771975168)), (51999/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945015741051345/1237940039285380274899124224), (-1389635895133/1237940039285380274899124224)), (55257/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221462182030467/19342813113834066795298816), (-2778699260273/154742504910672534362390528)), (110533/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550028228718587/9671406556917033397649408), (-2604422371319/9671406556917033397649408)), (51823/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259203844225085/604462909807314587353088), (-2278261533593/604462909807314587353088)), (90711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888466133138251/75557863725914323419136), (-3701035220323/75557863725914323419136)), (73721/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162255567501519/590295810358705651712), (-2774779420591/4722366482869645213696)), (110615/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811070914922479/295147905179352825856), (-953425539995/147573952589676412928)), (76075/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456085148520343/18446744073709551616), (-4764699387481/73786976294838206464)), (190269/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823629497600929/9223372036854775808), (-5356949509915/9223372036854775808)), (53541/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594875977272991/1152921504606846976), (-5352780325999/1152921504606846976)), (6697/36028797018963968), by norm_num⟩
  | 5 => ⟨((1195357338365147/144115188075855872), (-1169748952611/36028797018963968)), (93837/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492797720569177/36028797018963968), (-7009128155479/36028797018963968)), (281827/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490700146852179/9007199254740992), (-4372519665525/4503599627370496)), (352837/9007199254740992), by norm_num⟩
  | 2 => ⟨((557702323511617/1125899906842624), (-17441041494399/4503599627370496)), (88417/562949953421312), by norm_num⟩
  | 1 => ⟨((2220336529666019/2251799813685248), (-6509808273271/562949953421312)), (1065169/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188964122026547/2251799813685248), (-6448841319713/281474976710656)), (536763/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2188964122026547/2251799813685248), (-6448841319713/281474976710656)), (2047588350536155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2126699849132041/2251799813685248), (-100302218282125/2251799813685248)), (4272661/2251799813685248), by norm_num⟩
  | 2 => ⟨((2004082106179941/2251799813685248), (-23682468484965/281474976710656)), (8451219/2251799813685248), by norm_num⟩
  | 3 => ⟨((883837468156119/1125899906842624), (-84308757878817/562949953421312)), (2058143/281474976710656), by norm_num⟩
  | 4 => ⟨((1337129169159011/2251799813685248), (-66182827313633/281474976710656)), (15391087/1125899906842624), by norm_num⟩
  | 5 => ⟨((83687709574309/281474976710656), (-628794715129803/2251799813685248)), (25516369/1125899906842624), by norm_num⟩
  | 6 => ⟨((46939964082461/4503599627370496), (-1495618263949249/9007199254740992)), (58846813/2251799813685248), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-328894003/8388608)), (1/16777216), by norm_num⟩, -6, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile009Terms0
