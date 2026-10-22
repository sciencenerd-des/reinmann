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
namespace Reinmann.XiBand97.Tile037Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (33621/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (33621/1280))
  have he : value ((69/80), (33621/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1221816555/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((7743042162607/17592186044416), (185666349263201/562949953421312)), (62963685/2251799813685248), by norm_num⟩
  | 1 => ⟨((-655159649/2147483648), (-15341533/67108864)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((908244127/8589934592), (340286091/4294967296)), (61/8589934592), by norm_num⟩
  | 3 => ⟨((-26231119/1073741824), (-157245563/8589934592)), (29/17179869184), by norm_num⟩
  | 4 => ⟨((1163649675/274877906944), (871954549/274877906944)), (83/274877906944), by norm_num⟩
  | 5 => ⟨((-645264393/1099511627776), (-241757135/549755813888)), (3/68719476736), by norm_num⟩
  | 6 => ⟨((1192701853/17592186044416), (893724141/17592186044416)), (91/17592186044416), by norm_num⟩
  | 7 => ⟨((-118102561/17592186044416), (-353989925/70368744177664)), (37/70368744177664), by norm_num⟩
  | 8 => ⟨((654899657/1125899906842624), (490734237/1125899906842624)), (53/1125899906842624), by norm_num⟩
  | 9 => ⟨((-807007735/18014398509481984), (-604712983/18014398509481984)), (67/18014398509481984), by norm_num⟩
  | 10 => ⟨((447500109/144115188075855872), (670648159/288230376151711744)), (19/72057594037927936), by norm_num⟩
  | 11 => ⟨((-451175911/2305843009213693952), (-676156917/4611686018427387904)), (79/4611686018427387904), by norm_num⟩
  | 12 => ⟨((416975081/36893488147419103232), (624901681/73786976294838206464)), (75/73786976294838206464), by norm_num⟩
  | 13 => ⟨((-177861601/295147905179352825856), (-533106263/1180591620717411303424)), (33/590295810358705651712), by norm_num⟩
  | 14 => ⟨((281792611/9444732965739290427392), (52788729/2361183241434822606848)), (107/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-416690675/302231454903657293676544), (-624475455/604462909807314587353088)), (81/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((577655933/9671406556917033397649408), (432853401/9671406556917033397649408)), (57/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (104708888429/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781047897851141/633825300114114700748351602688), (124219541135/79228162514264337593543950336)), (46149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892305585151439/39614081257132168796771975168), (1117915264487/39614081257132168796771975168)), (51921/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892240551873157/2475880078570760549798248448), (1187712440223/2475880078570760549798248448)), (27585/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773906418876471/154742504910672534362390528), (74226928119/9671406556917033397649408)), (27587/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552099017285329/9671406556917033397649408), (278329309239/2417851639229258349412352)), (25865/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261015670243453/604462909807314587353088), (487032951501/302231454903657293676544)), (11317/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945705068274333/37778931862957161709568), (98918411269/4722366482869645213696)), (73569/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650126177636389/2361183241434822606848), (148359843605/590295810358705651712)), (3449/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1625177271167987/590295810358705651712), (1631727248671/590295810358705651712)), (4743/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1828134438216007/73786976294838206464), (1019656276341/36893488147419103232)), (47439/36893488147419103232), by norm_num⟩
  | 7 => ⟨((7140222430881/36028797018963968), (1146875117663/4611686018427387904)), (106761/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599142633258813/1152921504606846976), (2293154845691/1152921504606846976)), (106791/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599544886639947/72057594037927936), (1002920402547/72057594037927936)), (23369/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498394590393933/36028797018963968), (1503711079519/18014398509481984)), (17535/4503599627370496), by norm_num⟩
  | 3 => ⟨((1497693104795807/9007199254740992), (1878467543219/4503599627370496)), (43867/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122392891262789/2251799813685248), (3753422613481/2251799813685248)), (175643/2251799813685248), by norm_num⟩
  | 1 => ⟨((560319389130883/562949953421312), (2810678899097/562949953421312)), (263905/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115375266305211/1125899906842624), (11207641477103/1125899906842624)), (264787/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115375266305211/1125899906842624), (11207641477103/1125899906842624)), (1010082247020530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1104837442385379/1125899906842624), (11102875150095/562949953421312)), (1059791/1125899906842624), by norm_num⟩
  | 2 => ⟨((1083731041573685/1125899906842624), (43580684604035/1125899906842624)), (2121735/1125899906842624), by norm_num⟩
  | 3 => ⟨((2082909301747953/2251799813685248), (83896872948275/1125899906842624)), (8497583/2251799813685248), by norm_num⟩
  | 4 => ⟨((1914182775906669/2251799813685248), (310417606377783/2251799813685248)), (16986889/2251799813685248), by norm_num⟩
  | 5 => ⟨((1584393331745403/2251799813685248), (527752095772741/2251799813685248)), (33563411/2251799813685248), by norm_num⟩
  | 6 => ⟨((7743042162607/17592186044416), (185666349263201/562949953421312)), (62963685/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1221816555/67108864)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1936533423/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-729144842840515/2251799813685248), (240037168823211/1125899906842624)), (4848489/140737488355328), by norm_num⟩
  | 1 => ⟨((190984603/536870912), (-62872835/268435456)), (21/536870912), by norm_num⟩
  | 2 => ⟨((-839272127/4294967296), (552582953/4294967296)), (95/4294967296), by norm_num⟩
  | 3 => ⟨((1229379563/17179869184), (-202358141/4294967296)), (71/8589934592), by norm_num⟩
  | 4 => ⟨((-168826437/8589934592), (444626281/34359738368)), (5/2147483648), by norm_num⟩
  | 5 => ⟨((593519355/137438953472), (-390777517/137438953472)), (143/274877906944), by norm_num⟩
  | 6 => ⟨((-217349219/274877906944), (286208655/549755813888)), (107/1099511627776), by norm_num⟩
  | 7 => ⟨((34111789/274877906944), (-89837813/1099511627776)), (137/8796093022208), by norm_num⟩
  | 8 => ⟨((-1199220179/70368744177664), (789575403/70368744177664)), (153/70368744177664), by norm_num⟩
  | 9 => ⟨((585545789/281474976710656), (-771055325/562949953421312)), (19/70368744177664), by norm_num⟩
  | 10 => ⟨((-1029260479/4503599627370496), (169418171/1125899906842624)), (17/562949953421312), by norm_num⟩
  | 11 => ⟨((102796201/4503599627370496), (-270727105/18014398509481984)), (111/36028797018963968), by norm_num⟩
  | 12 => ⟨((-1204620477/576460752303423488), (793130999/576460752303423488)), (83/288230376151711744), by norm_num⟩
  | 13 => ⟨((814406683/4611686018427387904), (-536211361/4611686018427387904)), (57/2305843009213693952), by norm_num⟩
  | 14 => ⟨((-255633483/18446744073709551616), (673243875/73786976294838206464)), (73/36893488147419103232), by norm_num⟩
  | 15 => ⟨((599129783/590295810358705651712), (-49308933/73786976294838206464)), (87/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-329105671/4722366482869645213696), (216685599/4722366482869645213696)), (97/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (416726608815/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780499824015487/633825300114114700748351602688), (123522904087/19807040628566084398385987584)), (46295/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891688578579145/39614081257132168796771975168), (2223213334881/19807040628566084398385987584)), (26047/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236448057091193/309485009821345068724781056), (2361934475835/1237940039285380274899124224)), (13841/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886624866260821/77371252455336267181195264), (4723351985409/154742504910672534362390528)), (13845/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775741372932431/4835703278458516698824704), (2213796548751/4835703278458516698824704)), (51937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260475805011565/604462909807314587353088), (968398611343/151115727451828646838272)), (22731/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890531679011953/75557863725914323419136), (1573390091357/18889465931478580854784)), (73907/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299592483127939/4722366482869645213696), (1179817056071/1180591620717411303424)), (55459/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25379191808569/9223372036854775808), (6487527476431/590295810358705651712)), (38151/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913497844336113/36893488147419103232), (4053604485929/36893488147419103232)), (47723/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826612406860911/9223372036854775808), (4558791579259/4611686018427387904)), (6717/576460752303423488), by norm_num⟩
  | 6 => ⟨((1597853798861065/1152921504606846976), (9113797362095/1152921504606846976)), (107591/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197957212094727/144115188075855872), (1992577687721/36028797018963968)), (23569/36028797018963968), by norm_num⟩
  | 4 => ⟨((1496686099532383/36028797018963968), (11946934962141/36028797018963968)), (141681/36028797018963968), by norm_num⟩
  | 3 => ⟨((747770317391523/4503599627370496), (7459361414361/4503599627370496)), (88785/4503599627370496), by norm_num⟩
  | 2 => ⟨((560107597767947/1125899906842624), (7448135732883/1125899906842624)), (89137/1125899906842624), by norm_num⟩
  | 1 => ⟨((279327344188611/281474976710656), (22288165404527/1125899906842624)), (134587/562949953421312), by norm_num⟩
  | 0 => ⟨((1108466270460625/1125899906842624), (44350687672687/1125899906842624)), (545417/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1108466270460625/1125899906842624), (44350687672687/1125899906842624)), (2080600742820357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089555547341667/1125899906842624), (87327907317749/1125899906842624)), (1116913/1125899906842624), by norm_num⟩
  | 2 => ⟨((1047611000034811/1125899906842624), (21127234596417/140737488355328)), (583745/281474976710656), by norm_num⟩
  | 3 => ⟨((474696621888547/562949953421312), (314530600512661/1125899906842624)), (5046283/1125899906842624), by norm_num⟩
  | 4 => ⟨((712690380196379/1125899906842624), (530443648272923/1125899906842624)), (5664907/562949953421312), by norm_num⟩
  | 5 => ⟨((50305784878051/281474976710656), (671537643911051/1125899906842624)), (12509529/562949953421312), by norm_num⟩
  | 6 => ⟨((-729144842840515/2251799813685248), (240037168823211/1125899906842624)), (4848489/140737488355328), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1936533423/67108864)), (1/33554432), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1221816555/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((191289626127037/2251799813685248), (1307509929140189/4503599627370496)), (97872141/2251799813685248), by norm_num⟩
  | 1 => ⟨((-7903091/67108864), (-864312001/2147483648)), (131/2147483648), by norm_num⟩
  | 2 => ⟨((21912021/268435456), (1198190853/4294967296)), (23/536870912), by norm_num⟩
  | 3 => ⟨((-324016119/8589934592), (-553681741/4294967296)), (43/2147483648), by norm_num⟩
  | 4 => ⟨((449181719/34359738368), (1535131751/34359738368)), (241/34359738368), by norm_num⟩
  | 5 => ⟨((-124539617/34359738368), (-212814449/17179869184)), (135/68719476736), by norm_num⟩
  | 6 => ⟨((460396183/549755813888), (786729255/274877906944)), (63/137438953472), by norm_num⟩
  | 7 => ⟨((-364711219/2199023255552), (-623221903/1099511627776)), (101/1099511627776), by norm_num⟩
  | 8 => ⟨((252798553/8796093022208), (431984505/4398046511104)), (71/4398046511104), by norm_num⟩
  | 9 => ⟨((-311513963/70368744177664), (-532317941/35184372088832)), (177/70368744177664), by norm_num⟩
  | 10 => ⟨((43185005/70368744177664), (9224367/4398046511104)), (99/281474976710656), by norm_num⟩
  | 11 => ⟨((-348317841/4503599627370496), (-1190417497/4503599627370496)), (201/4503599627370496), by norm_num⟩
  | 12 => ⟨((321914039/36028797018963968), (68761211/2251799813685248)), (47/9007199254740992), by norm_num⟩
  | 13 => ⟨((-137313113/144115188075855872), (-938567671/288230376151711744)), (81/144115188075855872), by norm_num⟩
  | 14 => ⟨((217550165/2305843009213693952), (1487006937/4611686018427387904)), (259/4611686018427387904), by norm_num⟩
  | 15 => ⟨((-321694471/36893488147419103232), (-1099428977/36893488147419103232)), (193/36893488147419103232), by norm_num⟩
  | 16 => ⟨((445963231/590295810358705651712), (1524132191/590295810358705651712)), (135/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (104708888429/633825300114114700748351602688)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445030728727705/158456325028528675187087900672), (248194554521/79228162514264337593543950336)), (92395/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236408121318479/4951760157141521099596496896), (1116755336309/19807040628566084398385987584)), (103957/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891134883522645/2475880078570760549798248448), (296601905105/309485009821345068724781056)), (110469/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886400366660461/77371252455336267181195264), (1186244596111/77371252455336267181195264)), (110485/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387765604709747/2417851639229258349412352), (2223862230159/9671406556917033397649408)), (51799/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260108628412515/604462909807314587353088), (972766553911/302231454903657293676544)), (90665/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889936159567577/75557863725914323419136), (3160841999491/75557863725914323419136)), (147363/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299146842882997/4722366482869645213696), (2370063454963/4722366482869645213696)), (110551/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623657143633865/590295810358705651712), (3257914353287/590295810358705651712)), (152053/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57069818972893/2305843009213693952), (2035504451221/36893488147419103232)), (23767/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912879542167277/4611686018427387904), (1144495614983/2305843009213693952)), (106999/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798502326796041/576460752303423488), (2287802506843/576460752303423488)), (107059/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197218905272335/144115188075855872), (2000490394225/72057594037927936)), (187487/144115188075855872), by norm_num⟩
  | 4 => ⟨((747794009776397/18014398509481984), (1499031639325/9007199254740992)), (281499/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494184427013661/9007199254740992), (7485810889645/9007199254740992)), (352345/9007199254740992), by norm_num⟩
  | 2 => ⟨((69930220597373/140737488355328), (7471801506905/2251799813685248)), (88263/562949953421312), by norm_num⟩
  | 1 => ⟨((1115373069292325/1125899906842624), (5586359669201/562949953421312)), (265673/562949953421312), by norm_num⟩
  | 0 => ⟨((552418721192689/562949953421312), (11102875150095/562949953421312)), (133723/140737488355328), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552418721192689/562949953421312), (11102875150095/562949953421312)), (510112762988042787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1083731041573683/1125899906842624), (43580684604035/1125899906842624)), (1070871/562949953421312), by norm_num⟩
  | 2 => ⟨((1041454650873973/1125899906842624), (83896872948275/1125899906842624)), (536107/140737488355328), by norm_num⟩
  | 3 => ⟨((1914182775906657/2251799813685248), (155208803188891/1125899906842624)), (17147069/2251799813685248), by norm_num⟩
  | 4 => ⟨((1584393331745383/2251799813685248), (8246126496449/35184372088832)), (33879901/2251799813685248), by norm_num⟩
  | 5 => ⟨((495554698406835/1125899906842624), (742665397052787/2251799813685248)), (1986169/70368744177664), by norm_num⟩
  | 6 => ⟨((191289626127037/2251799813685248), (1307509929140189/4503599627370496)), (97872141/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1221816555/33554432)), (1/16777216), by norm_num⟩, -6, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1418485093/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-153873170739751/4503599627370496), (278309911959949/1125899906842624)), (185644763/4503599627370496), by norm_num⟩
  | 1 => ⟨((236176791/4294967296), (-1708688827/4294967296)), (287/4294967296), by norm_num⟩
  | 2 => ⟨((-190055941/4294967296), (687507145/2147483648)), (233/4294967296), by norm_num⟩
  | 3 => ⟨((101961079/4294967296), (-1475333419/8589934592)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((-82050013/8589934592), (1187228769/17179869184)), (51/4294967296), by norm_num⟩
  | 5 => ⟨((211287043/68719476736), (-764308397/34359738368)), (265/68719476736), by norm_num⟩
  | 6 => ⟨((-56675563/68719476736), (410035637/68719476736)), (143/137438953472), by norm_num⟩
  | 7 => ⟨((208493257/1099511627776), (-754202171/549755813888)), (265/1099511627776), by norm_num⟩
  | 8 => ⟨((-41944619/1099511627776), (37932549/137438953472)), (215/4398046511104), by norm_num⟩
  | 9 => ⟨((120012907/17592186044416), (-13566685/274877906944)), (155/17592186044416), by norm_num⟩
  | 10 => ⟨((-77261329/70368744177664), (69871159/8796093022208)), (201/140737488355328), by norm_num⟩
  | 11 => ⟨((90434409/562949953421312), (-1308547401/1125899906842624)), (237/1125899906842624), by norm_num⟩
  | 12 => ⟨((-194064755/9007199254740992), (702008599/4503599627370496)), (1/35184372088832), by norm_num⟩
  | 13 => ⟨((192206261/72057594037927936), (-695285695/36028797018963968)), (255/72057594037927936), by norm_num⟩
  | 14 => ⟨((-176768025/576460752303423488), (1278879037/576460752303423488)), (59/144115188075855872), by norm_num⟩
  | 15 => ⟨((151731819/4611686018427387904), (-548873709/2305843009213693952)), (205/4611686018427387904), by norm_num⟩
  | 16 => ⟨((-122101471/36893488147419103232), (1766756313/73786976294838206464)), (83/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (139065770117/633825300114114700748351602688)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444956057762145/158456325028528675187087900672), (659054261289/158456325028528675187087900672)), (23115/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890928896800415/39614081257132168796771975168), (1482686607197/19807040628566084398385987584)), (104033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945388866808279/1237940039285380274899124224), (3150262080033/2475880078570760549798248448)), (110555/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772443502986431/154742504910672534362390528), (3149759286457/154742504910672534362390528)), (6911/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775363715002701/4835703278458516698824704), (738091292389/2417851639229258349412352)), (12961/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314953856963953/151115727451828646838272), (2582785425587/604462909807314587353088)), (90751/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889459548817997/75557863725914323419136), (4196025018699/75557863725914323419136)), (18439/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298789245100213/4722366482869645213696), (3146142763873/4722366482869645213696)), (6917/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623165219905919/590295810358705651712), (4324523054221/590295810358705651712)), (152235/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825618962778845/73786976294838206464), (5403519393555/73786976294838206464)), (95193/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825066468122761/9223372036854775808), (3038012603905/4611686018427387904)), (26789/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1596311455634873/1152921504606846976), (6072358656043/1152921504606846976)), (107235/576460752303423488), by norm_num⟩
  | 5 => ⟨((299152926042965/36028797018963968), (5309190447063/144115188075855872)), (2935/2251799813685248), by norm_num⟩
  | 4 => ⟨((747337958030769/18014398509481984), (1988885663501/9007199254740992)), (282117/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493042028272327/9007199254740992), (9930011455621/9007199254740992)), (44159/1125899906842624), by norm_num⟩
  | 2 => ⟨((1117737744411327/2251799813685248), (4954201508631/1125899906842624)), (88553/562949953421312), by norm_num⟩
  | 1 => ⟨((1113645987250653/1125899906842624), (14808642511057/1125899906842624)), (533671/1125899906842624), by norm_num⟩
  | 0 => ⟨((550675015100413/562949953421312), (29401792169093/1125899906842624)), (1076775/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550675015100413/562949953421312), (29401792169093/1125899906842624)), (4107570652488326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1076567656035903/1125899906842624), (57521391549267/1125899906842624)), (135177/70368744177664), by norm_num⟩
  | 2 => ⟨((1026458214014591/1125899906842624), (110002086856507/1125899906842624)), (4357127/1125899906842624), by norm_num⟩
  | 3 => ⟨((462526020153059/562949953421312), (200572972653049/1125899906842624)), (4397995/562949953421312), by norm_num⟩
  | 4 => ⟨((724302182600339/1125899906842624), (659172050571635/2251799813685248)), (35175371/2251799813685248), by norm_num⟩
  | 5 => ⟨((738940826138743/2251799813685248), (848103374086009/2251799813685248)), (16462791/562949953421312), by norm_num⟩
  | 6 => ⟨((-153873170739751/4503599627370496), (278309911959949/1125899906842624)), (185644763/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1418485093/33554432)), (1/16777216), by norm_num⟩, -7, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1579174989/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-958519400704883/4503599627370496), (-58357280791461/4503599627370496)), (78162229/4503599627370496), by norm_num⟩
  | 1 => ⟨((818937403/2147483648), (99718295/4294967296)), (17/536870912), by norm_num⟩
  | 2 => ⟨((-1467338847/4294967296), (-5583475/268435456)), (31/1073741824), by norm_num⟩
  | 3 => ⟨((438186379/2147483648), (53355969/4294967296)), (75/4294967296), by norm_num⟩
  | 4 => ⟨((-392562297/4294967296), (-95601063/17179869184)), (17/2147483648), by norm_num⟩
  | 5 => ⟨((1125403541/34359738368), (17129411/8589934592)), (99/34359738368), by norm_num⟩
  | 6 => ⟨((-672150817/68719476736), (-40922379/68719476736)), (15/17179869184), by norm_num⟩
  | 7 => ⟨((172047513/68719476736), (83797783/549755813888)), (125/549755813888), by norm_num⟩
  | 8 => ⟨((-1233071043/2199023255552), (-2346023/68719476736)), (57/1099511627776), by norm_num⟩
  | 9 => ⟨((1963881527/17592186044416), (29891619/4398046511104)), (183/17592186044416), by norm_num⟩
  | 10 => ⟨((-1407521329/70368744177664), (-42846873/35184372088832)), (133/70368744177664), by norm_num⟩
  | 11 => ⟨((917068971/281474976710656), (27916833/140737488355328)), (11/35184372088832), by norm_num⟩
  | 12 => ⟨((-1095444675/2251799813685248), (-66693667/2251799813685248)), (107/2251799813685248), by norm_num⟩
  | 13 => ⟨((1207860535/18014398509481984), (18384463/4503599627370496)), (119/18014398509481984), by norm_num⟩
  | 14 => ⟨((-309170793/36028797018963968), (-75292653/144115188075855872)), (123/144115188075855872), by norm_num⟩
  | 15 => ⟨((1181780685/1152921504606846976), (71950039/1152921504606846976)), (119/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-1058733367/9223372036854775808), (-32229291/4611686018427387904)), (27/2305843009213693952), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-2006533202967/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889786604940717/316912650057057350374175801344), (-4753403538885/633825300114114700748351602688)), (46335/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472661512586513/9903520314283042199192993792), (-167087907067/1237940039285380274899124224)), (52141/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890476636960869/2475880078570760549798248448), (-2840044446581/1237940039285380274899124224)), (55417/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772141762815689/154742504910672534362390528), (-2839538114427/77371252455336267181195264)), (55437/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550443865215799/9671406556917033397649408), (-5323057930283/9671406556917033397649408)), (51993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629783312842267/302231454903657293676544), (-2328299783175/302231454903657293676544)), (45515/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944526982774797/37778931862957161709568), (-7564956378107/75557863725914323419136)), (4625/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((162310492340547/590295810358705651712), (-5671951419411/4722366482869645213696)), (27767/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202842950872079/73786976294838206464), (-7796063323877/590295810358705651712)), (76415/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825089224405317/73786976294838206464), (-9740773730887/73786976294838206464)), (95601/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824466773930887/9223372036854775808), (-10952449507605/9223372036854775808)), (53833/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595707095069185/1152921504606846976), (-684065429335/72057594037927936)), (107809/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598038824162121/72057594037927936), (-9568586044471/144115188075855872)), (47247/72057594037927936), by norm_num⟩
  | 4 => ⟨((746932187436463/18014398509481984), (-7000104581/17592186044416)), (8879/2251799813685248), by norm_num⟩
  | 3 => ⟨((1492009353686267/9007199254740992), (-8945546577229/4503599627370496)), (89073/4503599627370496), by norm_num⟩
  | 2 => ⟨((279169450596957/562949953421312), (-8923654770857/1125899906842624)), (44749/562949953421312), by norm_num⟩
  | 1 => ⟨((555994135952667/562949953421312), (-6665357617867/281474976710656)), (270623/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097765586250529/1125899906842624), (-6610535915083/140737488355328)), (137447/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1097765586250529/1125899906842624), (-6610535915083/140737488355328)), (524318696142101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1067850283318841/1125899906842624), (-51562799074043/562949953421312)), (280937/281474976710656), by norm_num⟩
  | 2 => ⟨((1003347927933199/1125899906842624), (-195617209896885/1125899906842624)), (2337477/1125899906842624), by norm_num⟩
  | 3 => ⟨((430074185899799/562949953421312), (-348649326685747/1125899906842624)), (155573/35184372088832), by norm_num⟩
  | 4 => ⟨((274579855968271/562949953421312), (-532711920225231/1125899906842624)), (21379525/2251799813685248), by norm_num⟩
  | 5 => ⟨((63218405671865/4503599627370496), (-259831200693883/562949953421312)), (82173919/4503599627370496), by norm_num⟩
  | 6 => ⟨((-958519400704883/4503599627370496), (-58357280791461/4503599627370496)), (78162229/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1579174989/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-214379545/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((278514950857719/2251799813685248), (-629733843764183/4503599627370496)), (24617061/1125899906842624), by norm_num⟩
  | 1 => ⟨((-516858167/2147483648), (292159433/1073741824)), (93/2147483648), by norm_num⟩
  | 2 => ⟨((1005759553/4294967296), (-284258003/1073741824)), (183/4294967296), by norm_num⟩
  | 3 => ⟨((-326186287/2147483648), (737520711/4294967296)), (15/536870912), by norm_num⟩
  | 4 => ⟨((317364603/4294967296), (-358787259/4294967296)), (119/8589934592), by norm_num⟩
  | 5 => ⟨((-988100803/34359738368), (558534215/17179869184)), (187/34359738368), by norm_num⟩
  | 6 => ⟨((160229615/17179869184), (-362285799/34359738368)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((-712668421/274877906944), (805686415/274877906944)), (69/137438953472), by norm_num⟩
  | 8 => ⟨((693394357/1099511627776), (-391948343/549755813888)), (17/137438953472), by norm_num⟩
  | 9 => ⟨((-599681385/4398046511104), (338976115/2199023255552)), (119/4398046511104), by norm_num⟩
  | 10 => ⟨((933540875/35184372088832), (-263846825/8796093022208)), (187/35184372088832), by norm_num⟩
  | 11 => ⟨((-660576969/140737488355328), (746795949/140737488355328)), (67/70368744177664), by norm_num⟩
  | 12 => ⟨((107118619/140737488355328), (-60549909/70368744177664)), (11/70368744177664), by norm_num⟩
  | 13 => ⟨((-513090973/4503599627370496), (580059975/4503599627370496)), (107/4503599627370496), by norm_num⟩
  | 14 => ⟨((285265409/18014398509481984), (-322498455/18014398509481984)), (15/4503599627370496), by norm_num⟩
  | 15 => ⟨((-296053789/144115188075855872), (167347471/72057594037927936)), (63/144115188075855872), by norm_num⟩
  | 16 => ⟨((576094073/2305843009213693952), (-651286285/2305843009213693952)), (31/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-1102770246599/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889689627741139/316912650057057350374175801344), (-652962381101/316912650057057350374175801344)), (92329/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236303566484395/4951760157141521099596496896), (-1468947559435/39614081257132168796771975168)), (51939/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945123193043191/1237940039285380274899124224), (-1560489490337/2475880078570760549798248448)), (27595/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885956240905705/77371252455336267181195264), (-390047216117/38685626227668133590597632)), (110391/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550229944284571/9671406556917033397649408), (-1462357720555/9671406556917033397649408)), (103503/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314845118586017/151115727451828646838272), (-1279243750089/604462909807314587353088)), (5661/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944376699373539/37778931862957161709568), (-1039086334757/37778931862957161709568)), (147207/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649130100234505/2361183241434822606848), (-1558106060233/4722366482869645213696)), (110425/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202804838233349/73786976294838206464), (-267693197005/73786976294838206464)), (18983/73786976294838206464), by norm_num⟩
  | 8 => ⟨((114044512673167/4611686018427387904), (-2675657173187/73786976294838206464)), (47469/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228006032820007/1152921504606846976), (-3008362429699/9223372036854775808)), (213673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12463247047351/9007199254740992), (-187885874973/72057594037927936)), (26719/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195725515094827/144115188075855872), (-1313971117095/72057594037927936)), (93561/72057594037927936), by norm_num⟩
  | 4 => ⟨((746675977542061/18014398509481984), (-1968499118881/18014398509481984)), (70215/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491396373768181/9007199254740992), (-2456328701021/4503599627370496)), (175693/4503599627370496), by norm_num⟩
  | 2 => ⟨((2232211998450049/4503599627370496), (-2449896945029/1125899906842624)), (703705/4503599627370496), by norm_num⟩
  | 1 => ⟨((555616508894529/562949953421312), (-1829402304937/281474976710656)), (264475/562949953421312), by norm_num⟩
  | 0 => ⟨((2193323872230609/2251799813685248), (-3626838505699/281474976710656)), (132825/140737488355328), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193323872230609/2251799813685248), (-3626838505699/281474976710656)), (506687164843511537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2135992607327753/2251799813685248), (-56522477189523/2251799813685248)), (4194791/2251799813685248), by norm_num⟩
  | 2 => ⟨((2024722446650161/2251799813685248), (-26807798963951/562949953421312)), (31909/8796093022208), by norm_num⟩
  | 3 => ⟨((453859445204635/562949953421312), (-192835444705951/2251799813685248)), (15467893/2251799813685248), by norm_num⟩
  | 4 => ⟨((1447121901105143/2251799813685248), (-310934168901269/2251799813685248)), (13795079/1125899906842624), by norm_num⟩
  | 5 => ⟨((110882510910173/281474976710656), (-399644446974669/2251799813685248)), (43081135/2251799813685248), by norm_num⟩
  | 6 => ⟨((278514950857719/2251799813685248), (-629733843764183/4503599627370496)), (24617061/1125899906842624), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-214379545/4194304)), (1/16777216), by norm_num⟩, -8, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1832724833/33554432)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((-525681245374825/9007199254740992), (1403334122948589/9007199254740992)), (391390965/9007199254740992), by norm_num⟩
  | 1 => ⟨((521241865/4294967296), (-86967685/268435456)), (391/4294967296), by norm_num⟩
  | 2 => ⟨((-270972997/2147483648), (180844217/536870912)), (409/4294967296), by norm_num⟩
  | 3 => ⟨((187824169/2147483648), (-1002813273/4294967296)), (143/2147483648), by norm_num⟩
  | 4 => ⟨((-97642345/2147483648), (1042645789/8589934592)), (75/2147483648), by norm_num⟩
  | 5 => ⟨((324866477/17179869184), (-867248387/17179869184)), (63/4294967296), by norm_num⟩
  | 6 => ⟨((-450360565/68719476736), (1202261549/68719476736)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((267570991/137438953472), (-714295031/137438953472)), (421/274877906944), by norm_num⟩
  | 8 => ⟨((-278199117/549755813888), (1485334761/1099511627776)), (441/1099511627776), by norm_num⟩
  | 9 => ⟨((128555289/1099511627776), (-686370401/2199023255552)), (205/2199023255552), by norm_num⟩
  | 10 => ⟨((-427717133/17592186044416), (285453425/4398046511104)), (343/17592186044416), by norm_num⟩
  | 11 => ⟨((323422827/70368744177664), (-107924311/8796093022208)), (261/70368744177664), by norm_num⟩
  | 12 => ⟨((-448359241/562949953421312), (598459455/281474976710656)), (91/140737488355328), by norm_num⟩
  | 13 => ⟨((286872871/2251799813685248), (-23931951/70368744177664)), (469/4503599627370496), by norm_num⟩
  | 14 => ⟨((-42609669/2251799813685248), (454995137/9007199254740992)), (281/18014398509481984), by norm_num⟩
  | 15 => ⟨((378045081/144115188075855872), (-252302877/36028797018963968)), (157/72057594037927936), by norm_num⟩
  | 16 => ⟨((-393061323/1152921504606846976), (1049298167/1152921504606846976)), (41/144115188075855872), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (1256506651443/5070602400912917605986812821504)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222399723646583/79228162514264337593543950336), (1487700149141/316912650057057350374175801344)), (138739/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59069506070095/1237940039285380274899124224), (418348669475/4951760157141521099596496896)), (78055/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945014516857291/1237940039285380274899124224), (3555312127403/2475880078570760549798248448)), (165899/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771694855546523/154742504910672534362390528), (1777289610899/77371252455336267181195264)), (10371/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550025628825731/9671406556917033397649408), (832909860085/2417851639229258349412352)), (38901/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259201407679945/604462909807314587353088), (1457203039359/302231454903657293676544)), (136193/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944230935446297/37778931862957161709568), (591806329291/9444732965739290427392)), (110693/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298041078538605/4722366482869645213696), (1774780726631/2361183241434822606848)), (20763/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811068320217719/295147905179352825856), (4878573241119/590295810358705651712)), (14281/36893488147419103232), by norm_num⟩
  | 8 => ⟨((456083365798161/18446744073709551616), (761888368965/9223372036854775808)), (285777/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911810295405331/4611686018427387904), (6852721304867/9223372036854775808)), (160857/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594865966506807/1152921504606846976), (6847381311137/1152921504606846976)), (321983/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195347339306767/144115188075855872), (374090914269/9007199254740992)), (141019/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492780248536811/36028797018963968), (8966182591675/36028797018963968)), (423663/36028797018963968), by norm_num⟩
  | 3 => ⟨((372668497846583/2251799813685248), (1398343615923/1125899906842624)), (530641/9007199254740992), by norm_num⟩
  | 2 => ⟨((278843011145665/562949953421312), (11155319076469/2251799813685248)), (133059/562949953421312), by norm_num⟩
  | 1 => ⟨((1110103335115209/1125899906842624), (16654540960977/1125899906842624)), (802351/1125899906842624), by norm_num⟩
  | 0 => ⟨((17098260063979/17592186044416), (16498076821339/562949953421312)), (810367/562949953421312), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((17098260063979/17592186044416), (16498076821339/562949953421312)), (3091304781200218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1062597912272975/1125899906842624), (32069739068761/562949953421312)), (202841/70368744177664), by norm_num⟩
  | 2 => ⟨((1998402244593811/2251799813685248), (242133337604887/2251799813685248)), (12991481/2251799813685248), by norm_num⟩
  | 3 => ⟨((1747483481481415/2251799813685248), (429771600849979/2251799813685248)), (6463247/562949953421312), by norm_num⟩
  | 4 => ⟨((39815302293373/70368744177664), (83379833403803/281474976710656)), (12498569/562949953421312), by norm_num⟩
  | 5 => ⟨((523298698708369/2251799813685248), (754833597998981/2251799813685248)), (86193549/2251799813685248), by norm_num⟩
  | 6 => ⟨((-525681245374825/9007199254740992), (1403334122948589/9007199254740992)), (391390965/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1832724833/33554432)), (3/33554432), by norm_num⟩, -9, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile037Terms0
