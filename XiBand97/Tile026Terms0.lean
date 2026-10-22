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
namespace Reinmann.XiBand97.Tile026Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (30041/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (30041/1280))
  have he : value ((69/80), (30041/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1091716223/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1049395800476473/2251799813685248), (328868584078159/1125899906842624)), (853691/35184372088832), by norm_num⟩
  | 1 => ⟨((693689099/2147483648), (-434788383/2147483648)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((-480828643/4294967296), (150686171/2147483648)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((888760049/34359738368), (-557054371/34359738368)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((-308020761/68719476736), (772241333/274877906944)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((683211911/1099511627776), (-214110761/549755813888)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((-78927735/1099511627776), (395760721/8796093022208)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((250096169/35184372088832), (-627018121/140737488355328)), (17/35184372088832), by norm_num⟩
  | 8 => ⟨((-346706909/562949953421312), (434615843/1125899906842624)), (49/1125899906842624), by norm_num⟩
  | 9 => ⟨((854467259/18014398509481984), (-267780219/9007199254740992)), (63/18014398509481984), by norm_num⟩
  | 10 => ⟨((-473817257/144115188075855872), (148488883/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 11 => ⟨((955418461/4611686018427387904), (-598834331/4611686018427387904)), (75/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-441497075/36893488147419103232), (276720219/36893488147419103232)), (71/73786976294838206464), by norm_num⟩
  | 13 => ⟨((376643019/590295810358705651712), (-236071187/590295810358705651712)), (63/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-1193458499/37778931862957161709568), (748032355/37778931862957161709568)), (51/18889465931478580854784), by norm_num⟩
  | 15 => ⟨((882391887/604462909807314587353088), (-69132869/75557863725914323419136)), (39/302231454903657293676544), by norm_num⟩
  | 16 => ⟨((-1223254897/19342813113834066795298816), (191677013/4835703278458516698824704)), (111/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (3362973997487/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((445259986288003/158456325028528675187087900672), (498700603507/79228162514264337593543950336)), (23149/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892296155250239/39614081257132168796771975168), (2244021034547/19807040628566084398385987584)), (26049/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946114972071147/1237940039285380274899124224), (4768251061687/2475880078570760549798248448)), (6921/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221736893650095/19342813113834066795298816), (4767920536005/154742504910672534362390528)), (6923/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552087748778165/9671406556917033397649408), (4469574153605/9671406556917033397649408)), (12985/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157625638407489/75557863725914323419136), (3910525849607/604462909807314587353088)), (22733/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472847913453023/18889465931478580854784), (397121561437/4722366482869645213696)), (9239/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((325059335094867/1180591620717411303424), (1191220315067/1180591620717411303424)), (6933/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812577376453717/295147905179352825856), (1637693148285/147573952589676412928)), (19077/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828103482239869/73786976294838206464), (2046763934563/18446744073709551616)), (47727/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827858257288923/9223372036854775808), (1151062106323/1152921504606846976)), (53741/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599099126309995/1152921504606846976), (4603033816805/576460752303423488)), (6725/144115188075855872), by norm_num⟩
  | 5 => ⟨((1199046283462743/144115188075855872), (2013142996409/36028797018963968)), (47143/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498318521796079/36028797018963968), (12073372791883/36028797018963968)), (70849/36028797018963968), by norm_num⟩
  | 3 => ⟨((374394769788243/2251799813685248), (7541046325189/4503599627370496)), (88797/9007199254740992), by norm_num⟩
  | 2 => ⟨((561125247302447/1125899906842624), (7533804601193/1125899906842624)), (1393/35184372088832), by norm_num⟩
  | 1 => ⟨((280088597983957/281474976710656), (2820629505061/140737488355328)), (134617/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114524147878353/1125899906842624), (44983549314505/1125899906842624)), (272795/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114524147878353/1125899906842624), (44983549314505/1125899906842624)), (1040630344871139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1101466079673797/1125899906842624), (89058097728931/1125899906842624)), (561877/1125899906842624), by norm_num⟩
  | 2 => ⟨((535259028167475/562949953421312), (10890674336649/70368744177664)), (37133/35184372088832), by norm_num⟩
  | 3 => ⟨((990892320495879/1125899906842624), (331359146998875/1125899906842624)), (1313709/562949953421312), by norm_num⟩
  | 4 => ⟨((193638151406247/281474976710656), (291625598414003/562949953421312)), (6171255/1125899906842624), by norm_num⟩
  | 5 => ⟨((57676037341449/281474976710656), (802484717320739/1125899906842624)), (29769445/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1049395800476473/2251799813685248), (328868584078159/1125899906842624)), (853691/35184372088832), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1091716223/67108864)), (1/67108864), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1730329275/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((694357833126771/2251799813685248), (-529141541634213/2251799813685248)), (44863521/2251799813685248), by norm_num⟩
  | 1 => ⟨((-727491425/2147483648), (554391289/2147483648)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((199807755/1073741824), (-609061083/4294967296)), (7/536870912), by norm_num⟩
  | 3 => ⟨((-585363347/8589934592), (446081327/8589934592)), (85/17179869184), by norm_num⟩
  | 4 => ⟨((643087367/34359738368), (-122517607/8589934592)), (49/34359738368), by norm_num⟩
  | 5 => ⟨((-1130405895/274877906944), (861435831/274877906944)), (89/274877906944), by norm_num⟩
  | 6 => ⟨((413959269/549755813888), (-157730665/274877906944)), (67/1099511627776), by norm_num⟩
  | 7 => ⟨((-519749417/4398046511104), (198039825/2199023255552)), (87/8796093022208), by norm_num⟩
  | 8 => ⟨((1142006193/70368744177664), (-435137971/35184372088832)), (49/35184372088832), by norm_num⟩
  | 9 => ⟨((-1115219589/562949953421312), (849862973/562949953421312)), (49/281474976710656), by norm_num⟩
  | 10 => ⟨((245038789/1125899906842624), (-746935925/4503599627370496)), (89/4503599627370496), by norm_num⟩
  | 11 => ⟨((-783134909/36028797018963968), (596794899/36028797018963968)), (73/36028797018963968), by norm_num⟩
  | 12 => ⟨((1147148847/576460752303423488), (-874194947/576460752303423488)), (55/288230376151711744), by norm_num⟩
  | 13 => ⟨((-387775945/2305843009213693952), (2308657/18014398509481984)), (77/4611686018427387904), by norm_num⟩
  | 14 => ⟨((121718691/9223372036854775808), (-742054459/73786976294838206464)), (99/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-1141091411/1180591620717411303424), (108697353/147573952589676412928)), (59/590295810358705651712), by norm_num⟩
  | 16 => ⟨((626808523/9444732965739290427392), (-477664991/9444732965739290427392)), (67/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-848227120957/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890253808483885/316912650057057350374175801344), (-251424975247/158456325028528675187087900672)), (23075/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891697811076477/39614081257132168796771975168), (-70707256981/2475880078570760549798248448)), (25961/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945797420962577/1237940039285380274899124224), (-1201907087771/2475880078570760549798248448)), (27585/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773260765185069/154742504910672534362390528), (-1201776287425/154742504910672534362390528)), (55175/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775746888360129/4835703278458516698824704), (-281631577773/2417851639229258349412352)), (51731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630243072258681/302231454903657293676544), (-492785791479/302231454903657293676544)), (45269/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945274884652293/37778931862957161709568), (-1601293351847/75557863725914323419136)), (36785/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649803588944049/2361183241434822606848), (-1200742142857/4722366482869645213696)), (55185/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624290311583595/590295810358705651712), (-1650650232165/590295810358705651712)), (75891/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913512988849471/36893488147419103232), (-128922350129/4611686018427387904)), (2965/2305843009213693952), by norm_num⟩
  | 7 => ⟨((913325126386349/4611686018427387904), (-2319839135115/9223372036854775808)), (26691/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597896354373227/1152921504606846976), (-579721375191/288230376151711744)), (106795/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197999741179709/144115188075855872), (-2027952420803/144115188075855872)), (93479/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496760465959195/36028797018963968), (-11874160007/140737488355328)), (70143/18014398509481984), by norm_num⟩
  | 3 => ⟨((747826032726379/4503599627370496), (-3795982289203/9007199254740992)), (175477/9007199254740992), by norm_num⟩
  | 2 => ⟨((560177137807553/1125899906842624), (-3790363933923/2251799813685248)), (175655/2251799813685248), by norm_num⟩
  | 1 => ⟨((2235173823807005/2251799813685248), (-2835758775493/562949953421312)), (527859/2251799813685248), by norm_num⟩
  | 0 => ⟨((1109295749235101/1125899906842624), (-5643513419465/562949953421312)), (1059303/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109295749235101/1125899906842624), (-5643513419465/562949953421312)), (4040920266158293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1092823309442005/1125899906842624), (-22241143849171/1125899906842624)), (1054301/1125899906842624), by norm_num⟩
  | 2 => ⟨((2120558159610753/2251799813685248), (-5396936326069/140737488355328)), (1044155/562949953421312), by norm_num⟩
  | 3 => ⟨((996827157780841/1125899906842624), (-162636373533265/2251799813685248)), (2046679/562949953421312), by norm_num⟩
  | 4 => ⟨((876678050146055/1125899906842624), (-143991799800023/1125899906842624)), (15678961/2251799813685248), by norm_num⟩
  | 5 => ⟨((1328414294473815/2251799813685248), (-448474858265887/2251799813685248)), (28427115/2251799813685248), by norm_num⟩
  | 6 => ⟨((694357833126771/2251799813685248), (-529141541634213/2251799813685248)), (44863521/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1730329275/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1091716223/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((593847960746631/4503599627370496), (-1226088780868875/4503599627370496)), (45556691/2251799813685248), by norm_num⟩
  | 1 => ⟨((-392555275/2147483648), (810489637/2147483648)), (31/1073741824), by norm_num⟩
  | 2 => ⟨((136049291/1073741824), (-561788607/2147483648)), (11/536870912), by norm_num⟩
  | 3 => ⟨((-502944973/8589934592), (1038405837/8589934592)), (21/2147483648), by norm_num⟩
  | 4 => ⟨((174307445/8589934592), (-359884039/8589934592)), (119/34359738368), by norm_num⟩
  | 5 => ⟨((-386626285/68719476736), (399124171/34359738368)), (17/17179869184), by norm_num⟩
  | 6 => ⟨((357318559/274877906944), (-737738117/274877906944)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((-141528201/549755813888), (584412681/1099511627776)), (103/2199023255552), by norm_num⟩
  | 8 => ⟨((196199747/4398046511104), (-202542001/2199023255552)), (73/8796093022208), by norm_num⟩
  | 9 => ⟨((-241769425/35184372088832), (998338965/70368744177664)), (23/17592186044416), by norm_num⟩
  | 10 => ⟨((536261745/562949953421312), (-553596671/281474976710656)), (13/70368744177664), by norm_num⟩
  | 11 => ⟨((-270333321/2251799813685248), (558143959/2251799813685248)), (107/4503599627370496), by norm_num⟩
  | 12 => ⟨((249841039/18014398509481984), (-1031669097/36028797018963968)), (101/36028797018963968), by norm_num⟩
  | 13 => ⟨((-426280891/288230376151711744), (880121263/288230376151711744)), (11/36028797018963968), by norm_num⟩
  | 14 => ⟨((337686169/2305843009213693952), (-1394408165/4611686018427387904)), (71/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-499341261/36893488147419103232), (1030965427/36893488147419103232)), (107/36893488147419103232), by norm_num⟩
  | 16 => ⟨((346116987/295147905179352825856), (-714610779/295147905179352825856)), (151/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-1458602388911/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445030856035539/158456325028528675187087900672), (-1728684047603/633825300114114700748351602688)), (23093/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891265573476225/39614081257132168796771975168), (-1944560882395/39614081257132168796771975168)), (12991/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891135561708351/2475880078570760549798248448), (-1032921826807/1237940039285380274899124224)), (27609/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886400726880593/77371252455336267181195264), (-1032779934119/77371252455336267181195264)), (55225/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551063139130719/9671406556917033397649408), (-1936160893659/9671406556917033397649408)), (51781/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260109303528221/604462909807314587353088), (-846919671585/302231454903657293676544)), (45317/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889937340704539/75557863725914323419136), (-2751923828499/75557863725914323419136)), (73653/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324786950565259/1180591620717411303424), (-128965531175/295147905179352825856)), (13813/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623658582183495/590295810358705651712), (-354554813229/73786976294838206464)), (75991/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826236184297725/73786976294838206464), (-3544343669219/73786976294838206464)), (95019/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825761554530503/9223372036854775808), (-3985730989913/9223372036854775808)), (53469/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597007430830005/1152921504606846976), (-1991831095275/576460752303423488)), (53495/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197221680345587/144115188075855872), (-1741689022979/72057594037927936)), (93675/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495592871063161/36028797018963968), (-5220416898353/36028797018963968)), (140629/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494191694550281/9007199254740992), (-3258694554107/4503599627370496)), (175991/9007199254740992), by norm_num⟩
  | 2 => ⟨((279723149242057/562949953421312), (-6505202651527/2251799813685248)), (88149/1125899906842624), by norm_num⟩
  | 1 => ⟨((2230782306283515/2251799813685248), (-9727378304615/1125899906842624)), (530433/2251799813685248), by norm_num⟩
  | 0 => ⟨((276222859875361/281474976710656), (-9666648326663/562949953421312)), (1067039/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276222859875361/281474976710656), (-9666648326663/562949953421312)), (4070430764205168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1083942994672149/1125899906842624), (-75890206011315/2251799813685248)), (266363/281474976710656), by norm_num⟩
  | 2 => ⟨((2084541579095707/2251799813685248), (-36531070244457/562949953421312)), (4246623/2251799813685248), by norm_num⟩
  | 3 => ⟨((960112276235389/1125899906842624), (-135270523410889/1125899906842624)), (8413535/2251799813685248), by norm_num⟩
  | 4 => ⟨((401242358660367/562949953421312), (-230704149365801/1125899906842624)), (16370979/2251799813685248), by norm_num⟩
  | 5 => ⟨((1049395800476455/2251799813685248), (-82217146019541/281474976710656)), (30045857/2251799813685248), by norm_num⟩
  | 6 => ⟨((593847960746631/4503599627370496), (-1226088780868875/4503599627370496)), (45556691/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1091716223/33554432)), (1/33554432), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1267443285/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((560388839009289/2251799813685248), (-10335665383763/562949953421312)), (36780333/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1720258795/4294967296), (7932001/268435456)), (59/4294967296), by norm_num⟩
  | 2 => ⟨((692162431/2147483648), (-102128505/4294967296)), (49/4294967296), by norm_num⟩
  | 3 => ⟨((-742661639/4294967296), (109579659/8589934592)), (55/8589934592), by norm_num⟩
  | 4 => ⟨((597633899/8589934592), (-88180829/17179869184)), (23/8589934592), by norm_num⟩
  | 5 => ⟨((-192370931/8589934592), (113537255/68719476736)), (61/68719476736), by norm_num⟩
  | 6 => ⟨((1651248371/274877906944), (-121820775/274877906944)), (17/68719476736), by norm_num⟩
  | 7 => ⟨((-379654533/274877906944), (112035985/1099511627776)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((611030399/2199023255552), (-90157481/4398046511104)), (53/4398046511104), by norm_num⟩
  | 9 => ⟨((-437073551/8796093022208), (128980327/35184372088832)), (39/17592186044416), by norm_num⟩
  | 10 => ⟨((562754195/70368744177664), (-83034331/140737488355328)), (13/35184372088832), by norm_num⟩
  | 11 => ⟨((-329351977/281474976710656), (97191709/1125899906842624)), (63/1125899906842624), by norm_num⟩
  | 12 => ⟨((353381039/2251799813685248), (-104282681/9007199254740992)), (69/9007199254740992), by norm_num⟩
  | 13 => ⟨((-1399987303/72057594037927936), (3227625/2251799813685248)), (35/36028797018963968), by norm_num⟩
  | 14 => ⟨((1287538653/576460752303423488), (-47494053/288230376151711744)), (33/288230376151711744), by norm_num⟩
  | 15 => ⟨((-1105180545/4611686018427387904), (81534645/4611686018427387904)), (29/2305843009213693952), by norm_num⟩
  | 16 => ⟨((889359735/36893488147419103232), (-131224949/73786976294838206464)), (3/2305843009213693952), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-47963166989/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827935787371/633825300114114700748351602688), (-28413111259/158456325028528675187087900672)), (46107/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890933281111235/39614081257132168796771975168), (-63921637113/19807040628566084398385987584)), (25935/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945391332527547/1237940039285380274899124224), (-135814241397/2475880078570760549798248448)), (55113/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443112185381363/38685626227668133590597632), (-135792604269/154742504910672534362390528)), (55113/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387683166822739/2417851639229258349412352), (-31820645483/2417851639229258349412352)), (51669/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259820336479493/604462909807314587353088), (-27837320027/151115727451828646838272)), (45211/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944734068123511/37778931862957161709568), (-180899506055/75557863725914323419136)), (18367/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298796219890955/4722366482869645213696), (-33909237835/1180591620717411303424)), (27551/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811587838863269/295147905179352825856), (-46609900715/147573952589676412928)), (37883/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825633335190799/73786976294838206464), (-232957733939/73786976294838206464)), (47355/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825084423005041/9223372036854775808), (-130975664749/4611686018427387904)), (106551/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399082910066181/288230376151711744), (-261793771067/1152921504606846976)), (53277/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196631870546615/144115188075855872), (-228892424305/144115188075855872)), (93239/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494711166173073/36028797018963968), (-171492352545/18014398509481984)), (69933/18014398509481984), by norm_num⟩
  | 3 => ⟨((373273705356309/2251799813685248), (-428112219407/9007199254740992)), (174847/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117803592494111/2251799813685248), (-427185660623/2251799813685248)), (43717/562949953421312), by norm_num⟩
  | 1 => ⟨((1113777254008165/1125899906842624), (-1276934211487/2251799813685248)), (65589/281474976710656), by norm_num⟩
  | 0 => ⟨((34429427753097/35184372088832), (-2535437358815/2251799813685248)), (524933/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((34429427753097/35184372088832), (-2535437358815/2251799813685248)), (2002460484031295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((269525100057247/281474976710656), (-4962069929651/2251799813685248)), (2057043/2251799813685248), by norm_num⟩
  | 2 => ⟨((2064649460179537/2251799813685248), (-1187851945055/281474976710656)), (3948491/2251799813685248), by norm_num⟩
  | 3 => ⟨((946506670799447/1125899906842624), (-17426045510625/2251799813685248)), (7273979/2251799813685248), by norm_num⟩
  | 4 => ⟨((795629305640871/1125899906842624), (-29298995800995/2251799813685248)), (12342569/2251799813685248), by norm_num⟩
  | 5 => ⟨((281024707596095/562949953421312), (-20704451206939/1125899906842624)), (17765207/2251799813685248), by norm_num⟩
  | 6 => ⟨((560388839009289/2251799813685248), (-10335665383763/562949953421312)), (36780333/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1267443285/33554432)), (1/33554432), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1411022749/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-169029294988657/2251799813685248), (898822231306947/4503599627370496)), (83295161/4503599627370496), by norm_num⟩
  | 1 => ⟨((288829651/2147483648), (-767933485/2147483648)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((-258756631/2147483648), (687976047/2147483648)), (33/1073741824), by norm_num⟩
  | 3 => ⟨((309086429/4294967296), (-821791731/4294967296)), (81/4294967296), by norm_num⟩
  | 4 => ⟨((-69226067/2147483648), (368113279/4294967296)), (147/17179869184), by norm_num⟩
  | 5 => ⟨((396916675/34359738368), (-527656363/17179869184)), (107/34359738368), by norm_num⟩
  | 6 => ⟨((-237059737/68719476736), (1260577713/137438953472)), (65/68719476736), by norm_num⟩
  | 7 => ⟨((60679147/68719476736), (-1290658317/549755813888)), (135/549755813888), by norm_num⟩
  | 8 => ⟨((-434889745/2199023255552), (1156274631/2199023255552)), (123/2199023255552), by norm_num⟩
  | 9 => ⟨((346319031/8796093022208), (-460392449/4398046511104)), (25/2199023255552), by norm_num⟩
  | 10 => ⟨((-496416323/70368744177664), (82491253/4398046511104)), (145/70368744177664), by norm_num⟩
  | 11 => ⟨((80859877/70368744177664), (-53747085/17592186044416)), (3/8796093022208), by norm_num⟩
  | 12 => ⟨((-193175267/1125899906842624), (1027219717/2251799813685248)), (117/2251799813685248), by norm_num⟩
  | 13 => ⟨((212999147/9007199254740992), (-1132634249/18014398509481984)), (131/18014398509481984), by norm_num⟩
  | 14 => ⟨((-436163701/144115188075855872), (1159661795/144115188075855872)), (17/18014398509481984), by norm_num⟩
  | 15 => ⟨((416800235/1152921504606846976), (-277044667/288230376151711744)), (33/288230376151711744), by norm_num⟩
  | 16 => ⟨((-93350721/2305843009213693952), (992794811/9223372036854775808)), (15/1152921504606846976), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (1257373438265/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111223783904303/39614081257132168796771975168), (1489335771347/316912650057057350374175801344)), (46247/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945327362297595/19807040628566084398385987584), (3350539331719/39614081257132168796771975168)), (52037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890486393424019/2475880078570760549798248448), (55615402217/38685626227668133590597632)), (13825/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886076063297629/77371252455336267181195264), (3558753202699/154742504910672534362390528)), (3457/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550454226224665/9671406556917033397649408), (3335659131671/9671406556917033397649408)), (51869/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629788168093279/302231454903657293676544), (1459014915467/302231454903657293676544)), (22699/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889070953040747/75557863725914323419136), (4740538829427/75557863725914323419136)), (18449/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298497735541711/4722366482869645213696), (444287764511/590295810358705651712)), (55369/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202845536568049/73786976294838206464), (4885374995297/590295810358705651712)), (38083/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825117651367105/73786976294838206464), (763004215925/9223372036854775808)), (23815/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824502284093651/9223372036854775808), (857918378583/1152921504606846976)), (107239/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595747011637745/1152921504606846976), (6858734861363/1152921504606846976)), (1677/18014398509481984), by norm_num⟩
  | 5 => ⟨((1196117524440499/144115188075855872), (2998103173345/72057594037927936)), (47007/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493934067068151/36028797018963968), (8983941289059/36028797018963968)), (70611/18014398509481984), by norm_num⟩
  | 3 => ⟨((93257106874173/562949953421312), (11211793657667/9007199254740992)), (176881/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116807929332391/2251799813685248), (2796154290625/562949953421312)), (177413/2251799813685248), by norm_num⟩
  | 1 => ⟨((556123785364869/562949953421312), (8354532466401/562949953421312)), (133725/562949953421312), by norm_num⟩
  | 0 => ⟨((1098538709056521/1125899906842624), (33147170404345/1125899906842624)), (270119/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098538709056521/1125899906842624), (33147170404345/1125899906842624)), (1030422212840843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((535433280108745/562949953421312), (4042705035719/70368744177664)), (1086029/1125899906842624), by norm_num⟩
  | 2 => ⟨((1014807138771931/1125899906842624), (61521598632543/562949953421312)), (547669/281474976710656), by norm_num⟩
  | 3 => ⟨((901229225033669/1125899906842624), (221805000965127/1125899906842624)), (4427857/1125899906842624), by norm_num⟩
  | 4 => ⟨((677694929153503/1125899906842624), (177544334015417/562949953421312)), (17666349/2251799813685248), by norm_num⟩
  | 5 => ⟨((295925466208455/1125899906842624), (854931378044795/2251799813685248)), (32410547/2251799813685248), by norm_num⟩
  | 6 => ⟨((-169029294988657/2251799813685248), (898822231306947/4503599627370496)), (83295161/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1411022749/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-95776091/2097152)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-97729687344591/4503599627370496), (-417521237064247/2251799813685248)), (138787713/9007199254740992), by norm_num⟩
  | 1 => ⟨((181363287/4294967296), (774821103/2147483648)), (131/4294967296), by norm_num⟩
  | 2 => ⟨((-88229165/2147483648), (-188466531/536870912)), (129/4294967296), by norm_num⟩
  | 3 => ⟨((14307169/536870912), (977970495/4294967296)), (85/4294967296), by norm_num⟩
  | 4 => ⟨((-222723723/17179869184), (-237880339/2147483648)), (167/17179869184), by norm_num⟩
  | 5 => ⟨((173360141/34359738368), (1481260051/34359738368)), (33/8589934592), by norm_num⟩
  | 6 => ⟨((-224895505/137438953472), (-1921599311/137438953472)), (173/137438953472), by norm_num⟩
  | 7 => ⟨((125036127/274877906944), (534179943/137438953472)), (49/137438953472), by norm_num⟩
  | 8 => ⟨((-60827267/549755813888), (-1039466173/1099511627776)), (97/1099511627776), by norm_num⟩
  | 9 => ⟨((210425593/8796093022208), (1797962467/8796093022208)), (85/4398046511104), by norm_num⟩
  | 10 => ⟨((-163787719/35184372088832), (-1399469365/35184372088832)), (67/17592186044416), by norm_num⟩
  | 11 => ⟨((57948397/70368744177664), (123783711/17592186044416)), (97/140737488355328), by norm_num⟩
  | 12 => ⟨((-18793729/140737488355328), (-642325279/562949953421312)), (1/8796093022208), by norm_num⟩
  | 13 => ⟨((180041393/9007199254740992), (1538347421/9007199254740992)), (155/9007199254740992), by norm_num⟩
  | 14 => ⟨((-200196785/72057594037927936), (-427640837/18014398509481984)), (87/36028797018963968), by norm_num⟩
  | 15 => ⟨((25970997/72057594037927936), (1775254709/576460752303423488)), (183/576460752303423488), by norm_num⟩
  | 16 => ⟨((-202148907/4611686018427387904), (-863621539/2305843009213693952)), (45/1152921504606846976), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-137368695049/633825300114114700748351602688)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779376545588065/633825300114114700748351602688), (-1301400221627/316912650057057350374175801344)), (46229/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890425327200423/39614081257132168796771975168), (-1463855973255/19807040628566084398385987584)), (3251/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1890242781625625/2475880078570760549798248448), (-3110160683291/2475880078570760549798248448)), (13819/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771908653056529/154742504910672534362390528), (-3109560857239/154742504910672534362390528)), (27643/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550226116637137/9671406556917033397649408), (-2914576097511/9671406556917033397649408)), (51843/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259376887100943/604462909807314587353088), (-318702125221/75557863725914323419136)), (22687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888747123423579/75557863725914323419136), (-517741669591/9444732965739290427392)), (73753/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298255103972879/4722366482869645213696), (-3105405290813/4722366482869645213696)), (27667/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622431064978441/590295810358705651712), (-2134117541201/295147905179352825856)), (38057/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456175425703021/18446744073709551616), (-5332748919137/73786976294838206464)), (95187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114002196687573/576460752303423488), (-5995844639073/9223372036854775808)), (107149/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595280879959419/1152921504606846976), (-46808393391/9007199254740992)), (107227/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597855394554475/72057594037927936), (-2618813177097/72057594037927936)), (11739/18014398509481984), by norm_num⟩
  | 4 => ⟨((746663110417785/18014398509481984), (-122603426293/562949953421312)), (35261/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491357844765263/9007199254740992), (-4895552392253/4503599627370496)), (176615/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232115928861691/4503599627370496), (-4882691519065/1125899906842624)), (177079/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222274653656535/2251799813685248), (-29167766006017/2251799813685248)), (266783/1125899906842624), by norm_num⟩
  | 0 => ⟨((274094187780177/281474976710656), (-57823353306831/2251799813685248)), (538235/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274094187780177/281474976710656), (-57823353306831/2251799813685248)), (2053203587058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2133770663006173/2251799813685248), (-56307119178321/1125899906842624)), (537943/562949953421312), by norm_num⟩
  | 2 => ⟨((504074035359587/562949953421312), (-106711509869489/1125899906842624)), (1073299/562949953421312), by norm_num⟩
  | 3 => ⟨((892597272678023/1125899906842624), (-95551125055287/562949953421312)), (8502197/2251799813685248), by norm_num⟩
  | 4 => ⟨((1350403915258839/2251799813685248), (-606012474873309/2251799813685248)), (8183523/1125899906842624), by norm_num⟩
  | 5 => ⟨((646744708740745/2251799813685248), (-90856391162199/281474976710656)), (28440147/2251799813685248), by norm_num⟩
  | 6 => ⟨((-97729687344591/4503599627370496), (-417521237064247/2251799813685248)), (138787713/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-95776091/2097152)), (1/33554432), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-818787167/16777216)), (3/33554432), by norm_num⟩
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
  | 0 => ⟨((162769870040149/9007199254740992), (23276495958497/140737488355328)), (173892787/4503599627370496), by norm_num⟩
  | 1 => ⟨((-80697639/2147483648), (-738557627/2147483648)), (347/4294967296), by norm_num⟩
  | 2 => ⟨((167806023/4294967296), (1535787411/4294967296)), (363/4294967296), by norm_num⟩
  | 3 => ⟨((-3634821/134217728), (-532263357/2147483648)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((120934365/8589934592), (138351317/1073741824)), (133/4294967296), by norm_num⟩
  | 5 => ⟨((-100590377/17179869184), (-920619123/17179869184)), (445/34359738368), by norm_num⟩
  | 6 => ⟨((2178873/1073741824), (1276249099/68719476736)), (311/68719476736), by norm_num⟩
  | 7 => ⟨((-20712407/34359738368), (-379126485/68719476736)), (93/68719476736), by norm_num⟩
  | 8 => ⟨((86140479/549755813888), (1576742725/1099511627776)), (389/1099511627776), by norm_num⟩
  | 9 => ⟨((-79610707/2199023255552), (-1457219699/4398046511104)), (181/2199023255552), by norm_num⟩
  | 10 => ⟨((132436649/17592186044416), (1212081271/17592186044416)), (303/17592186044416), by norm_num⟩
  | 11 => ⟨((-100143371/70368744177664), (-1833056107/140737488355328)), (461/140737488355328), by norm_num⟩
  | 12 => ⟨((138828191/562949953421312), (158822209/70368744177664)), (161/281474976710656), by norm_num⟩
  | 13 => ⟨((-88826187/2251799813685248), (-1625902765/4503599627370496)), (207/2251799813685248), by norm_num⟩
  | 14 => ⟨((52773961/9007199254740992), (482995679/9007199254740992)), (495/36028797018963968), by norm_num⟩
  | 15 => ⟨((-117056391/144115188075855872), (-535659349/72057594037927936)), (69/36028797018963968), by norm_num⟩
  | 16 => ⟨((121705961/1152921504606846976), (1113872303/1152921504606846976)), (289/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (1904371627987/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779199804808247/633825300114114700748351602688), (35230786877/9903520314283042199192993792)), (138633/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945113288609621/19807040628566084398385987584), (2536213365233/39614081257132168796771975168)), (155983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945015856963353/1237940039285380274899124224), (673558320735/618970019642690137449562112)), (165757/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771697702489069/154742504910672534362390528), (2693678307567/154742504910672534362390528)), (165785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550028474887799/9671406556917033397649408), (1262366939145/4835703278458516698824704)), (155453/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259204074927865/604462909807314587353088), (2208552750473/604462909807314587353088)), (136051/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236058317088307/9444732965739290427392), (3587793409335/75557863725914323419136)), (221137/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298044867759817/4722366482869645213696), (672469662447/1180591620717411303424)), (82951/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405535580300359/147573952589676412928), (3697013297303/590295810358705651712)), (114097/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57010664664565/2305843009213693952), (4618912841907/73786976294838206464)), (285361/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823630340936497/9223372036854775808), (5193042107553/9223372036854775808)), (160597/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594876925138777/1152921504606846976), (5189000968595/1152921504606846976)), (160699/576460752303423488), by norm_num⟩
  | 5 => ⟨((298839571280849/36028797018963968), (566979109931/18014398509481984)), (281453/144115188075855872), by norm_num⟩
  | 4 => ⟨((23324990232915/562949953421312), (6794671662479/36028797018963968)), (211319/18014398509481984), by norm_num⟩
  | 3 => ⟨((745351311692575/4503599627370496), (4238736148759/4503599627370496)), (529103/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115407734000015/2251799813685248), (16907417177077/4503599627370496)), (1060623/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220348825544443/2251799813685248), (12621283737701/1125899906842624)), (1596993/2251799813685248), by norm_num⟩
  | 0 => ⟨((1094500375136405/1125899906842624), (25006230743575/1125899906842624)), (1609145/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094500375136405/1125899906842624), (25006230743575/1125899906842624)), (6138401035789107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531710568728685/562949953421312), (48617694633873/1125899906842624)), (200001/70368744177664), by norm_num⟩
  | 2 => ⟨((2004620177159947/2251799813685248), (91839574395373/1125899906842624)), (6321241/1125899906842624), by norm_num⟩
  | 3 => ⟨((1769590707290673/2251799813685248), (163516723623355/1125899906842624)), (6142983/562949953421312), by norm_num⟩
  | 4 => ⟨((671573995461347/1125899906842624), (514002484327325/2251799813685248)), (45757271/2251799813685248), by norm_num⟩
  | 5 => ⟨((683829869008171/2251799813685248), (613181864531427/2251799813685248)), (37737875/1125899906842624), by norm_num⟩
  | 6 => ⟨((162769870040149/9007199254740992), (23276495958497/140737488355328)), (173892787/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-818787167/16777216)), (3/33554432), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile026Terms0
