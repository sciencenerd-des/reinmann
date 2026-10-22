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
namespace Reinmann.XiBand97.Tile017Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (53817/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (53817/2560))
  have he : value ((69/80), (53817/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-22364231/8388608), (-272548875/4194304)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-684376535390333/18014398509481984), (-1049000920360937/18014398509481984)), (56885353/2251799813685248), by norm_num⟩
  | 1 => ⟨((252179733/2147483648), (773073763/4294967296)), (337/4294967296), by norm_num⟩
  | 2 => ⟨((-779498261/4294967296), (-1194801911/4294967296)), (523/4294967296), by norm_num⟩
  | 3 => ⟨((100394259/536870912), (1231061143/4294967296)), (541/4294967296), by norm_num⟩
  | 4 => ⟨((-620645833/4294967296), (-237828891/1073741824)), (105/1073741824), by norm_num⟩
  | 5 => ⟨((767377047/8589934592), (588111359/4294967296)), (521/8589934592), by norm_num⟩
  | 6 => ⟨((-395332505/8589934592), (-1211918119/17179869184)), (539/17179869184), by norm_num⟩
  | 7 => ⟨((349139873/17179869184), (535155765/17179869184)), (239/17179869184), by norm_num⟩
  | 8 => ⟨((-539603085/68719476736), (-413547297/34359738368)), (371/68719476736), by norm_num⟩
  | 9 => ⟨((185326227/68719476736), (1136259779/274877906944)), (1/536870912), by norm_num⟩
  | 10 => ⟨((-114570247/137438953472), (-702445443/549755813888)), (159/274877906944), by norm_num⟩
  | 11 => ⟨((515114905/2199023255552), (394779761/1099511627776)), (359/2199023255552), by norm_num⟩
  | 12 => ⟨((-530747347/8796093022208), (-813520667/8796093022208)), (93/2199023255552), by norm_num⟩
  | 13 => ⟨((504788487/35184372088832), (24179105/1099511627776)), (89/8796093022208), by norm_num⟩
  | 14 => ⟨((-222903235/70368744177664), (-683324709/140737488355328)), (79/35184372088832), by norm_num⟩
  | 15 => ⟨((91867115/140737488355328), (140812379/140737488355328)), (523/1125899906842624), by norm_num⟩
  | 16 => ⟨((-567930305/4503599627370496), (-870514083/4503599627370496)), (203/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-2799133251705/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777851962650759/633825300114114700748351602688), (-1654697715195/316912650057057350374175801344)), (46263/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944355191085249/19807040628566084398385987584), (-1861101748551/19807040628566084398385987584)), (104113/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236052611457269/309485009821345068724781056), (-1976882479885/1237940039285380274899124224)), (27661/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770087032294273/154742504910672534362390528), (-3952554585037/154742504910672534362390528)), (221343/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96782414581035/604462909807314587353088), (-3704234312529/9671406556917033397649408)), (207567/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257883125407455/604462909807314587353088), (-1619959938009/302231454903657293676544)), (11355/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943160148787879/37778931862957161709568), (-5262461131769/75557863725914323419136)), (147669/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648217727300707/2361183241434822606848), (-1972369624917/2361183241434822606848)), (221599/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619929811283875/590295810358705651712), (-2710297545187/295147905179352825856)), (304853/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455394070677493/18446744073709551616), (-3385307511855/36893488147419103232)), (381299/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820520627715079/9223372036854775808), (-7609894990961/9223372036854775808)), (214641/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591768335350753/1152921504606846976), (-7601094213657/1152921504606846976)), (429683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596319768253763/72057594037927936), (-6641067365279/144115188075855872)), (47053/18014398509481984), by norm_num⟩
  | 4 => ⟨((744361897907021/18014398509481984), (-9941847892961/36028797018963968)), (141385/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485612621240031/9007199254740992), (-12392802517667/9007199254740992)), (177127/2251799813685248), by norm_num⟩
  | 2 => ⟨((2220648958507013/4503599627370496), (-1542645338995/281474976710656)), (1421779/4503599627370496), by norm_num⟩
  | 1 => ⟨((2205133075104379/2251799813685248), (-36766136471835/2251799813685248)), (2144611/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158706950136027/2251799813685248), (-4531746326139/140737488355328)), (4337209/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2158706950136027/2251799813685248), (-4531746326139/140737488355328)), (16545139321334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2067127933281069/2251799813685248), (-69510351540385/1125899906842624)), (4297561/1125899906842624), by norm_num⟩
  | 2 => ⟨((944509167914063/1125899906842624), (-15952438183899/140737488355328)), (1052609/140737488355328), by norm_num⟩
  | 3 => ⟨((194469069757953/281474976710656), (-428236265727121/2251799813685248)), (16037409/1125899906842624), by norm_num⟩
  | 4 => ⟨((124177319684593/281474976710656), (-295865405890697/1125899906842624)), (56520195/2251799813685248), by norm_num⟩
  | 5 => ⟨((565534354215653/4503599627370496), (-1044207155328563/4503599627370496)), (155419/4398046511104), by norm_num⟩
  | 6 => ⟨((-684376535390333/18014398509481984), (-1049000920360937/18014398509481984)), (56885353/2251799813685248), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-272548875/4194304)), (1/8388608), by norm_num⟩, -10, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45371695/16777216), (-552936709/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-587573573337/8796093022208), (-70178764490781/18014398509481984)), (99844329/9007199254740992), by norm_num⟩
  | 1 => ⟨((224894231/1073741824), (104925685/8589934592)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-1410309121/4294967296), (-41124235/2147483648)), (237/4294967296), by norm_num⟩
  | 3 => ⟨((368501341/1073741824), (85963201/4294967296)), (125/2147483648), by norm_num⟩
  | 4 => ⟨((-1155433823/4294967296), (-8423035/536870912)), (197/4294967296), by norm_num⟩
  | 5 => ⟨((1449142427/8589934592), (10564151/1073741824)), (249/8589934592), by norm_num⟩
  | 6 => ⟨((-757296283/8589934592), (-88330225/17179869184)), (131/8589934592), by norm_num⟩
  | 7 => ⟨((678428033/17179869184), (79131117/34359738368)), (237/34359738368), by norm_num⟩
  | 8 => ⟨((-1063603587/68719476736), (-31014395/34359738368)), (47/17179869184), by norm_num⟩
  | 9 => ⟨((1482187953/274877906944), (86440405/274877906944)), (33/34359738368), by norm_num⟩
  | 10 => ⟨((-1858956701/1099511627776), (-27103339/274877906944)), (333/1099511627776), by norm_num⟩
  | 11 => ⟨((132471545/274877906944), (61805355/2199023255552)), (3/34359738368), by norm_num⟩
  | 12 => ⟨((-1107636701/8796093022208), (-32298389/4398046511104)), (203/8796093022208), by norm_num⟩
  | 13 => ⟨((1068611837/35184372088832), (62320869/35184372088832)), (99/17592186044416), by norm_num⟩
  | 14 => ⟨((-957321781/140737488355328), (-111660985/281474976710656)), (357/281474976710656), by norm_num⟩
  | 15 => ⟨((800447175/562949953421312), (93363299/1125899906842624)), (301/1125899906842624), by norm_num⟩
  | 16 => ⟨((-1254898743/4503599627370496), (-73185021/4503599627370496)), (119/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (-2008196765789/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888893349557727/316912650057057350374175801344), (-2374126443431/316912650057057350374175801344)), (23167/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888636637241043/39614081257132168796771975168), (-41722704853/309485009821345068724781056)), (52141/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944171050713421/1237940039285380274899124224), (-2836359696663/1237940039285380274899124224)), (110835/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770007751839473/154742504910672534362390528), (-708869394493/19342813113834066795298816)), (55437/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548443787457193/9671406556917033397649408), (-1328661600351/2417851639229258349412352)), (51993/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628908557695231/302231454903657293676544), (-1162110510853/151115727451828646838272)), (91029/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943106028772475/37778931862957161709568), (-7550206461327/75557863725914323419136)), (4625/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1296353423617013/4722366482869645213696), (-176861969725/147573952589676412928)), (111069/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619815637878133/590295810358705651712), (-7776936960847/590295810358705651712)), (152831/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910715749131937/36893488147419103232), (-4856845063925/36893488147419103232)), (191205/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820354907846195/9223372036854775808), (-10917620587759/9223372036854775808)), (26917/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591599077321159/1152921504606846976), (-85193578821/9007199254740992)), (215623/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74530466689907/9007199254740992), (-4763622362027/72057594037927936)), (188995/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488487783520747/36028797018963968), (-14262024167939/36028797018963968)), (284139/36028797018963968), by norm_num⟩
  | 3 => ⟨((742651916251053/4503599627370496), (-4444280266165/2251799813685248)), (356311/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109995161702201/2251799813685248), (-8850819708935/1125899906842624)), (89505/562949953421312), by norm_num⟩
  | 1 => ⟨((1102021697068763/1125899906842624), (-26364217918323/1125899906842624)), (270657/562949953421312), by norm_num⟩
  | 0 => ⟨((1078063072938325/1125899906842624), (-25989126830389/562949953421312)), (274961/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078063072938325/1125899906842624), (-25989126830389/562949953421312)), (1048892975927257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1029859087235607/1125899906842624), (-49769820147377/562949953421312)), (551945/281474976710656), by norm_num⟩
  | 2 => ⟨((1866420972568059/2251799813685248), (-364195085103759/2251799813685248)), (2214641/562949953421312), by norm_num⟩
  | 3 => ⟨((1488093731273639/2251799813685248), (-75466449194635/281474976710656)), (2193807/281474976710656), by norm_num⟩
  | 4 => ⟨((821534447580121/2251799813685248), (-24935864477275/70368744177664)), (32607241/2251799813685248), by norm_num⟩
  | 5 => ⟨((2120435784639/281474976710656), (-1164475614147641/4503599627370496)), (93803799/4503599627370496), by norm_num⟩
  | 6 => ⟨((-587573573337/8796093022208), (-70178764490781/18014398509481984)), (99844329/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-552936709/8388608)), (1/16777216), by norm_num⟩, -10, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-45987547/16777216), (-1120883985/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-778628804287443/18014398509481984), (862476586735825/18014398509481984)), (213382047/9007199254740992), by norm_num⟩
  | 1 => ⟨((147493139/1073741824), (-653504615/4294967296)), (325/4294967296), by norm_num⟩
  | 2 => ⟨((-937482271/4294967296), (519218211/2147483648)), (519/4294967296), by norm_num⟩
  | 3 => ⟨((993123041/4294967296), (-1100068949/4294967296)), (69/536870912), by norm_num⟩
  | 4 => ⟨((-789049621/4294967296), (3414139/16777216)), (55/536870912), by norm_num⟩
  | 5 => ⟨((250764217/2147483648), (-1111072515/8589934592)), (281/4294967296), by norm_num⟩
  | 6 => ⟨((-531294787/8589934592), (147127011/2147483648)), (299/8589934592), by norm_num⟩
  | 7 => ⟨((241211919/8589934592), (-534374355/17179869184)), (545/34359738368), by norm_num⟩
  | 8 => ⟨((-766584463/68719476736), (849135233/68719476736)), (435/68719476736), by norm_num⟩
  | 9 => ⟨((541388153/137438953472), (-599688329/137438953472)), (309/137438953472), by norm_num⟩
  | 10 => ⟨((-688224277/549755813888), (190584179/137438953472)), (395/549755813888), by norm_num⟩
  | 11 => ⟨((99418809/274877906944), (-880998953/2199023255552)), (459/2199023255552), by norm_num⟩
  | 12 => ⟨((-421277769/4398046511104), (466643683/4398046511104)), (61/1099511627776), by norm_num⟩
  | 13 => ⟨((25746989/1099511627776), (-912626919/35184372088832)), (15/1099511627776), by norm_num⟩
  | 14 => ⟨((-11689331/2199023255552), (828679279/140737488355328)), (219/70368744177664), by norm_num⟩
  | 15 => ⟨((634015115/562949953421312), (-351144981/281474976710656)), (373/562949953421312), by norm_num⟩
  | 16 => ⟨((-503733541/2251799813685248), (278989413/1125899906842624)), (595/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (1501355420859/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777735506323329/633825300114114700748351602688), (443705455797/79228162514264337593543950336)), (185099/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888579352079503/39614081257132168796771975168), (1996196857677/19807040628566084398385987584)), (104141/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888281645536897/2475880078570760549798248448), (2120365659771/1237940039285380274899124224)), (27669/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769947756275901/154742504910672534362390528), (4239396389527/154742504910672534362390528)), (110705/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48387125947553/302231454903657293676544), (3973016208315/9671406556917033397649408)), (207635/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257768816162165/604462909807314587353088), (108592868387/18889465931478580854784)), (181743/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886134485861641/75557863725914323419136), (5644172632411/75557863725914323419136)), (295449/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296296044162743/4722366482869645213696), (4230806105627/4722366482869645213696)), (221689/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404934509563515/147573952589676412928), (5813584963501/590295810358705651712)), (304989/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910668220680739/36893488147419103232), (7261324629783/73786976294838206464)), (381485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820250634975053/9223372036854775808), (4080609111225/4611686018427387904)), (429515/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198937266210549/144115188075855872), (8151511942151/1152921504606846976)), (429945/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298100717129987/36028797018963968), (3560832671793/72057594037927936)), (188343/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488368321545741/36028797018963968), (5330356342175/18014398509481984)), (282999/18014398509481984), by norm_num⟩
  | 3 => ⟨((742583730181887/4503599627370496), (13287833707057/9007199254740992)), (709197/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219756216347377/4503599627370496), (6615441110095/1125899906842624)), (711753/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203788028270069/2251799813685248), (9852206934583/562949953421312)), (1074037/1125899906842624), by norm_num⟩
  | 0 => ⟨((269499227748491/281474976710656), (9711000216397/281474976710656)), (2173825/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((269499227748491/281474976710656), (9711000216397/281474976710656)), (8292484287742232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030791881814681/1125899906842624), (148765312757429/2251799813685248)), (4312669/1125899906842624), by norm_num⟩
  | 2 => ⟨((938803811618791/1125899906842624), (17024834507271/140737488355328)), (8466565/1125899906842624), by norm_num⟩
  | 3 => ⟨((1532645152746377/2251799813685248), (454263599965689/2251799813685248)), (32335303/2251799813685248), by norm_num⟩
  | 4 => ⟨((951525856322267/2251799813685248), (154592983871223/562949953421312)), (7132883/281474976710656), by norm_num⟩
  | 5 => ⟨((116133237394343/1125899906842624), (522601415864727/2251799813685248)), (159131695/4503599627370496), by norm_num⟩
  | 6 => ⟨((-778628804287443/18014398509481984), (862476586735825/18014398509481984)), (213382047/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1120883985/16777216)), (1/8388608), by norm_num⟩, -11, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2911141/1048576), (-1135281703/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((8658826540739/1125899906842624), (1113163004137647/18014398509481984)), (87691707/9007199254740992), by norm_num⟩
  | 1 => ⟨((-53161025/2147483648), (-427142797/2147483648)), (271/8589934592), by norm_num⟩
  | 2 => ⟨((85559369/2147483648), (1374919623/4294967296)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((-183603323/4294967296), (-1475231845/4294967296)), (119/2147483648), by norm_num⟩
  | 4 => ⟨((73874537/2147483648), (1187147031/4294967296)), (97/2147483648), by norm_num⟩
  | 5 => ⟨((-190234369/8589934592), (-23882993/134217728)), (63/2147483648), by norm_num⟩
  | 6 => ⟨((51028401/4294967296), (410007407/4294967296)), (17/1073741824), by norm_num⟩
  | 7 => ⟨((-46929739/8589934592), (-377075123/8589934592)), (63/8589934592), by norm_num⟩
  | 8 => ⟨((75530501/34359738368), (606878999/34359738368)), (205/68719476736), by norm_num⟩
  | 9 => ⟨((-216109603/274877906944), (-1736416123/274877906944)), (37/34359738368), by norm_num⟩
  | 10 => ⟨((139125995/549755813888), (139732697/68719476736)), (3/8589934592), by norm_num⟩
  | 11 => ⟨((-162847019/2199023255552), (-654228655/1099511627776)), (113/1099511627776), by norm_num⟩
  | 12 => ⟨((174728111/8796093022208), (1403920535/8796093022208)), (61/2199023255552), by norm_num⟩
  | 13 => ⟨((-86527399/17592186044416), (-1390475653/35184372088832)), (61/8796093022208), by norm_num⟩
  | 14 => ⟨((79577415/70368744177664), (639395495/70368744177664)), (113/70368744177664), by norm_num⟩
  | 15 => ⟨((-34153309/140737488355328), (-1097671841/562949953421312)), (195/562949953421312), by norm_num⟩
  | 16 => ⟨((219870521/4503599627370496), (1766634677/4503599627370496)), (79/1125899906842624), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (1884847472219/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888842693202245/316912650057057350374175801344), (557008983403/158456325028528675187087900672)), (23105/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888523205001757/39614081257132168796771975168), (2505939448933/39614081257132168796771975168)), (103987/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888222307557083/2475880078570760549798248448), (2661806731935/2475880078570760549798248448)), (55251/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884944387985543/77371252455336267181195264), (41577483687/2417851639229258349412352)), (110521/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548333116007521/9671406556917033397649408), (1246874303595/4835703278458516698824704)), (103633/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257721145512083/604462909807314587353088), (545282502189/151115727451828646838272)), (45349/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886057731646677/75557863725914323419136), (3542649553527/75557863725914323419136)), (147421/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296239099533211/4722366482869645213696), (2655512124407/4722366482869645213696)), (55299/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809830373593273/295147905179352825856), (1824466893659/295147905179352825856)), (38031/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821241336814445/73786976294838206464), (2278788441141/36893488147419103232)), (95117/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910072856859213/4611686018427387904), (5122341681459/9223372036854775808)), (214121/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795697895883607/576460752303423488), (2558091460361/576460752303423488)), (13391/72057594037927936), by norm_num⟩
  | 5 => ⟨((596158110528033/72057594037927936), (4469740553905/144115188075855872)), (187627/144115188075855872), by norm_num⟩
  | 4 => ⟨((744122063353953/18014398509481984), (6690794558875/36028797018963968)), (281745/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485022280393489/9007199254740992), (8339365789381/9007199254740992)), (88179/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109747933735749/2251799813685248), (16606553223347/4503599627370496)), (707039/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203471906173233/2251799813685248), (24730095725493/2251799813685248)), (266149/562949953421312), by norm_num⟩
  | 0 => ⟨((1077827721523693/1125899906842624), (48745511524471/2251799813685248)), (2145427/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077827721523693/1125899906842624), (48745511524471/2251799813685248)), (8184154519087981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062560906177975/2251799813685248), (93328480270087/2251799813685248)), (525067/281474976710656), by norm_num⟩
  | 2 => ⟨((1885357330905973/2251799813685248), (170970504276799/2251799813685248)), (502703/140737488355328), by norm_num⟩
  | 3 => ⟨((1565566055402915/2251799813685248), (286295870217183/2251799813685248)), (14690077/2251799813685248), by norm_num⟩
  | 4 => ⟨((526030718656407/1125899906842624), (398094975841143/2251799813685248)), (12081001/1125899906842624), by norm_num⟩
  | 5 => ⟨((421153626679935/2251799813685248), (46498402069877/281474976710656)), (15560301/1125899906842624), by norm_num⟩
  | 6 => ⟨((8658826540739/1125899906842624), (1113163004137647/18014398509481984)), (87691707/9007199254740992), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-1135281703/16777216)), (1/16777216), by norm_num⟩, -11, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47145793/16777216), (-35909833/524288)), (1/8388608), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((220261089997823/4503599627370496), (316136641987727/9007199254740992)), (225270411/18014398509481984), by norm_num⟩
  | 1 => ⟨((-684387107/4294967296), (-491144037/4294967296)), (177/4294967296), by norm_num⟩
  | 2 => ⟨((69681227/268435456), (800097343/4294967296)), (291/4294967296), by norm_num⟩
  | 3 => ⟨((-1210816877/4294967296), (-868931461/4294967296)), (159/2147483648), by norm_num⟩
  | 4 => ⟨((986239569/4294967296), (353882823/2147483648)), (261/4294967296), by norm_num⟩
  | 5 => ⟨((-642652745/4294967296), (-14412305/134217728)), (43/1073741824), by norm_num⟩
  | 6 => ⟨((697941561/8589934592), (15652227/268435456)), (189/8589934592), by norm_num⟩
  | 7 => ⟨((-324851569/8589934592), (-466253409/17179869184)), (177/17179869184), by norm_num⟩
  | 8 => ⟨((264599443/17179869184), (759549309/68719476736)), (145/34359738368), by norm_num⟩
  | 9 => ⟨((-766302693/137438953472), (-274964997/68719476736)), (53/34359738368), by norm_num⟩
  | 10 => ⟨((998675261/549755813888), (179172501/137438953472)), (139/274877906944), by norm_num⟩
  | 11 => ⟨((-1183192877/2199023255552), (-849107353/2199023255552)), (331/2199023255552), by norm_num⟩
  | 12 => ⟨((642492769/4398046511104), (461078955/4398046511104)), (91/2199023255552), by norm_num⟩
  | 13 => ⟨((-322046687/8796093022208), (-462227615/17592186044416)), (23/2199023255552), by norm_num⟩
  | 14 => ⟨((1199153367/140737488355328), (860561253/140737488355328)), (43/17592186044416), by norm_num⟩
  | 15 => ⟨((-260463829/140737488355328), (-747677771/562949953421312)), (301/562949953421312), by norm_num⟩
  | 16 => ⟨((212154075/562949953421312), (609001589/2251799813685248)), (247/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (810833420083/10141204801825835211973625643008)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222204433834245/79228162514264337593543950336), (479207216535/316912650057057350374175801344)), (184589/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888467181897887/39614081257132168796771975168), (269489028911/9903520314283042199192993792)), (51919/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944081479857017/1237940039285380274899124224), (572500134653/1237940039285380274899124224)), (220669/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110614351667973/9671406556917033397649408), (286157838383/38685626227668133590597632)), (220685/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774138937176883/4835703278458516698824704), (1072700086435/9671406556917033397649408)), (206909/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628836509836583/302231454903657293676544), (938220954433/604462909807314587353088)), (181063/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885979921642203/75557863725914323419136), (1523875156883/75557863725914323419136)), (147129/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648090543398529/2361183241434822606848), (571132302889/2361183241434822606848)), (110361/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619581539160379/590295810358705651712), (1569571710787/590295810358705651712)), (303537/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821143164681181/73786976294838206464), (980201375391/36893488147419103232)), (189745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820036420022479/9223372036854775808), (2203307602323/9223372036854775808)), (427019/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591287932282113/1152921504606846976), (2200628888439/1152921504606846976)), (427137/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596111726529233/72057594037927936), (961270526005/72057594037927936)), (186939/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488108181751277/36028797018963968), (179862745623/2251799813685248)), (280541/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484857936690361/9007199254740992), (1793382894341/4503599627370496)), (701819/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219183843569427/4503599627370496), (3571080509433/2251799813685248)), (1405043/4503599627370496), by norm_num⟩
  | 1 => ⟨((275380648021375/281474976710656), (5317576475789/1125899906842624)), (527777/562949953421312), by norm_num⟩
  | 0 => ⟨((2154965196935923/2251799813685248), (20959970333975/2251799813685248)), (4236529/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154965196935923/2251799813685248), (20959970333975/2251799813685248)), (16161075600630950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062099681964771/2251799813685248), (40117248721683/2251799813685248)), (4093779/1125899906842624), by norm_num⟩
  | 2 => ⟨((1887665892359097/2251799813685248), (9184404995453/281474976710656)), (3821837/562949953421312), by norm_num⟩
  | 3 => ⟨((1580017854458117/2251799813685248), (123187419742473/2251799813685248)), (26628165/2251799813685248), by norm_num⟩
  | 4 => ⟨((1101910243061443/2251799813685248), (172873557813465/2251799813685248)), (40281763/2251799813685248), by norm_num⟩
  | 5 => ⟨((525944140138465/2251799813685248), (338380246683435/4503599627370496)), (22804221/1125899906842624), by norm_num⟩
  | 6 => ⟨((220261089997823/4503599627370496), (316136641987727/9007199254740992)), (225270411/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-35909833/524288)), (1/8388608), by norm_num⟩, -11, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47691909/16777216), (-290606371/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((517206240971765/9007199254740992), (-44635866745757/4503599627370496)), (2403385/562949953421312), by norm_num⟩
  | 1 => ⟨((-1625659367/8589934592), (280594893/8589934592)), (123/8589934592), by norm_num⟩
  | 2 => ⟨((669738509/2147483648), (-57799687/1073741824)), (103/4294967296), by norm_num⟩
  | 3 => ⟨((-183945739/536870912), (126998893/2147483648)), (115/4294967296), by norm_num⟩
  | 4 => ⟨((151563787/536870912), (-209283817/4294967296)), (3/134217728), by norm_num⟩
  | 5 => ⟨((-799247227/4294967296), (17244133/536870912)), (129/8589934592), by norm_num⟩
  | 6 => ⟨((878062825/8589934592), (-303113863/17179869184)), (9/1073741824), by norm_num⟩
  | 7 => ⟨((-206710845/4294967296), (285432527/34359738368)), (69/17179869184), by norm_num⟩
  | 8 => ⟨((1362570447/68719476736), (-235184761/68719476736)), (115/68719476736), by norm_num⟩
  | 9 => ⟨((-498978879/68719476736), (86125623/68719476736)), (43/68719476736), by norm_num⟩
  | 10 => ⟨((328910597/137438953472), (-227084803/549755813888)), (115/549755813888), by norm_num⟩
  | 11 => ⟨((-788389579/1099511627776), (272157987/2199023255552)), (35/549755813888), by norm_num⟩
  | 12 => ⟨((1732268959/8796093022208), (-298996109/8796093022208)), (39/2199023255552), by norm_num⟩
  | 13 => ⟨((-439175069/8796093022208), (151606523/17592186044416)), (5/1099511627776), by norm_num⟩
  | 14 => ⟨((827113933/70368744177664), (-71381481/35184372088832)), (153/140737488355328), by norm_num⟩
  | 15 => ⟨((-1453884049/562949953421312), (250945831/562949953421312)), (17/70368744177664), by norm_num⟩
  | 16 => ⟨((598970581/1125899906842624), (-103384565/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-55660489245/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888792904416083/316912650057057350374175801344), (-263151200421/633825300114114700748351602688)), (92227/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944205675360271/19807040628566084398385987584), (-295972983835/39614081257132168796771975168)), (103757/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944051844858993/1237940039285380274899124224), (-78595043859/618970019642690137449562112)), (27561/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110610650849421/9671406556917033397649408), (-78569430897/38685626227668133590597632)), (55123/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193527802810973/1208925819614629174706176), (-73631639493/2417851639229258349412352)), (51679/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257624559654155/604462909807314587353088), (-257601983467/604462909807314587353088)), (11305/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1885901287190151/75557863725914323419136), (-209199710401/37778931862957161709568)), (73485/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296122209798959/4722366482869645213696), (-9800667229/147573952589676412928)), (13779/590295810358705651712), by norm_num⟩
  | 9 => ⟨((101218796481969/36893488147419103232), (-430939971165/590295810358705651712)), (151575/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28453787666687/1152921504606846976), (-538241253023/73786976294838206464)), (94739/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819923401619679/9223372036854775808), (-18903926777/288230376151711744)), (26647/1152921504606846976), by norm_num⟩
  | 6 => ⟨((795587662693447/576460752303423488), (-18880683265/36028797018963968)), (213193/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192125383845757/144115188075855872), (-527823598907/144115188075855872)), (186563/144115188075855872), by norm_num⟩
  | 4 => ⟨((371990499691525/9007199254740992), (-790067413173/36028797018963968)), (69971/9007199254740992), by norm_num⟩
  | 3 => ⟨((185584601639847/1125899906842624), (-984672208409/9007199254740992)), (349923/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109413193396731/2251799813685248), (-980317919403/2251799813685248)), (350027/2251799813685248), by norm_num⟩
  | 1 => ⟨((1101260443706805/1125899906842624), (-729819648695/562949953421312)), (1050617/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153963635024147/2251799813685248), (-89881746771/35184372088832)), (2103447/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2153963635024147/2251799813685248), (-89881746771/35184372088832)), (8024013527877043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060363546678667/2251799813685248), (-5502500186969/1125899906842624)), (4034861/2251799813685248), by norm_num⟩
  | 2 => ⟨((1885148408242305/2251799813685248), (-20138825364355/2251799813685248)), (1855779/562949953421312), by norm_num⟩
  | 3 => ⟨((1578017249675519/2251799813685248), (-33719404672435/2251799813685248)), (6280829/1125899906842624), by norm_num⟩
  | 4 => ⟨((276334670925807/562949953421312), (-11814949512499/562949953421312)), (2247767/281474976710656), by norm_num⟩
  | 5 => ⟨((541584607018501/2251799813685248), (-46396737979271/2251799813685248)), (18408549/2251799813685248), by norm_num⟩
  | 6 => ⟨((517206240971765/9007199254740992), (-44635866745757/4503599627370496)), (2403385/562949953421312), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-290606371/4194304)), (1/16777216), by norm_num⟩, -11, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile017Terms3
