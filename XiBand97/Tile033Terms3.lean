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
namespace Reinmann.XiBand97.Tile033Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (32189/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (32189/1280))
  have he : value ((69/80), (32189/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-22364231/8388608), (-1304134491/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-433004396896557/9007199254740992), (-113109663475865/2251799813685248)), (459832265/18014398509481984), by norm_num⟩
  | 1 => ⟨((638215529/4294967296), (666860145/4294967296)), (85/1073741824), by norm_num⟩
  | 2 => ⟨((-986375647/4294967296), (-1030646509/4294967296)), (33/268435456), by norm_num⟩
  | 3 => ⟨((1016309667/4294967296), (530962019/2147483648)), (273/2147483648), by norm_num⟩
  | 4 => ⟨((-392682041/2147483648), (-820613071/4294967296)), (53/536870912), by norm_num⟩
  | 5 => ⟨((60689843/536870912), (31706873/268435456)), (527/8589934592), by norm_num⟩
  | 6 => ⟨((-1000506033/17179869184), (-1045411099/17179869184)), (545/17179869184), by norm_num⟩
  | 7 => ⟨((220900473/8589934592), (923260025/34359738368)), (483/34359738368), by norm_num⟩
  | 8 => ⟨((-170703185/17179869184), (-713458983/68719476736)), (375/68719476736), by norm_num⟩
  | 9 => ⟨((234511463/68719476736), (490073779/137438953472)), (517/274877906944), by norm_num⟩
  | 10 => ⟨((-289953955/274877906944), (-302967771/274877906944)), (161/274877906944), by norm_num⟩
  | 11 => ⟨((651825443/2199023255552), (681080903/2199023255552)), (91/549755813888), by norm_num⟩
  | 12 => ⟨((-335803353/4398046511104), (-701749995/8796093022208)), (377/8796093022208), by norm_num⟩
  | 13 => ⟨((159689603/8796093022208), (667427393/35184372088832)), (361/35184372088832), by norm_num⟩
  | 14 => ⟨((-564122677/140737488355328), (-294720915/70368744177664)), (321/140737488355328), by norm_num⟩
  | 15 => ⟨((464993905/562949953421312), (971727851/1125899906842624)), (531/1125899906842624), by norm_num⟩
  | 16 => ⟨((-359328975/2251799813685248), (-375456505/2251799813685248)), (103/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486533253/5070602400912917605986812821504), (-3040620449777/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777850905410413/633825300114114700748351602688), (-449363004419/79228162514264337593543950336)), (46277/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888709134955287/39614081257132168796771975168), (-4043323524755/39614081257132168796771975168)), (208293/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236052436128037/309485009821345068724781056), (-4294861862105/2475880078570760549798248448)), (221363/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885042771302313/77371252455336267181195264), (-4293546712589/154742504910672534362390528)), (221423/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548517144291533/9671406556917033397649408), (-502975390351/1208925819614629174706176)), (207647/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257881730192347/604462909807314587353088), (-1759715645619/302231454903657293676544)), (90877/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886317857402847/75557863725914323419136), (-2858229269365/37778931862957161709568)), (295469/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296433473322881/4722366482869645213696), (-267815923485/295147905179352825856)), (221705/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619926841748051/590295810358705651712), (-2944116195345/295147905179352825856)), (305013/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821572203466207/73786976294838206464), (-7354716936643/73786976294838206464)), (381519/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820515534457607/9223372036854775808), (-2066599585385/2305843009213693952)), (429557/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795881306699787/576460752303423488), (-8256833705651/1152921504606846976)), (429993/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192633824499117/144115188075855872), (-7213980450347/144115188075855872)), (188367/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488713822138745/36028797018963968), (-168742195481/562949953421312)), (283041/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485597705326449/9007199254740992), (-13461865631107/9007199254740992)), (709323/9007199254740992), by norm_num⟩
  | 2 => ⟨((277576478057939/562949953421312), (-26811452173855/4503599627370496)), (1423819/4503599627370496), by norm_num⟩
  | 1 => ⟨((275632409101391/281474976710656), (-39937357950225/2251799813685248)), (1074349/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158487862246489/2251799813685248), (-78760692225707/2251799813685248)), (4349509/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2158487862246489/2251799813685248), (-78760692225707/2251799813685248)), (16592060097701262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((64571495439835/70368744177664), (-75496941228135/1125899906842624)), (8642805/2251799813685248), by norm_num⟩
  | 2 => ⟨((235741778506909/281474976710656), (-34638605912349/281474976710656)), (8510319/1125899906842624), by norm_num⟩
  | 3 => ⟨((1545412064673699/2251799813685248), (-232085044523759/1125899906842624)), (32699509/2251799813685248), by norm_num⟩
  | 4 => ⟨((964936831803273/2251799813685248), (-159280156991559/562949953421312)), (58364293/2251799813685248), by norm_num⟩
  | 5 => ⟨((466453893102467/4503599627370496), (-1092070718702323/4503599627370496)), (83047305/2251799813685248), by norm_num⟩
  | 6 => ⟨((-433004396896557/9007199254740992), (-113109663475865/2251799813685248)), (459832265/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22364231/8388608), (-1304134491/16777216)), (1/8388608), by norm_num⟩, -12, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-45371695/16777216), (-661444515/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1147749148219209/18014398509481984), (368306674468265/18014398509481984)), (53190757/4503599627370496), by norm_num⟩
  | 1 => ⟨((53625715/268435456), (-275331365/4294967296)), (161/4294967296), by norm_num⟩
  | 2 => ⟨((-1345144953/4294967296), (431649951/4294967296)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((1405898073/4294967296), (-112786327/1073741824)), (67/1073741824), by norm_num⟩
  | 4 => ⟨((-1102046319/4294967296), (88410219/1073741824)), (53/1073741824), by norm_num⟩
  | 5 => ⟨((1382183943/8589934592), (-27720973/536870912)), (67/2147483648), by norm_num⟩
  | 6 => ⟨((-1444609919/17179869184), (57945967/2147483648)), (141/8589934592), by norm_num⟩
  | 7 => ⟨((1294161727/34359738368), (-415289701/34359738368)), (127/17179869184), by norm_num⟩
  | 8 => ⟨((-63403697/4294967296), (162767307/34359738368)), (201/68719476736), by norm_num⟩
  | 9 => ⟨((1413702579/274877906944), (-453649733/274877906944)), (141/137438953472), by norm_num⟩
  | 10 => ⟨((-221632813/137438953472), (284483223/549755813888)), (179/549755813888), by norm_num⟩
  | 11 => ⟨((505402475/1099511627776), (-20272625/137438953472)), (205/2199023255552), by norm_num⟩
  | 12 => ⟨((-1056457691/8796093022208), (339011725/8796093022208)), (27/1099511627776), by norm_num⟩
  | 13 => ⟨((509617997/17592186044416), (-163533739/17592186044416)), (105/17592186044416), by norm_num⟩
  | 14 => ⟨((-913088161/140737488355328), (73251299/35184372088832)), (95/70368744177664), by norm_num⟩
  | 15 => ⟨((763462039/562949953421312), (-244990959/562949953421312)), (5/17592186044416), by norm_num⟩
  | 16 => ⟨((-1196915403/4503599627370496), (384083867/4503599627370496)), (253/4503599627370496), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031359859/10141204801825835211973625643008), (115243611095/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111111787314443/39614081257132168796771975168), (272486151953/39614081257132168796771975168)), (46315/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888638875978785/39614081257132168796771975168), (2451791143495/19807040628566084398385987584)), (104237/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236043077389337/309485009821345068724781056), (40692317473/19342813113834066795298816)), (110783/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770010425772817/154742504910672534362390528), (1301749376895/38685626227668133590597632)), (110819/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774223230071047/4835703278458516698824704), (2439920147255/4835703278458516698824704)), (103931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257819619706531/604462909807314587353088), (2134070450349/302231454903657293676544)), (45489/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886216437447019/75557863725914323419136), (6932506257027/75557863725914323419136)), (147911/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296356979803145/4722366482869645213696), (5196560912343/4722366482869645213696)), (27749/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619820967811935/590295810358705651712), (7140692776195/590295810358705651712)), (76361/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910719409932783/36893488147419103232), (4459500911531/36893488147419103232)), (11941/4611686018427387904), by norm_num⟩
  | 7 => ⟨((113772753079335/576460752303423488), (5012222325449/4611686018427387904)), (53787/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591609346887505/1152921504606846976), (10012662855547/1152921504606846976)), (215413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192497718453483/144115188075855872), (8747837449747/144115188075855872)), (188783/144115188075855872), by norm_num⟩
  | 4 => ⟨((744252841351589/18014398509481984), (13095301009933/36028797018963968)), (141885/18014398509481984), by norm_num⟩
  | 3 => ⟨((46416581243917/281474976710656), (2040362136127/1125899906842624)), (88939/2251799813685248), by norm_num⟩
  | 2 => ⟨((1110028478521743/2251799813685248), (16253688096369/2251799813685248)), (357325/2251799813685248), by norm_num⟩
  | 1 => ⟨((275521976208765/281474976710656), (24207981514541/1125899906842624)), (539919/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078259574271029/1125899906842624), (23864296447343/562949953421312)), (273911/281474976710656), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078259574271029/1125899906842624), (23864296447343/562949953421312)), (1044887543798351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2061223531284345/2251799813685248), (182836189762197/2251799813685248)), (4382921/2251799813685248), by norm_num⟩
  | 2 => ⟨((1871930776446339/2251799813685248), (41840559540175/281474976710656)), (272991/70368744177664), by norm_num⟩
  | 3 => ⟨((1506388061737577/2251799813685248), (556515765786891/2251799813685248)), (8560577/1125899906842624), by norm_num⟩
  | 4 => ⟨((870190672841941/2251799813685248), (744585465062391/2251799813685248)), (7842459/562949953421312), by norm_num⟩
  | 5 => ⟨((90072079714313/2251799813685248), (1150957243877875/4503599627370496)), (702983/35184372088832), by norm_num⟩
  | 6 => ⟨((-1147749148219209/18014398509481984), (368306674468265/18014398509481984)), (53190757/4503599627370496), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45371695/16777216), (-661444515/8388608)), (1/16777216), by norm_num⟩, -13, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-45987547/16777216), (-1340845257/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((-109726567767241/9007199254740992), (285259640375847/4503599627370496)), (198572253/9007199254740992), by norm_num⟩
  | 1 => ⟨((83140597/2147483648), (-864572995/4294967296)), (151/2147483648), by norm_num⟩
  | 2 => ⟨((-264225293/4294967296), (1373829759/4294967296)), (241/2147483648), by norm_num⟩
  | 3 => ⟨((279907401/4294967296), (-1455368309/4294967296)), (513/4294967296), by norm_num⟩
  | 4 => ⟨((-222390197/4294967296), (1156309707/4294967296)), (409/4294967296), by norm_num⟩
  | 5 => ⟨((282707207/8589934592), (-1469925797/8589934592)), (261/4294967296), by norm_num⟩
  | 6 => ⟨((-299486241/17179869184), (778583885/8589934592)), (555/17179869184), by norm_num⟩
  | 7 => ⟨((271938113/34359738368), (-353483071/8589934592)), (253/17179869184), by norm_num⟩
  | 8 => ⟨((-108029245/34359738368), (280847057/17179869184)), (101/17179869184), by norm_num⟩
  | 9 => ⟨((305175783/274877906944), (-793375169/137438953472)), (143/68719476736), by norm_num⟩
  | 10 => ⟨((-193973013/549755813888), (504277799/274877906944)), (365/549755813888), by norm_num⟩
  | 11 => ⟨((14010379/137438953472), (-582771633/1099511627776)), (53/274877906944), by norm_num⟩
  | 12 => ⟨((-118735303/4398046511104), (1234719747/8796093022208)), (451/8796093022208), by norm_num⟩
  | 13 => ⟨((58053413/8796093022208), (-603693203/17592186044416)), (443/35184372088832), by norm_num⟩
  | 14 => ⟨((-210853567/140737488355328), (548162713/70368744177664)), (101/35184372088832), by norm_num⟩
  | 15 => ⟨((44673599/140737488355328), (-58069687/35184372088832)), (43/70368744177664), by norm_num⟩
  | 16 => ⟨((-283950205/4503599627370496), (1476388729/4503599627370496)), (549/4503599627370496), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197550651945091/1267650600228229401496703205376), (2293643480545/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777738321784949/633825300114114700748351602688), (1355711128533/316912650057057350374175801344)), (92467/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888582672830661/39614081257132168796771975168), (3049625101007/39614081257132168796771975168)), (104043/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888285380067307/2475880078570760549798248448), (1619660260935/1237940039285380274899124224)), (110565/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769951722548481/154742504910672534362390528), (3238301534657/154742504910672534362390528)), (27647/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774195997360519/4835703278458516698824704), (758706351701/2417851639229258349412352)), (25925/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((628886265398571/302231454903657293676544), (663597597489/151115727451828646838272)), (90761/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117883811406005/4722366482869645213696), (134729902139/2361183241434822606848)), (295063/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648150659476085/2361183241434822606848), (3231744511747/4722366482869645213696)), (3459/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1619745943921941/590295810358705651712), (555096138301/73786976294838206464)), (152259/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910673650537009/36893488147419103232), (5546645055963/73786976294838206464)), (380839/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910132096879371/4611686018427387904), (6234045721893/9223372036854775808)), (428707/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795756680767883/576460752303423488), (778330091767/144115188075855872)), (429035/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596209036590283/72057594037927936), (339999393315/9007199254740992)), (11743/4503599627370496), by norm_num⟩
  | 4 => ⟨((1488394868617661/36028797018963968), (8143370368319/36028797018963968)), (564405/36028797018963968), by norm_num⟩
  | 3 => ⟨((46412723720021/281474976710656), (10150194172315/9007199254740992)), (353403/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109927518673915/2251799813685248), (20213561951501/4503599627370496)), (88595/281474976710656), by norm_num⟩
  | 1 => ⟨((550996099363801/562949953421312), (30104080156269/2251799813685248)), (2136083/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156576595218947/2251799813685248), (59347915017737/2251799813685248)), (4311571/2251799813685248), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2156576595218947/2251799813685248), (59347915017737/2251799813685248)), (16447338112837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((257976997321507/281474976710656), (113676467796515/2251799813685248)), (66295/17592186044416), by norm_num⟩
  | 2 => ⟨((1885786661971985/2251799813685248), (13023321900123/140737488355328)), (4102869/562949953421312), by norm_num⟩
  | 3 => ⟨((389996031542661/562949953421312), (349007318814921/2251799813685248)), (15262571/1125899906842624), by norm_num⟩
  | 4 => ⟨((1026620728569409/2251799813685248), (483565078884721/2251799813685248)), (51756143/2251799813685248), by norm_num⟩
  | 5 => ⟨((182102096693359/1125899906842624), (440925459339919/2251799813685248)), (138842527/4503599627370496), by norm_num⟩
  | 6 => ⟨((-109726567767241/9007199254740992), (285259640375847/4503599627370496)), (198572253/9007199254740992), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45987547/16777216), (-1340845257/16777216)), (1/8388608), by norm_num⟩, -13, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-2911141/1048576), (-679034185/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((208182820527339/4503599627370496), (751587757021963/18014398509481984)), (31269861/4503599627370496), by norm_num⟩
  | 1 => ⟨((-639071129/4294967296), (-288399179/2147483648)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((128568163/536870912), (928321145/4294967296)), (5/134217728), by norm_num⟩
  | 3 => ⟨((-551793269/2147483648), (-249012541/1073741824)), (87/2147483648), by norm_num⟩
  | 4 => ⟨((888077007/4294967296), (25048139/134217728)), (71/2147483648), by norm_num⟩
  | 5 => ⟨((-285860961/2147483648), (-258005917/2147483648)), (93/4294967296), by norm_num⟩
  | 6 => ⟨((306716979/4294967296), (553659339/8589934592)), (101/8589934592), by norm_num⟩
  | 7 => ⟨((-564162211/17179869184), (-1018377521/34359738368)), (47/8589934592), by norm_num⟩
  | 8 => ⟨((907984051/68719476736), (51219231/4294967296)), (153/68719476736), by norm_num⟩
  | 9 => ⟨((-649486203/137438953472), (-293099279/68719476736)), (111/137438953472), by norm_num⟩
  | 10 => ⟨((836246175/549755813888), (754760147/549755813888)), (145/549755813888), by norm_num⟩
  | 11 => ⟨((-978826399/2199023255552), (-883446979/2199023255552)), (43/549755813888), by norm_num⟩
  | 12 => ⟨((1050240211/8796093022208), (947902041/8796093022208)), (93/4398046511104), by norm_num⟩
  | 13 => ⟨((-130022801/4398046511104), (-938824297/35184372088832)), (93/17592186044416), by norm_num⟩
  | 14 => ⟨((239158429/35184372088832), (431708405/70368744177664)), (173/140737488355328), by norm_num⟩
  | 15 => ⟨((-821142705/562949953421312), (-741128399/562949953421312)), (151/562949953421312), by norm_num⟩
  | 16 => ⟨((660789101/2251799813685248), (74550009/281474976710656)), (123/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790179675953489/5070602400912917605986812821504), (478205813379/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888843682023581/316912650057057350374175801344), (141319092337/79228162514264337593543950336)), (11539/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((59016423042719/1237940039285380274899124224), (1271568300863/39614081257132168796771975168)), (51929/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472056232636227/618970019642690137449562112), (168832365019/309485009821345068724781056)), (55179/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769891561711765/154742504910672534362390528), (1350228948329/154742504910672534362390528)), (110367/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548335900417279/9671406556917033397649408), (632691491629/4835703278458516698824704)), (103479/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314430938620721/151115727451828646838272), (1106753667581/604462909807314587353088)), (45277/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886062294520581/75557863725914323419136), (449404833017/18889465931478580854784)), (147169/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296242804221627/4722366482869645213696), (1347466495689/4722366482869645213696)), (55197/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619666299591171/590295810358705651712), (1851551773345/590295810358705651712)), (151817/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821248963857063/73786976294838206464), (578154802709/18446744073709551616)), (189811/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820155236262893/9223372036854775808), (2599195821903/9223372036854775808)), (213593/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198925811146007/144115188075855872), (324509179763/144115188075855872)), (106831/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192326899158525/144115188075855872), (2268056525957/144115188075855872)), (23379/18014398509481984), by norm_num⟩
  | 4 => ⟨((1488262770044719/36028797018963968), (848770419771/9007199254740992)), (2193/281474976710656), by norm_num⟩
  | 3 => ⟨((1485050158910565/9007199254740992), (1057906101059/2251799813685248)), (175577/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219565261939585/4503599627370496), (4213338230409/2251799813685248)), (175783/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203609793161797/2251799813685248), (12548970257123/2251799813685248)), (1056775/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156064618874343/2251799813685248), (24736072279989/2251799813685248)), (2121925/2251799813685248), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2156064618874343/2251799813685248), (24736072279989/2251799813685248)), (8094501503951262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064127876395505/2251799813685248), (2960552372855/140737488355328)), (2055021/1125899906842624), by norm_num⟩
  | 2 => ⟨((118193790402199/140737488355328), (10855243250665/281474976710656)), (1926979/562949953421312), by norm_num⟩
  | 3 => ⟨((198103762914047/281474976710656), (145862753189929/2251799813685248)), (13541005/2251799813685248), by norm_num⟩
  | 4 => ⟨((1105964437185567/2251799813685248), (102659073334365/1125899906842624)), (20814747/2251799813685248), by norm_num⟩
  | 5 => ⟨((262235076979357/1125899906842624), (403365462852295/4503599627370496)), (6060489/562949953421312), by norm_num⟩
  | 6 => ⟨((208182820527339/4503599627370496), (751587757021963/18014398509481984)), (31269861/4503599627370496), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/1048576), (-679034185/8388608)), (1/16777216), by norm_num⟩, -13, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-47145793/16777216), (-1374615889/16777216)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((1050165666309391/18014398509481984), (-135241213398999/9007199254740992)), (170449669/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1631517945/8589934592), (420216493/8589934592)), (267/8589934592), by norm_num⟩
  | 2 => ⟨((664455371/2147483648), (-342276475/4294967296)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((-1443239829/4294967296), (185861633/2147483648)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((1175553673/4294967296), (-75694393/1073741824)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((-1532026941/8589934592), (6165491/134217728)), (65/2147483648), by norm_num⟩
  | 6 => ⟨((831915279/8589934592), (-53567373/2147483648)), (285/17179869184), by norm_num⟩
  | 7 => ⟨((-387208613/8589934592), (199460197/17179869184)), (267/34359738368), by norm_num⟩
  | 8 => ⟨((630781521/34359738368), (-324930289/68719476736)), (219/68719476736), by norm_num⟩
  | 9 => ⟨((-913398707/137438953472), (58814125/34359738368)), (5/4294967296), by norm_num⟩
  | 10 => ⟨((595188233/274877906944), (-306595355/549755813888)), (105/274877906944), by norm_num⟩
  | 11 => ⟨((-352578313/549755813888), (181621321/1099511627776)), (251/2199023255552), by norm_num⟩
  | 12 => ⟨((1531645575/8796093022208), (-197246599/4398046511104)), (275/8796093022208), by norm_num⟩
  | 13 => ⟨((-383865319/8796093022208), (49434497/4398046511104)), (139/17592186044416), by norm_num⟩
  | 14 => ⟨((178667181/17592186044416), (-368142545/140737488355328)), (261/140737488355328), by norm_num⟩
  | 15 => ⟨((-1241845171/562949953421312), (39981465/70368744177664)), (229/562949953421312), by norm_num⟩
  | 16 => ⟨((1011512863/2251799813685248), (-260526945/2251799813685248)), (47/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790157643683405/5070602400912917605986812821504), (-164182978587/5070602400912917605986812821504)), (155285/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888817941363373/316912650057057350374175801344), (-388132339997/633825300114114700748351602688)), (46119/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888467667818247/39614081257132168796771975168), (-436543641625/39614081257132168796771975168)), (103771/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472040876545215/618970019642690137449562112), (-463694757579/2475880078570760549798248448)), (220519/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769830207059019/154742504910672534362390528), (-463545371365/154742504910672534362390528)), (110263/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774139227222347/4835703278458516698824704), (-27150945671/604462909807314587353088)), (103375/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314418390802631/151115727451828646838272), (-47494332619/75557863725914323419136)), (180913/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885980872237185/75557863725914323419136), (-617129151887/75557863725914323419136)), (293997/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648090929298851/2361183241434822606848), (-231293500295/2361183241434822606848)), (220509/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619582695886039/590295810358705651712), (-635635152025/590295810358705651712)), (303219/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821144753595607/73786976294838206464), (-793911511117/73786976294838206464)), (379051/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455009600948279/2305843009213693952), (-446140861771/4611686018427387904)), (426471/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591290160766327/1152921504606846976), (-891197108949/1152921504606846976)), (53315/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192225677476915/144115188075855872), (-389289527557/72057594037927936)), (93315/36028797018963968), by norm_num⟩
  | 4 => ⟨((744056032676619/18014398509481984), (-1165436185701/36028797018963968)), (280001/18014398509481984), by norm_num⟩
  | 3 => ⟨((23200995998073/140737488355328), (-1452548493403/9007199254740992)), (700199/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109599148987315/2251799813685248), (-2892396498143/4503599627370496)), (43781/140737488355328), by norm_num⟩
  | 1 => ⟨((1101536951543915/1125899906842624), (-4306982139117/2251799813685248)), (2103001/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155050409714419/2251799813685248), (-4244171037945/1125899906842624)), (2106095/1125899906842624), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2155050409714419/2251799813685248), (-4244171037945/1125899906842624)), (8034114841941451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2062425881836511/2251799813685248), (-4061818674393/562949953421312)), (8094181/2251799813685248), by norm_num⟩
  | 2 => ⟨((1888860865110869/2251799813685248), (-29761792892895/2251799813685248)), (7471871/1125899906842624), by norm_num⟩
  | 3 => ⟨((1584026067394353/2251799813685248), (-780152135545/35184372088832)), (25465321/2251799813685248), by norm_num⟩
  | 4 => ⟨((139146783183519/281474976710656), (-70246035149731/2251799813685248)), (36956403/2251799813685248), by norm_num⟩
  | 5 => ⟨((548104868090561/2251799813685248), (-138904138999599/4503599627370496)), (77688893/4503599627370496), by norm_num⟩
  | 6 => ⟨((1050165666309391/18014398509481984), (-135241213398999/9007199254740992)), (170449669/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47145793/16777216), (-1374615889/16777216)), (1/8388608), by norm_num⟩, -13, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-47691909/16777216), (-695269411/8388608)), (1/8388608), by norm_num⟩
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
  | 0 => ⟨((47403902292117/2251799813685248), (-244702706799697/4503599627370496)), (149436133/9007199254740992), by norm_num⟩
  | 1 => ⟨((-148997811/2147483648), (769138529/4294967296)), (59/1073741824), by norm_num⟩
  | 2 => ⟨((245536239/2147483648), (-1267477559/4294967296)), (391/4294967296), by norm_num⟩
  | 3 => ⟨((-539498259/4294967296), (696233211/2147483648)), (431/4294967296), by norm_num⟩
  | 4 => ⟨((444524563/4294967296), (-573667771/2147483648)), (357/4294967296), by norm_num⟩
  | 5 => ⟨((-586032177/8589934592), (1512572311/8589934592)), (473/8589934592), by norm_num⟩
  | 6 => ⟨((80477769/2147483648), (-51929079/536870912)), (131/4294967296), by norm_num⟩
  | 7 => ⟨((-303133255/17179869184), (391199481/8589934592)), (31/2147483648), by norm_num⟩
  | 8 => ⟨((499538879/68719476736), (-1289329671/68719476736)), (411/68719476736), by norm_num⟩
  | 9 => ⟨((-365866367/137438953472), (472157807/68719476736)), (303/137438953472), by norm_num⟩
  | 10 => ⟨((60291793/68719476736), (-1244924085/549755813888)), (201/274877906944), by norm_num⟩
  | 11 => ⟨((-578071023/2199023255552), (1492024253/2199023255552)), (121/549755813888), by norm_num⟩
  | 12 => ⟨((317537965/4398046511104), (-409789045/2199023255552)), (67/1099511627776), by norm_num⟩
  | 13 => ⟨((-161008205/8796093022208), (831137133/17592186044416)), (137/8796093022208), by norm_num⟩
  | 14 => ⟨((75808111/17592186044416), (-195663743/17592186044416)), (65/17592186044416), by norm_num⟩
  | 15 => ⟨((-533015823/562949953421312), (85983437/35184372088832)), (459/562949953421312), by norm_num⟩
  | 16 => ⟨((109795825/562949953421312), (-566774763/1125899906842624)), (95/562949953421312), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885989599/10141204801825835211973625643008), (-1564649619327/10141204801825835211973625643008)), (38821/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777584010642535/633825300114114700748351602688), (-1849334380405/633825300114114700748351602688)), (46191/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236051153793233/4951760157141521099596496896), (-2079992258203/39614081257132168796771975168)), (51971/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944050652575911/1237940039285380274899124224), (-552337793867/618970019642690137449562112)), (27613/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884883940545461/77371252455336267181195264), (-552157717733/38685626227668133590597632)), (110467/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48381871600827/302231454903657293676544), (-1034913215363/4835703278458516698824704)), (207159/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314405546977957/151115727451828646838272), (-1810333468137/604462909807314587353088)), (181297/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885897139269737/75557863725914323419136), (-2940358898241/75557863725914323419136)), (294667/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296118842076223/4722366482869645213696), (-1102008028441/2361183241434822606848)), (110527/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619495696433421/590295810358705651712), (-757121790899/147573952589676412928)), (76009/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455258869412819/18446744073709551616), (-3782559031077/73786976294838206464)), (380175/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454978686455815/2305843009213693952), (-4251189240699/9223372036854775808)), (427877/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591165601999521/1152921504606846976), (-4245958111345/1152921504606846976)), (214051/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192115678409771/144115188075855872), (-231833531779/9007199254740992)), (374843/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487945054566565/36028797018963968), (-694033938729/4503599627370496)), (562771/36028797018963968), by norm_num⟩
  | 3 => ⟨((742325738626883/4503599627370496), (-6919852071965/9007199254740992)), (352177/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109381663893153/2251799813685248), (-13778425311313/4503599627370496)), (1411387/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101197803958401/1125899906842624), (-20515080006431/2251799813685248)), (2123807/2251799813685248), by norm_num⟩
  | 0 => ⟨((134599497816917/140737488355328), (-40423748725409/2251799813685248)), (4274687/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((134599497816917/140737488355328), (-40423748725409/2251799813685248)), (16306636818892668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2058941582808035/2251799813685248), (-9665186479277/281474976710656)), (8329987/2251799813685248), by norm_num⟩
  | 2 => ⟨((1879945900425545/2251799813685248), (-35349597645111/562949953421312)), (15805175/2251799813685248), by norm_num⟩
  | 3 => ⟨((195077458834851/281474976710656), (-118048382046643/1125899906842624)), (28375259/2251799813685248), by norm_num⟩
  | 4 => ⟨((264209995492405/562949953421312), (-163627890893457/1125899906842624)), (45281375/2251799813685248), by norm_num⟩
  | 5 => ⟨((448447679336087/2251799813685248), (-153591359418897/1125899906842624)), (27832741/1125899906842624), by norm_num⟩
  | 6 => ⟨((47403902292117/2251799813685248), (-244702706799697/4503599627370496)), (149436133/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47691909/16777216), (-695269411/8388608)), (1/8388608), by norm_num⟩, -13, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile033Terms3
