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
namespace Reinmann.XiBand97.Tile050Terms0
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-320962607/536870912), (-22099031391/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-198504980921333/2251799813685248), (-305618788965055/562949953421312)), (6351261/2251799813685248), by norm_num⟩
  | 1 => ⟨((4199010249/68719476736), (6464807187/17179869184)), (137/68719476736), by norm_num⟩
  | 2 => ⟨((-2910532115/137438953472), (-8962125749/68719476736)), (97/137438953472), by norm_num⟩
  | 3 => ⟨((2689902839/549755813888), (16565525853/549755813888)), (91/549755813888), by norm_num⟩
  | 4 => ⟨((-1864498569/2199023255552), (-22964695079/4398046511104)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((1033897541/8796093022208), (25468661835/35184372088832)), (9/2199023255552), by norm_num⟩
  | 6 => ⟨((-3822096883/281474976710656), (-23538041525/281474976710656)), (135/281474976710656), by norm_num⟩
  | 7 => ⟨((189233977/140737488355328), (2330761017/281474976710656)), (109/2251799813685248), by norm_num⟩
  | 8 => ⟨((-1049335981/9007199254740992), (-3231120855/4503599627370496)), (153/36028797018963968), by norm_num⟩
  | 9 => ⟨((323264123/36028797018963968), (15926345321/288230376151711744)), (3/9007199254740992), by norm_num⟩
  | 10 => ⟨((-1434045539/2305843009213693952), (-8831441085/2305843009213693952)), (27/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1445824905/36893488147419103232), (1112997907/4611686018427387904)), (55/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-668112971/295147905179352825856), (-8229027853/590295810358705651712)), (103/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((1139939993/9444732965739290427392), (28080873625/37778931862957161709568)), (89/18889465931478580854784), by norm_num⟩
  | 14 => ⟨((-1806048439/302231454903657293676544), (-22244775293/604462909807314587353088)), (143/604462909807314587353088), by norm_num⟩
  | 15 => ⟨((2670629085/9671406556917033397649408), (8223415081/4835703278458516698824704)), (107/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-3702278041/309485009821345068724781056), (-2850018489/38685626227668133590597632)), (75/154742504910672534362390528), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-281978117187/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781044608898557/633825300114114700748351602688), (-2676158087643/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946150842640307/19807040628566084398385987584), (-3010509076841/39614081257132168796771975168)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118264760305143/154742504910672534362390528), (-799617473795/618970019642690137449562112)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1773901758126471/154742504910672534362390528), (-3198249351519/154742504910672534362390528)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552094357016683/9671406556917033397649408), (-2998124401265/9671406556917033397649408)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261011301753099/604462909807314587353088), (-1311562221215/302231454903657293676544)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945701246356841/37778931862957161709568), (-4262137611575/75557863725914323419136)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650123072808087/2361183241434822606848), (-1598109230589/2361183241434822606848)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((203145994795267/73786976294838206464), (-4394174998817/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828121635836859/73786976294838206464), (-1372945093055/18446744073709551616)), (5951/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827880943425661/9223372036854775808), (-6176962166929/9223372036854775808)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799562320074695/576460752303423488), (-6175348001277/1152921504606846976)), (419/72057594037927936), by norm_num⟩
  | 5 => ⟨((1199071787210101/144115188075855872), (-5401612567851/144115188075855872)), (367/9007199254740992), by norm_num⟩
  | 4 => ⟨((1498363130615155/36028797018963968), (-4049391248251/18014398509481984)), (4409/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497645946824499/9007199254740992), (-10117108908927/9007199254740992)), (11043/9007199254740992), by norm_num⟩
  | 2 => ⟨((561166999645179/1125899906842624), (-5053771967843/1125899906842624)), (173/35184372088832), by norm_num⟩
  | 1 => ⟨((280130290219703/281474976710656), (-7568682267311/562949953421312)), (8341/562949953421312), by norm_num⟩
  | 0 => ⟨((1115023247562045/1125899906842624), (-30178690851513/1125899906842624)), (8415/281474976710656), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115023247562045/1125899906842624), (-30178690851513/1125899906842624)), (32100678563976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((551721374907243/562949953421312), (-29887152202357/562949953421312)), (68475/1125899906842624), by norm_num⟩
  | 2 => ⟨((539130044896957/562949953421312), (-58582048386123/562949953421312)), (70745/562949953421312), by norm_num⟩
  | 3 => ⟨((7972215912907/8796093022208), (-224413144966933/1125899906842624)), (300455/1125899906842624), by norm_num⟩
  | 4 => ⟨((880135037169423/1125899906842624), (-406787431841369/1125899906842624)), (41525/70368744177664), by norm_num⟩
  | 5 => ⟨((541044248469125/1125899906842624), (-79498157266879/140737488355328)), (1518841/1125899906842624), by norm_num⟩
  | 6 => ⟨((-198504980921333/2251799813685248), (-305618788965055/562949953421312)), (6351261/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-22099031391/1073741824)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-4378267007/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((312505666749727/2251799813685248), (-815146477485375/2251799813685248)), (7550329/2251799813685248), by norm_num⟩
  | 1 => ⟨((-5238686611/34359738368), (13664702411/34359738368)), (129/34359738368), by norm_num⟩
  | 2 => ⟨((5755285487/68719476736), (-7506104995/34359738368)), (9/4294967296), by norm_num⟩
  | 3 => ⟨((-8430436481/274877906944), (10995065583/137438953472)), (107/137438953472), by norm_num⟩
  | 4 => ⟨((9261781117/1099511627776), (-3019828541/137438953472)), (119/549755813888), by norm_num⟩
  | 5 => ⟨((-1017510655/549755813888), (21232772767/4398046511104)), (53/1099511627776), by norm_num⟩
  | 6 => ⟨((5961865117/17592186044416), (-15551056723/17592186044416)), (157/17592186044416), by norm_num⟩
  | 7 => ⟨((-1871365223/35184372088832), (19525236591/140737488355328)), (25/17592186044416), by norm_num⟩
  | 8 => ⟨((4111809661/562949953421312), (-10725332429/562949953421312)), (111/562949953421312), by norm_num⟩
  | 9 => ⟨((-8030728217/9007199254740992), (20947523567/9007199254740992)), (219/9007199254740992), by norm_num⟩
  | 10 => ⟨((7058125365/72057594037927936), (-9205282723/36028797018963968)), (195/72057594037927936), by norm_num⟩
  | 11 => ⟨((-5639376917/576460752303423488), (14709871593/576460752303423488)), (79/288230376151711744), by norm_num⟩
  | 12 => ⟨((2065162927/2305843009213693952), (-21547260929/9223372036854775808)), (117/4611686018427387904), by norm_num⟩
  | 13 => ⟨((-1396192843/18446744073709551616), (14567437319/73786976294838206464)), (5/2305843009213693952), by norm_num⟩
  | 14 => ⟨((3505999119/590295810358705651712), (-4572561615/295147905179352825856)), (51/295147905179352825856), by norm_num⟩
  | 15 => ⟨((-1027128991/2361183241434822606848), (10716741079/9444732965739290427392)), (121/9444732965739290427392), by norm_num⟩
  | 16 => ⟨((2256833063/75557863725914323419136), (-23547086887/302231454903657293676544)), (269/302231454903657293676544), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-1569262344653/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27820411096511/9903520314283042199192993792), (-29071794011/9903520314283042199192993792)), (5775/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236462032861223/4951760157141521099596496896), (-261623689289/4951760157141521099596496896)), (3249/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945796550218739/1237940039285380274899124224), (-2223586047015/2475880078570760549798248448)), (863/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1773258915123109/154742504910672534362390528), (-138958989545/9671406556917033397649408)), (6905/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551491926960547/9671406556917033397649408), (-2084127507815/9671406556917033397649408)), (6475/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260484410688731/604462909807314587353088), (-911677126733/302231454903657293676544)), (5667/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472636683936647/18889465931478580854784), (-2962468236045/75557863725914323419136)), (4605/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649802356862051/2361183241434822606848), (-2221429095863/4722366482869645213696)), (6909/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624286616390693/590295810358705651712), (-3053779202625/590295810358705651712)), (4751/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827020898519611/73786976294838206464), (-119256107283/2305843009213693952)), (5941/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456660976591065/2305843009213693952), (-4291805799311/9223372036854775808)), (3343/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597889218190573/1152921504606846976), (-4290038552655/1152921504606846976)), (13379/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598996304702025/72057594037927936), (-3751796037769/144115188075855872)), (11715/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496747995263257/36028797018963968), (-5623719807561/36028797018963968)), (17587/36028797018963968), by norm_num⟩
  | 3 => ⟨((93477086201319/562949953421312), (-3511348698197/4503599627370496)), (5503/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120330952472949/2251799813685248), (-7012274003015/2251799813685248)), (22053/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117540369465295/1125899906842624), (-10492370574963/1125899906842624)), (16591/562949953421312), by norm_num⟩
  | 0 => ⟨((1109156640478065/1125899906842624), (-10440343975877/562949953421312)), (66777/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109156640478065/1125899906842624), (-10440343975877/562949953421312)), (254734043601607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((273068778697205/281474976710656), (-20570171077095/562949953421312)), (67023/562949953421312), by norm_num⟩
  | 2 => ⟨((1058151254293419/1125899906842624), (-9977923365083/140737488355328)), (134941/562949953421312), by norm_num⟩
  | 3 => ⟨((988819962677967/1125899906842624), (-150040365895253/1125899906842624)), (272777/562949953421312), by norm_num⟩
  | 4 => ⟨((1696869857412641/2251799813685248), (-527090936247747/2251799813685248)), (2207337/2251799813685248), by norm_num⟩
  | 5 => ⟨((577658467264779/1125899906842624), (-794390972411039/2251799813685248)), (136253/70368744177664), by norm_num⟩
  | 6 => ⟨((312505666749727/2251799813685248), (-815146477485375/2251799813685248)), (7550329/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-4378267007/134217728)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-320962607/268435456), (-22099031391/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1292336263998191/4503599627370496), (431063908995751/4503599627370496)), (7353429/2251799813685248), by norm_num⟩
  | 1 => ⟨((13668506435/34359738368), (-4559184771/34359738368)), (157/34359738368), by norm_num⟩
  | 2 => ⟨((-4737143349/17179869184), (6320372139/68719476736)), (55/17179869184), by norm_num⟩
  | 3 => ⟨((4378050075/34359738368), (-5841264171/137438953472)), (205/137438953472), by norm_num⟩
  | 4 => ⟨((-24277064527/549755813888), (4048855791/274877906944)), (143/274877906944), by norm_num⟩
  | 5 => ⟨((1682757883/137438953472), (-2245162381/549755813888)), (161/1099511627776), by norm_num⟩
  | 6 => ⟨((-24883176153/8796093022208), (4149941265/4398046511104)), (75/2199023255552), by norm_num⟩
  | 7 => ⟨((9855830511/17592186044416), (-6574903057/35184372088832)), (15/2199023255552), by norm_num⟩
  | 8 => ⟨((-6831541131/70368744177664), (1139343879/35184372088832)), (21/17592186044416), by norm_num⟩
  | 9 => ⟨((263070193/17592186044416), (-5615879093/1125899906842624)), (209/1125899906842624), by norm_num⟩
  | 10 => ⟨((-18672267527/9007199254740992), (97315769/140737488355328)), (117/4503599627370496), by norm_num⟩
  | 11 => ⟨((9412821521/36028797018963968), (-3139684115/36028797018963968)), (119/36028797018963968), by norm_num⟩
  | 12 => ⟨((-17398588529/576460752303423488), (5803368513/576460752303423488)), (111/288230376151711744), by norm_num⟩
  | 13 => ⟨((14842809335/4611686018427387904), (-2475439091/2305843009213693952)), (191/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-23516003297/73786976294838206464), (7843856579/73786976294838206464)), (305/73786976294838206464), by norm_num⟩
  | 15 => ⟨((4346680369/147573952589676412928), (-5799410211/590295810358705651712)), (227/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-24103113941/9444732965739290427392), (8039689673/9444732965739290427392)), (317/9444732965739290427392), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (1836450254447/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780114905596375/633825300114114700748351602688), (4352991991833/633825300114114700748351602688)), (2895/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891255487542941/39614081257132168796771975168), (2448283540263/19807040628566084398385987584)), (1629/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891124216903103/2475880078570760549798248448), (5201964425475/2475880078570760549798248448)), (1731/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221598675265027/19342813113834066795298816), (5201246365351/154742504910672534362390528)), (6927/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551051089981557/9671406556917033397649408), (1218851353065/2417851639229258349412352)), (203/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1260098010098523/604462909807314587353088), (4265216549579/604462909807314587353088)), (5687/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889917582498037/75557863725914323419136), (6929545641257/75557863725914323419136)), (9245/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299131753682939/4722366482869645213696), (649488326031/590295810358705651712)), (3469/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811817259002439/295147905179352825856), (7142335555289/590295810358705651712)), (4773/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913101555085773/36893488147419103232), (4462432245373/36893488147419103232)), (5971/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825720233052795/9223372036854775808), (313633453781/288230376151711744)), (13447/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798480486645709/576460752303423488), (10031015782581/1152921504606846976)), (13463/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197175259213589/144115188075855872), (137050378345/2251799813685248)), (11799/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495511716001515/36028797018963968), (13144999620541/36028797018963968)), (17735/36028797018963968), by norm_num⟩
  | 3 => ⟨((747035062903439/4503599627370496), (4102629620347/2251799813685248)), (22233/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118740922796209/2251799813685248), (8189694235977/1125899906842624)), (11165/1125899906842624), by norm_num⟩
  | 1 => ⟨((557544332573641/562949953421312), (24491141503997/1125899906842624)), (16869/562949953421312), by norm_num⟩
  | 0 => ⟨((1103988277755485/1125899906842624), (24334914031589/562949953421312)), (34225/562949953421312), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1103988277755485/1125899906842624), (24334914031589/562949953421312)), (130558016063499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((540199602942081/562949953421312), (47722643314539/562949953421312)), (140155/1125899906842624), by norm_num⟩
  | 2 => ⟨((257161545688205/281474976710656), (183176162024243/1125899906842624)), (292745/1125899906842624), by norm_num⟩
  | 3 => ⟨((227497901174715/281474976710656), (167353650792945/562949953421312)), (157543/281474976710656), by norm_num⟩
  | 4 => ⟨((635985258135017/1125899906842624), (541044248469137/1125899906842624)), (696665/562949953421312), by norm_num⟩
  | 5 => ⟨((49626245230319/562949953421312), (611237577930109/1125899906842624)), (2913209/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1292336263998191/4503599627370496), (431063908995751/4503599627370496)), (7353429/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-22099031391/536870912)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-745252095/536870912), (-25656180927/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-221180566764375/1125899906842624), (692997821838977/4503599627370496)), (1577977/562949953421312), by norm_num⟩
  | 1 => ⟨((10863537281/34359738368), (-4254672881/17179869184)), (157/34359738368), by norm_num⟩
  | 2 => ⟨((-17484188763/68719476736), (13695263679/68719476736)), (255/68719476736), by norm_num⟩
  | 3 => ⟨((9379905421/68719476736), (-14694451057/137438953472)), (275/137438953472), by norm_num⟩
  | 4 => ⟨((-15096375399/274877906944), (11824903317/274877906944)), (7/8589934592), by norm_num⟩
  | 5 => ⟨((9718671563/549755813888), (-1903144771/137438953472)), (73/274877906944), by norm_num⟩
  | 6 => ⟨((-10427732315/2199023255552), (8167982259/2199023255552)), (159/2199023255552), by norm_num⟩
  | 7 => ⟨((149846319/137438953472), (-15023840361/17592186044416)), (295/17592186044416), by norm_num⟩
  | 8 => ⟨((-15434774197/70368744177664), (6044984567/35184372088832)), (15/4398046511104), by norm_num⟩
  | 9 => ⟨((11040582561/281474976710656), (-540501519/17592186044416)), (173/281474976710656), by norm_num⟩
  | 10 => ⟨((-14215305719/2251799813685248), (5567383273/1125899906842624)), (7/70368744177664), by norm_num⟩
  | 11 => ⟨((2079877451/2251799813685248), (-6516623791/9007199254740992)), (33/2251799813685248), by norm_num⟩
  | 12 => ⟨((-8926489661/72057594037927936), (13984135187/144115188075855872)), (285/144115188075855872), by norm_num⟩
  | 13 => ⟨((17682007243/1152921504606846976), (-13850213749/1152921504606846976)), (71/288230376151711744), by norm_num⟩
  | 14 => ⟨((-508180229/288230376151711744), (12737748059/9223372036854775808)), (263/9223372036854775808), by norm_num⟩
  | 15 => ⟨((436205081/2305843009213693952), (-1366707643/9223372036854775808)), (227/73786976294838206464), by norm_num⟩
  | 16 => ⟨((-11232719919/590295810358705651712), (8798524383/590295810358705651712)), (23/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (3226727333577/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779820137029007/633825300114114700748351602688), (3822990368925/633825300114114700748351602688)), (5787/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59091376618801/1237940039285380274899124224), (4300316300367/39614081257132168796771975168)), (6511/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118173267751471/154742504910672534362390528), (2284218355929/1237940039285380274899124224)), (865/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((110777357126749/9671406556917033397649408), (2283853055173/77371252455336267181195264)), (6923/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550721642435441/9671406556917033397649408), (535181025749/1208925819614629174706176)), (1623/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314952500871043/151115727451828646838272), (234093181145/37778931862957161709568)), (2841/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236181257389733/9444732965739290427392), (6084967161291/75557863725914323419136)), (9237/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162347692185565/590295810358705651712), (4562451746449/4722366482869645213696)), (1733/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202894207915239/73786976294838206464), (3135650737675/295147905179352825856)), (9537/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456400770084833/18446744073709551616), (7836022268015/73786976294838206464)), (11929/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825046626867271/9223372036854775808), (4405628080229/4611686018427387904)), (13431/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596289150436811/1152921504606846976), (8805919902191/1152921504606846976)), (6723/576460752303423488), by norm_num⟩
  | 5 => ⟨((598294709619147/72057594037927936), (7699176431405/144115188075855872)), (11781/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494636963013197/36028797018963968), (1442094652295/4503599627370496)), (2213/4503599627370496), by norm_num⟩
  | 3 => ⟨((1492983689845869/9007199254740992), (14399932532133/9007199254740992)), (11093/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117664980827233/2251799813685248), (14368409691235/2251799813685248)), (87/8796093022208), by norm_num⟩
  | 1 => ⟨((556750469099661/562949953421312), (21473801510755/1125899906842624)), (8405/281474976710656), by norm_num⟩
  | 0 => ⟨((1100917271994781/1125899906842624), (42632319903311/1125899906842624)), (133/2199023255552), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100917271994781/1125899906842624), (42632319903311/1125899906842624)), (507354744716733/8388608000000000000000000), by norm_num⟩
  | 1 => ⟨((1074874700425081/1125899906842624), (83372699547301/1125899906842624)), (17291/140737488355328), by norm_num⟩
  | 2 => ⟨((127498524469705/140737488355328), (159188583114541/1125899906842624)), (284605/1125899906842624), by norm_num⟩
  | 3 => ⟨((901532106292989/1125899906842624), (144213952492059/562949953421312)), (596145/1125899906842624), by norm_num⟩
  | 4 => ⟨((323993934926901/562949953421312), (923801539066481/2251799813685248)), (39379/35184372088832), by norm_num⟩
  | 5 => ⟨((366881562609699/2251799813685248), (1063348860461405/2251799813685248)), (4968833/2251799813685248), by norm_num⟩
  | 6 => ⟨((-221180566764375/1125899906842624), (692997821838977/4503599627370496)), (1577977/562949953421312), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-25656180927/536870912)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-28562583723/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-940163721409765/4503599627370496), (-195594454660697/4503599627370496)), (10169881/4503599627370496), by norm_num⟩
  | 1 => ⟨((25704151161/68719476736), (5347567997/68719476736)), (35/8589934592), by norm_num⟩
  | 2 => ⟨((-23027828121/68719476736), (-2395388899/34359738368)), (63/17179869184), by norm_num⟩
  | 3 => ⟨((27506886061/137438953472), (5722614323/137438953472)), (303/137438953472), by norm_num⟩
  | 4 => ⟨((-24642861785/274877906944), (-5126774201/274877906944)), (273/274877906944), by norm_num⟩
  | 5 => ⟨((17661632381/549755813888), (3674378489/549755813888)), (197/549755813888), by norm_num⟩
  | 6 => ⟨((-10548465687/1099511627776), (-4389068301/2199023255552)), (237/2199023255552), by norm_num⟩
  | 7 => ⟨((21600358035/8796093022208), (561725335/1099511627776)), (61/2199023255552), by norm_num⟩
  | 8 => ⟨((-1209457689/2199023255552), (-62904793/549755813888)), (221/35184372088832), by norm_num⟩
  | 9 => ⟨((15410185009/140737488355328), (3205980687/140737488355328)), (89/70368744177664), by norm_num⟩
  | 10 => ⟨((-11044537965/562949953421312), (-4595477003/1125899906842624)), (257/1125899906842624), by norm_num⟩
  | 11 => ⟨((7196056539/2251799813685248), (2994177977/4503599627370496)), (169/4503599627370496), by norm_num⟩
  | 12 => ⟨((-17191469927/36028797018963968), (-3576564495/36028797018963968)), (51/9007199254740992), by norm_num⟩
  | 13 => ⟨((4738919851/72057594037927936), (1971797939/144115188075855872)), (227/288230376151711744), by norm_num⟩
  | 14 => ⟨((-19408010325/2305843009213693952), (-4037700147/2305843009213693952)), (117/1152921504606846976), by norm_num⟩
  | 15 => ⟨((9273196341/9223372036854775808), (964611663/4611686018427387904)), (225/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-8307668677/73786976294838206464), (-3456704163/147573952589676412928)), (203/147573952589676412928), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-3825087280935/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779574314490195/633825300114114700748351602688), (-2265372856883/316912650057057350374175801344)), (5791/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890647357067821/39614081257132168796771975168), (-5096362019209/39614081257132168796771975168)), (6517/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890478106706301/2475880078570760549798248448), (-169188350945/77371252455336267181195264)), (3463/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((6922434859565/604462909807314587353088), (-2706531233773/77371252455336267181195264)), (6929/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550445426030603/9671406556917033397649408), (-5073720957121/9671406556917033397649408)), (3249/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39361502765753/18889465931478580854784), (-2219240339783/302231454903657293676544)), (711/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889056524595119/75557863725914323419136), (-1802652205947/18889465931478580854784)), (289/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649243008557809/2361183241434822606848), (-5406274513513/4722366482869645213696)), (1735/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622746723105151/590295810358705651712), (-3715446916761/295147905179352825856)), (9549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825093506711917/73786976294838206464), (-9284516505027/73786976294838206464)), (11945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824472123258439/9223372036854775808), (-10439441916751/9223372036854775808)), (3363/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595713108172745/1152921504606846976), (-2608098032681/288230376151711744)), (13469/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196083655314117/144115188075855872), (-9120410952811/144115188075855872)), (5903/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493874873345973/36028797018963968), (-13664749261365/36028797018963968)), (8873/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492025073868877/9007199254740992), (-4263290682825/2251799813685248)), (22249/9007199254740992), by norm_num⟩
  | 2 => ⟨((279174351106275/562949953421312), (-8505744803401/1125899906842624)), (22351/2251799813685248), by norm_num⟩
  | 1 => ⟨((139003416416651/140737488355328), (-12706504730353/562949953421312)), (33779/1125899906842624), by norm_num⟩
  | 0 => ⟨((274470510199631/281474976710656), (-787638674151/17592186044416)), (34287/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274470510199631/281474976710656), (-787638674151/17592186044416)), (130794527293968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((133538060699765/140737488355328), (-12288614285989/140737488355328)), (139877/1125899906842624), by norm_num⟩
  | 2 => ⟨((251267857924863/281474976710656), (-93279920772511/562949953421312)), (289871/1125899906842624), by norm_num⟩
  | 3 => ⟨((433148631780381/562949953421312), (-83269376744645/281474976710656)), (613589/1125899906842624), by norm_num⟩
  | 4 => ⟨((568017031808131/1125899906842624), (-1025114687710927/2251799813685248)), (2614525/2251799813685248), by norm_num⟩
  | 5 => ⟨((53227038495819/1125899906842624), (-1034341682839965/2251799813685248)), (313659/140737488355328), by norm_num⟩
  | 6 => ⟨((-940163721409765/4503599627370496), (-195594454660697/4503599627370496)), (10169881/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-28562583723/536870912)), (1/268435456), by norm_num⟩, -8, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-901055955/536870912), (-31019912273/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((280673770142489/4503599627370496), (-1585016406528949/9007199254740992)), (14872191/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1041728855/8589934592), (23531337829/68719476736)), (223/68719476736), by norm_num⟩
  | 2 => ⟨((4054221503/34359738368), (-22894934551/68719476736)), (219/68719476736), by norm_num⟩
  | 3 => ⟨((-2629716923/34359738368), (232038987/1073741824)), (9/4294967296), by norm_num⟩
  | 4 => ⟨((2558596425/68719476736), (-14448864633/137438953472)), (71/68719476736), by norm_num⟩
  | 5 => ⟨((-7966078001/549755813888), (11246476933/274877906944)), (223/549755813888), by norm_num⟩
  | 6 => ⟨((5167090677/1099511627776), (-14589755737/1099511627776)), (73/549755813888), by norm_num⟩
  | 7 => ⟨((-5745539537/4398046511104), (4055764823/1099511627776)), (41/1099511627776), by norm_num⟩
  | 8 => ⟨((698768981/2199023255552), (-15784307863/17592186044416)), (161/17592186044416), by norm_num⟩
  | 9 => ⟨((-4834636985/70368744177664), (13651042163/70368744177664)), (35/17592186044416), by norm_num⟩
  | 10 => ⟨((7526215341/562949953421312), (-2656370149/70368744177664)), (55/140737488355328), by norm_num⟩
  | 11 => ⟨((-5325577751/2251799813685248), (1879657321/281474976710656)), (157/2251799813685248), by norm_num⟩
  | 12 => ⟨((3454365265/9007199254740992), (-19507436041/18014398509481984)), (205/18014398509481984), by norm_num⟩
  | 13 => ⟨((-8273088527/144115188075855872), (23359826323/144115188075855872)), (31/18014398509481984), by norm_num⟩
  | 14 => ⟨((4599624837/576460752303423488), (-12987463749/576460752303423488)), (139/576460752303423488), by norm_num⟩
  | 15 => ⟨((-4773576881/4611686018427387904), (105301823/36028797018963968)), (73/2305843009213693952), by norm_num⟩
  | 16 => ⟨((2322237925/18446744073709551616), (-6557052355/18446744073709551616)), (143/36893488147419103232), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-1602761198993/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444844560332303/158456325028528675187087900672), (-1898025036583/633825300114114700748351602688)), (5775/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890427332555517/39614081257132168796771975168), (-266870050113/4951760157141521099596496896)), (3249/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236280629643733/309485009821345068724781056), (-2268006801299/2475880078570760549798248448)), (6905/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442977762233839/38685626227668133590597632), (-566892423407/38685626227668133590597632)), (3453/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775114255911711/4835703278458516698824704), (-265672782367/1208925819614629174706176)), (6475/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259379131852365/604462909807314587353088), (-929622629013/302231454903657293676544)), (5667/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944375525133701/37778931862957161709568), (-1510201684429/37778931862957161709568)), (4605/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298258293154581/4722366482869645213696), (-141533834839/295147905179352825856)), (6909/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622435846338595/590295810358705651712), (-778126976413/147573952589676412928)), (4751/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824708273263507/73786976294838206464), (-3888780959195/73786976294838206464)), (5941/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456010838547441/2305843009213693952), (-1093082670823/2305843009213693952)), (13373/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797645052485875/576460752303423488), (-4369147685043/1152921504606846976)), (3345/288230376151711744), by norm_num⟩
  | 5 => ⟨((149465000504285/18014398509481984), (-3819425923541/144115188075855872)), (2929/36028797018963968), by norm_num⟩
  | 4 => ⟨((186667790534701/4503599627370496), (-5721988710491/36028797018963968)), (8795/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491381954620819/9007199254740992), (-1784996883299/2251799813685248)), (22015/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116088022569683/2251799813685248), (-7121268878961/2251799813685248)), (22057/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111197205998841/1125899906842624), (-10635207648829/1125899906842624)), (66383/2251799813685248), by norm_num⟩
  | 0 => ⟨((274138801540569/281474976710656), (-21084237554835/1125899906842624)), (133617/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274138801540569/281474976710656), (-21084237554835/1125899906842624)), (509708413130950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((266895122688809/281474976710656), (-41069424232483/1125899906842624)), (132637/1125899906842624), by norm_num⟩
  | 2 => ⟨((2021567636195703/2251799813685248), (-38942108273287/562949953421312)), (130605/562949953421312), by norm_num⟩
  | 3 => ⟨((451024984356517/562949953421312), (-139842103711107/1125899906842624)), (1010289/2251799813685248), by norm_num⟩
  | 4 => ⟨((1410673057628809/2251799813685248), (-448155522567251/2251799813685248)), (233727/281474976710656), by norm_num⟩
  | 5 => ⟨((794544476040343/2251799813685248), (-70188401903113/281474976710656)), (3087013/2251799813685248), by norm_num⟩
  | 6 => ⟨((280673770142489/4503599627370496), (-1585016406528949/9007199254740992)), (14872191/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-31019912273/536870912)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-962887821/536870912), (-16574273543/268435456)), (3/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((695887883648261/9007199254740992), (1327187820491085/9007199254740992)), (18689545/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2760044429/17179869184), (-5263918853/17179869184)), (299/68719476736), by norm_num⟩
  | 2 => ⟨((11478702085/68719476736), (10946011535/34359738368)), (313/68719476736), by norm_num⟩
  | 3 => ⟨((-7956429987/68719476736), (-3793598517/17179869184)), (219/68719476736), by norm_num⟩
  | 4 => ⟨((8272465519/137438953472), (15777132697/137438953472)), (115/68719476736), by norm_num⟩
  | 5 => ⟨((-6880843381/274877906944), (-1640381257/34359738368)), (193/274877906944), by norm_num⟩
  | 6 => ⟨((9538874379/1099511627776), (18192410293/1099511627776)), (135/549755813888), by norm_num⟩
  | 7 => ⟨((-11334589511/4398046511104), (-21617173547/4398046511104)), (81/1099511627776), by norm_num⟩
  | 8 => ⟨((736550509/1099511627776), (2809478043/2199023255552)), (85/4398046511104), by norm_num⟩
  | 9 => ⟨((-10891475385/70368744177664), (-20772072367/70368744177664)), (317/70368744177664), by norm_num⟩
  | 10 => ⟨((4529637273/140737488355328), (17277724075/281474976710656)), (133/140737488355328), by norm_num⟩
  | 11 => ⟨((-6850266119/1125899906842624), (-13064733523/1125899906842624)), (51/281474976710656), by norm_num⟩
  | 12 => ⟨((9496485293/9007199254740992), (18111566413/9007199254740992)), (285/9007199254740992), by norm_num⟩
  | 13 => ⟨((-6076118775/36028797018963968), (-5794145167/18014398509481984)), (23/4503599627370496), by norm_num⟩
  | 14 => ⟨((7219962167/288230376151711744), (13769812753/288230376151711744)), (221/288230376151711744), by norm_num⟩
  | 15 => ⟨((-250224821/72057594037927936), (-15271211019/2305843009213693952)), (31/288230376151711744), by norm_num⟩
  | 16 => ⟨((8325246201/18446744073709551616), (3969448823/4611686018427387904)), (65/4611686018427387904), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790819754617223/5070602400912917605986812821504), (1417075572611/10141204801825835211973625643008)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779201018220619/633825300114114700748351602688), (1677813275653/633825300114114700748351602688)), (2165/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945114005885063/19807040628566084398385987584), (943620564633/19807040628566084398385987584)), (9743/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236254165926981/309485009821345068724781056), (1002413345721/1237940039285380274899124224)), (10353/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442924854087429/38685626227668133590597632), (2004413914447/154742504910672534362390528)), (10355/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550030188218187/9671406556917033397649408), (939349787461/4835703278458516698824704)), (9709/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314801420152989/151115727451828646838272), (1643423777071/604462909807314587353088)), (8497/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944234672763927/37778931862957161709568), (5214339809/147573952589676412928)), (6905/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298047148872343/4722366482869645213696), (2001587790557/4722366482869645213696)), (1295/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622145741025251/590295810358705651712), (2751015804117/590295810358705651712)), (1781/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824345968527595/73786976294838206464), (3437019471187/73786976294838206464)), (17815/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455909052630541/2305843009213693952), (1932120804683/4611686018427387904)), (10025/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797441761126059/576460752303423488), (1930618502877/576460752303423488)), (20059/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298841218632677/36028797018963968), (1687602485663/72057594037927936)), (8781/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492810889049945/36028797018963968), (2528029780181/18014398509481984)), (6591/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490719860008321/9007199254740992), (6308281189131/9007199254740992)), (32993/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115429219346975/2251799813685248), (3145311188857/1125899906842624)), (33049/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220434405160163/2251799813685248), (18783790325347/2251799813685248)), (24857/562949953421312), by norm_num⟩
  | 0 => ⟨((2189255685941233/2251799813685248), (18608287200149/1125899906842624)), (199987/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189255685941233/2251799813685248), (18608287200149/1125899906842624)), (762889870650481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1063916817981775/1125899906842624), (565357463047/17592186044416)), (98869/562949953421312), by norm_num⟩
  | 2 => ⟨((2008366441953263/2251799813685248), (68381872677857/1125899906842624)), (193207/562949953421312), by norm_num⟩
  | 3 => ⟨((1782943323256475/2251799813685248), (121978745614485/1125899906842624)), (736219/1125899906842624), by norm_num⟩
  | 4 => ⟨((1385279285245615/2251799813685248), (386324199426273/2251799813685248)), (2650757/2251799813685248), by norm_num⟩
  | 5 => ⟨((392963952726311/1125899906842624), (475323701158381/2251799813685248)), (4170967/2251799813685248), by norm_num⟩
  | 6 => ⟨((695887883648261/9007199254740992), (1327187820491085/9007199254740992)), (18689545/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-962887821/536870912), (-16574273543/268435456)), (3/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨50,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile050Terms0
