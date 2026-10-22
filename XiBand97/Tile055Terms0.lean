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
namespace Reinmann.XiBand97.Tile055Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨55,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (77803/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (77803/2560))
  have he : value ((69/80), (77803/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-320962607/536870912), (-22619432719/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-745205723589217/2251799813685248), (-989200770155337/2251799813685248)), (3421003/1125899906842624), by norm_num⟩
  | 1 => ⟨((7881732883/34359738368), (2615591907/8589934592)), (37/17179869184), by norm_num⟩
  | 2 => ⟨((-2731600463/34359738368), (-14503921247/137438953472)), (13/17179869184), by norm_num⟩
  | 3 => ⟨((10098139517/549755813888), (13404469493/549755813888)), (49/274877906944), by norm_num⟩
  | 4 => ⟨((-6999496935/2199023255552), (-2322817559/549755813888)), (139/4398046511104), by norm_num⟩
  | 5 => ⟨((7762690505/17592186044416), (10304348429/17592186044416)), (79/17592186044416), by norm_num⟩
  | 6 => ⟨((-7174249383/140737488355328), (-19046480163/281474976710656)), (37/70368744177664), by norm_num⟩
  | 7 => ⟨((2841606133/562949953421312), (3772004007/562949953421312)), (15/281474976710656), by norm_num⟩
  | 8 => ⟨((-3939302559/9007199254740992), (-5229107885/9007199254740992)), (85/18014398509481984), by norm_num⟩
  | 9 => ⟨((9708502977/288230376151711744), (6443629133/144115188075855872)), (107/288230376151711744), by norm_num⟩
  | 10 => ⟨((-5383537173/2305843009213693952), (-3573106693/1152921504606846976)), (121/4611686018427387904), by norm_num⟩
  | 11 => ⟨((10855515965/73786976294838206464), (14409825921/73786976294838206464)), (31/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-5016313523/590295810358705651712), (-6658753473/590295810358705651712)), (117/1180591620717411303424), by norm_num⟩
  | 13 => ⟨((8558876493/18889465931478580854784), (11361221405/18889465931478580854784)), (51/9444732965739290427392), by norm_num⟩
  | 14 => ⟨((-423754365/18889465931478580854784), (-17999996765/604462909807314587353088)), (41/151115727451828646838272), by norm_num⟩
  | 15 => ⟨((10025784093/9671406556917033397649408), (13308423475/9671406556917033397649408)), (123/9671406556917033397649408), by norm_num⟩
  | 16 => ⟨((-6949343977/154742504910672534362390528), (-18449392419/309485009821345068724781056)), (173/309485009821345068724781056), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481737/10141204801825835211973625643008), (-1443575330005/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222630271839579/79228162514264337593543950336), (-1712560106195/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946149399476503/19807040628566084398385987584), (-3853038965177/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892232918043581/2475880078570760549798248448), (-4093602402061/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773898308678395/154742504910672534362390528), (-4093319356267/154742504910672534362390528)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552090907926565/9671406556917033397649408), (-3837186062917/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630504034305783/302231454903657293676544), (-839309215481/151115727451828646838272)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1891396835477183/75557863725914323419136), (-1363736349895/18889465931478580854784)), (4617/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650120774912711/2361183241434822606848), (-255669679919/295147905179352825856)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625161065925925/590295810358705651712), (-2811964747279/295147905179352825856)), (4765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457028040192321/18446744073709551616), (-7028705910517/73786976294838206464)), (745/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1827869102641441/9223372036854775808), (-3952817359939/4611686018427387904)), (3355/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799555661732179/576460752303423488), (-987944822275/144115188075855872)), (1679/288230376151711744), by norm_num⟩
  | 5 => ⟨((599529237888135/72057594037927936), (-6913275548709/144115188075855872)), (1471/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498339847434003/36028797018963968), (-10365230546879/36028797018963968)), (1105/4503599627370496), by norm_num⟩
  | 3 => ⟨((46800345179405/281474976710656), (-6474164516423/4503599627370496)), (2769/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122290414462307/2251799813685248), (-3233996693913/562949953421312)), (11113/2251799813685248), by norm_num⟩
  | 1 => ⟨((280108529022321/281474976710656), (-9686512451969/562949953421312)), (16765/1125899906842624), by norm_num⟩
  | 0 => ⟨((139345342441509/140737488355328), (-19310816504427/562949953421312)), (33911/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139345342441509/140737488355328), (-19310816504427/562949953421312)), (129360203269576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((551205452353889/562949953421312), (-38239595861491/562949953421312)), (69479/1125899906842624), by norm_num⟩
  | 2 => ⟨((537108462618017/562949953421312), (-74883650337167/562949953421312)), (145499/1125899906842624), by norm_num⟩
  | 3 => ⟨((502492162596139/562949953421312), (-285784852194275/1125899906842624)), (158175/562949953421312), by norm_num⟩
  | 4 => ⟨((824514245446361/1125899906842624), (-255093099383997/562949953421312)), (725349/1125899906842624), by norm_num⟩
  | 5 => ⟨((745241705734129/2251799813685248), (-93404348414503/140737488355328)), (3439467/2251799813685248), by norm_num⟩
  | 6 => ⟨((-745205723589217/2251799813685248), (-989200770155337/2251799813685248)), (3421003/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/536870912), (-22619432719/1073741824)), (1/536870912), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-17925476323/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-341631680790485/2251799813685248), (-803374984790925/2251799813685248)), (4720725/1125899906842624), by norm_num⟩
  | 1 => ⟨((5726940349/34359738368), (6733685537/17179869184)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((-1572921761/17179869184), (-7397709679/34359738368)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((9216166271/274877906944), (21672572697/274877906944)), (33/34359738368), by norm_num⟩
  | 4 => ⟨((-632812095/68719476736), (-5952438673/274877906944)), (293/1099511627776), by norm_num⟩
  | 5 => ⟨((8898753843/4398046511104), (5231537819/1099511627776)), (65/1099511627776), by norm_num⟩
  | 6 => ⟨((-6517520217/17592186044416), (-15326484631/17592186044416)), (3/274877906944), by norm_num⟩
  | 7 => ⟨((511444843/8796093022208), (19243273551/140737488355328)), (243/140737488355328), by norm_num⟩
  | 8 => ⟨((-1123759179/140737488355328), (-21140896797/1125899906842624)), (269/1125899906842624), by norm_num⟩
  | 9 => ⟨((274350143/281474976710656), (10322510673/4503599627370496)), (265/9007199254740992), by norm_num⟩
  | 10 => ⟨((-7715953625/72057594037927936), (-2268087415/9007199254740992)), (235/72057594037927936), by norm_num⟩
  | 11 => ⟨((6164975615/576460752303423488), (1812180877/72057594037927936)), (95/288230376151711744), by norm_num⟩
  | 12 => ⟨((-9030557293/9223372036854775808), (-2654512241/1152921504606846976)), (281/9223372036854775808), by norm_num⟩
  | 13 => ⟨((1526320187/18446744073709551616), (14357069629/73786976294838206464)), (3/1152921504606846976), by norm_num⟩
  | 14 => ⟨((-3832763689/590295810358705651712), (-18026117855/1180591620717411303424)), (61/295147905179352825856), by norm_num⟩
  | 15 => ⟨((4491436041/9444732965739290427392), (2640495279/2361183241434822606848)), (289/18889465931478580854784), by norm_num⟩
  | 16 => ⟨((-9868693657/302231454903657293676544), (-23207044493/302231454903657293676544)), (5/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-2569889940329/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780503205124073/633825300114114700748351602688), (-3046988235439/633825300114114700748351602688)), (2891/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891692584259517/39614081257132168796771975168), (-3427561572841/39614081257132168796771975168)), (3253/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236448620314629/309485009821345068724781056), (-227589427601/154742504910672534362390528)), (3457/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773254519222317/154742504910672534362390528), (-3641033297445/154742504910672534362390528)), (1729/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96967970736215/604462909807314587353088), (-853261574771/2417851639229258349412352)), (6485/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315120072742777/151115727451828646838272), (-2985993064521/604462909807314587353088)), (5677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890539527770069/75557863725914323419136), (-1212861644483/18889465931478580854784)), (4613/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649799429338457/2361183241434822606848), (-3637891737171/4722366482869645213696)), (3461/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624277836328933/590295810358705651712), (-2500487288049/295147905179352825856)), (9523/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827008830011827/73786976294838206464), (-6249528169321/73786976294838206464)), (5955/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826628826845193/9223372036854775808), (-7028395035051/9223372036854775808)), (419/288230376151711744), by norm_num⟩
  | 6 => ⟨((1597872262140585/1152921504606846976), (-7025489338853/1152921504606846976)), (13419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197975663865151/144115188075855872), (-3072016787775/72057594037927936)), (11755/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496718364219803/36028797018963968), (-9209509459295/36028797018963968)), (8829/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495588979954281/9007199254740992), (-11500436409483/9007199254740992)), (5529/2251799813685248), by norm_num⟩
  | 2 => ⟨((1120275536159427/2251799813685248), (-11483253171611/2251799813685248)), (22185/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117429785139079/1125899906842624), (-8590947614233/562949953421312)), (16723/562949953421312), by norm_num⟩
  | 0 => ⟨((138603266116619/140737488355328), (-34191695504783/1125899906842624)), (33785/562949953421312), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((138603266116619/140737488355328), (-34191695504783/1125899906842624)), (128879549266624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((545486461406483/562949953421312), (-67346386899599/1125899906842624)), (137195/1125899906842624), by norm_num⟩
  | 2 => ⟨((1053101057453385/1125899906842624), (-130514416264213/1125899906842624)), (70573/281474976710656), by norm_num⟩
  | 3 => ⟨((969880020168867/1125899906842624), (-244151134475519/1125899906842624)), (296763/562949953421312), by norm_num⟩
  | 4 => ⟨((24454257426173/35184372088832), (-210318258124225/562949953421312)), (1279971/1125899906842624), by norm_num⟩
  | 5 => ⟨((193368825136221/562949953421312), (-1169423018289785/2251799813685248)), (5471273/2251799813685248), by norm_num⟩
  | 6 => ⟨((-341631680790485/2251799813685248), (-803374984790925/2251799813685248)), (4720725/1125899906842624), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-17925476323/536870912)), (1/268435456), by norm_num⟩, -5, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-320962607/268435456), (-22619432719/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-375865199591789/4503599627370496), (1309455789486297/4503599627370496)), (7237603/2251799813685248), by norm_num⟩
  | 1 => ⟨((496921355/4294967296), (-13849572579/34359738368)), (155/34359738368), by norm_num⟩
  | 2 => ⟨((-5511034179/68719476736), (19199584371/68719476736)), (217/68719476736), by norm_num⟩
  | 3 => ⟨((5093277071/137438953472), (-4436045925/34359738368)), (101/68719476736), by norm_num⟩
  | 4 => ⟨((-7060781283/549755813888), (12299330903/274877906944)), (283/549755813888), by norm_num⟩
  | 5 => ⟨((3915328511/1099511627776), (-13640394461/1099511627776)), (159/1099511627776), by norm_num⟩
  | 6 => ⟨((-3618531891/4398046511104), (25212802567/8796093022208)), (37/1099511627776), by norm_num⟩
  | 7 => ⟨((1433242959/8796093022208), (-19972780587/35184372088832)), (237/35184372088832), by norm_num⟩
  | 8 => ⟨((-248362079/8796093022208), (1730509569/17592186044416)), (83/70368744177664), by norm_num⟩
  | 9 => ⟨((2448376531/562949953421312), (-17059524675/1125899906842624)), (103/562949953421312), by norm_num⟩
  | 10 => ⟨((-2715336463/4503599627370496), (18919618289/9007199254740992)), (231/9007199254740992), by norm_num⟩
  | 11 => ⟨((342205057/4503599627370496), (-19075025563/72057594037927936)), (235/72057594037927936), by norm_num⟩
  | 12 => ⟨((-1265058509/144115188075855872), (8814533459/288230376151711744)), (219/576460752303423488), by norm_num⟩
  | 13 => ⟨((2158453511/2305843009213693952), (-7519715711/2305843009213693952)), (189/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-6839432985/73786976294838206464), (23827518829/73786976294838206464)), (151/36893488147419103232), by norm_num⟩
  | 15 => ⟨((5056782603/590295810358705651712), (-17617042663/590295810358705651712)), (225/590295810358705651712), by norm_num⟩
  | 16 => ⟨((-876273651/1180591620717411303424), (3052800863/1180591620717411303424)), (157/4722366482869645213696), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395604565464523/2535301200456458802993406410752), (1205124531933/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780120663933143/633825300114114700748351602688), (1428271041909/316912650057057350374175801344)), (5781/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945631152698299/19807040628566084398385987584), (3213260040701/39614081257132168796771975168)), (6505/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891131885712407/2475880078570760549798248448), (426708913713/309485009821345068724781056)), (6913/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886398774365685/77371252455336267181195264), (3413201636129/154742504910672534362390528)), (3457/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551059234906261/9671406556917033397649408), (3199377524699/9671406556917033397649408)), (6483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315026411043361/151115727451828646838272), (2798956346291/604462909807314587353088)), (2837/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472482734636217/18889465931478580854784), (1136842126501/18889465931478580854784)), (1153/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1299142602110401/4722366482869645213696), (3409707812901/4722366482869645213696)), (6921/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623650784764397/590295810358705651712), (4687018157551/590295810358705651712)), (595/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1826225467406959/73786976294838206464), (5856777719205/73786976294838206464)), (5953/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825748165256575/9223372036854775808), (6586132084209/9223372036854775808)), (6701/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596992377299105/1152921504606846976), (6582703889723/1152921504606846976)), (13413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197206638564259/144115188075855872), (2878004846213/72057594037927936)), (11749/144115188075855872), by norm_num⟩
  | 4 => ⟨((747783287186535/18014398509481984), (8626303391373/36028797018963968)), (8823/18014398509481984), by norm_num⟩
  | 3 => ⟨((747076151172851/4503599627370496), (5384693807719/4503599627370496)), (5525/2251799813685248), by norm_num⟩
  | 2 => ⟨((139855431138877/281474976710656), (10749155986111/2251799813685248)), (22163/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115293134399331/1125899906842624), (2009146925101/140737488355328)), (8351/281474976710656), by norm_num⟩
  | 0 => ⟨((1104598766549461/1125899906842624), (15972120418317/562949953421312)), (67445/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104598766549461/1125899906842624), (15972120418317/562949953421312)), (257282261375045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((135349287393445/140737488355328), (31339880936181/562949953421312)), (68083/562949953421312), by norm_num⟩
  | 2 => ⟨((129731197086933/140737488355328), (120560075393641/1125899906842624)), (277067/1125899906842624), by norm_num⟩
  | 3 => ⟨((943775734956661/1125899906842624), (222263493323395/1125899906842624)), (570135/1125899906842624), by norm_num⟩
  | 4 => ⟨((747234787316013/1125899906842624), (186310426433531/562949953421312)), (590461/562949953421312), by norm_num⟩
  | 5 => ⟨((93150715448649/281474976710656), (247300192538829/562949953421312)), (4698331/2251799813685248), by norm_num⟩
  | 6 => ⟨((-375865199591789/4503599627370496), (1309455789486297/4503599627370496)), (7237603/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-320962607/268435456), (-22619432719/536870912)), (1/268435456), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-745252095/536870912), (-102579485/2097152)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((244181053240339/4503599627370496), (137121928186843/562949953421312)), (10383495/4503599627370496), by norm_num⟩
  | 1 => ⟨((-5996616281/68719476736), (-26939603253/68719476736)), (257/68719476736), by norm_num⟩
  | 2 => ⟨((2412795397/34359738368), (10839404705/34359738368)), (209/68719476736), by norm_num⟩
  | 3 => ⟨((-2588829591/68719476736), (-11630232587/68719476736)), (227/137438953472), by norm_num⟩
  | 4 => ⟨((4166560493/274877906944), (2339767157/34359738368)), (185/274877906944), by norm_num⟩
  | 5 => ⟨((-5364656337/1099511627776), (-3012567975/137438953472)), (241/1099511627776), by norm_num⟩
  | 6 => ⟨((5756054197/4398046511104), (12929442967/2199023255552)), (261/4398046511104), by norm_num⟩
  | 7 => ⟨((-5293721057/17592186044416), (-23781869369/17592186044416)), (243/17592186044416), by norm_num⟩
  | 8 => ⟨((4259957683/70368744177664), (19137721095/70368744177664)), (99/35184372088832), by norm_num⟩
  | 9 => ⟨((-1523586089/140737488355328), (-53473913/1099511627776)), (143/281474976710656), by norm_num⟩
  | 10 => ⟨((3923387543/2251799813685248), (17625690707/2251799813685248)), (93/1125899906842624), by norm_num⟩
  | 11 => ⟨((-574040787/2251799813685248), (-20630876259/18014398509481984)), (219/18014398509481984), by norm_num⟩
  | 12 => ⟨((4927376031/144115188075855872), (11068038139/72057594037927936)), (237/144115188075855872), by norm_num⟩
  | 13 => ⟨((-1220047045/288230376151711744), (-5481021599/288230376151711744)), (237/1152921504606846976), by norm_num⟩
  | 14 => ⟨((1122051411/2305843009213693952), (20163117623/9223372036854775808)), (55/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-3852527105/73786976294838206464), (-17307352499/73786976294838206464)), (191/73786976294838206464), by norm_num⟩
  | 16 => ⟨((6200403181/1180591620717411303424), (27855109275/1180591620717411303424)), (155/590295810358705651712), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (880417199571/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779825618228651/633825300114114700748351602688), (521554213703/158456325028528675187087900672)), (361/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945465269217587/19807040628566084398385987584), (2346702226011/39614081257132168796771975168)), (6499/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890779580111889/2475880078570760549798248448), (2493017624223/2475880078570760549798248448)), (3453/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772445464469943/154742504910672534362390528), (2492619999641/154742504910672534362390528)), (6907/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387682347754751/2417851639229258349412352), (2336408835133/9671406556917033397649408)), (6477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78738579112931/37778931862957161709568), (510983846369/151115727451828646838272)), (1417/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236182845529287/9444732965739290427392), (1660301625605/37778931862957161709568)), (9213/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298791856690485/4722366482869645213696), (1244879902087/2361183241434822606848)), (27/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1623169135654723/590295810358705651712), (3422294476065/590295810358705651712)), (4753/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825624344274831/73786976294838206464), (4276180695975/73786976294838206464)), (11887/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912536595503139/4611686018427387904), (4808383893891/9223372036854775808)), (13379/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399079753349941/288230376151711744), (2402742917261/576460752303423488)), (13387/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196619255091337/144115188075855872), (1050385351669/36028797018963968)), (5861/72057594037927936), by norm_num⟩
  | 4 => ⟨((747344557388845/18014398509481984), (6295798758329/36028797018963968)), (17601/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493061795583501/9007199254740992), (3929179591903/4503599627370496)), (1377/562949953421312), by norm_num⟩
  | 2 => ⟨((2235524799531515/4503599627370496), (15682586976859/4503599627370496)), (44155/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227390273615203/2251799813685248), (23438679376475/2251799813685248)), (66465/2251799813685248), by norm_num⟩
  | 0 => ⟨((550748337258387/562949953421312), (23268659292209/1125899906842624)), (66931/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((550748337258387/562949953421312), (23268659292209/1125899906842624)), (255321506980514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2154282962625329/2251799813685248), (91057297989153/2251799813685248)), (267455/2251799813685248), by norm_num⟩
  | 2 => ⟨((2057307058729609/2251799813685248), (174227908261253/2251799813685248)), (4167/17592186044416), by norm_num⟩
  | 3 => ⟨((933066284210323/1125899906842624), (159179472045055/1125899906842624)), (1057153/2251799813685248), by norm_num⟩
  | 4 => ⟨((1501509292739763/2251799813685248), (527666793827707/2251799813685248)), (2051109/2251799813685248), by norm_num⟩
  | 5 => ⟨((877563759827039/2251799813685248), (351850368575101/1125899906842624)), (1848327/1125899906842624), by norm_num⟩
  | 6 => ⟨((244181053240339/4503599627370496), (137121928186843/562949953421312)), (10383495/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-102579485/2097152)), (1/268435456), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-29235192683/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-479716948756653/4503599627370496), (415943704972389/2251799813685248)), (5326693/2251799813685248), by norm_num⟩
  | 1 => ⟨((1639437457/8589934592), (-11371934083/34359738368)), (147/34359738368), by norm_num⟩
  | 2 => ⟨((-11749910351/68719476736), (20375770577/68719476736)), (265/68719476736), by norm_num⟩
  | 3 => ⟨((7017671045/68719476736), (-3042373323/17179869184)), (5/2147483648), by norm_num⟩
  | 4 => ⟨((-6286989273/137438953472), (10902402421/137438953472)), (145/137438953472), by norm_num⟩
  | 5 => ⟨((4505909025/274877906944), (-3906896555/137438953472)), (105/274877906944), by norm_num⟩
  | 6 => ⟨((-10764673551/2199023255552), (9333625197/1099511627776)), (253/2199023255552), by norm_num⟩
  | 7 => ⟨((11021546153/8796093022208), (-9556349331/4398046511104)), (261/8796093022208), by norm_num⟩
  | 8 => ⟨((-9873979843/35184372088832), (17122679405/35184372088832)), (59/8796093022208), by norm_num⟩
  | 9 => ⟨((7863020837/140737488355328), (-3408858107/35184372088832)), (189/140737488355328), by norm_num⟩
  | 10 => ⟨((-11270913633/1125899906842624), (2443141517/140737488355328)), (273/1125899906842624), by norm_num⟩
  | 11 => ⟨((1835887839/1125899906842624), (-12734609303/4503599627370496)), (179/4503599627370496), by norm_num⟩
  | 12 => ⟨((-8771918453/36028797018963968), (3802892801/9007199254740992)), (27/4503599627370496), by norm_num⟩
  | 13 => ⟨((9672103355/288230376151711744), (-16772601075/288230376151711744)), (15/18014398509481984), by norm_num⟩
  | 14 => ⟨((-4951452221/1152921504606846976), (4293209543/576460752303423488)), (31/288230376151711744), by norm_num⟩
  | 15 => ⟨((9463265497/18446744073709551616), (-16410450885/18446744073709551616)), (239/18446744073709551616), by norm_num⟩
  | 16 => ⟨((-4238973891/73786976294838206464), (918861899/9223372036854775808)), (27/18446744073709551616), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (1363754891167/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779579706289805/633825300114114700748351602688), (807671325381/158456325028528675187087900672)), (723/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236331716927299/4951760157141521099596496896), (1817006830565/19807040628566084398385987584)), (1627/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890485280831777/2475880078570760549798248448), (1930264719819/1237940039285380274899124224)), (1729/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772150944746339/154742504910672534362390528), (3859843131889/154742504910672534362390528)), (6917/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550453044691107/9671406556917033397649408), (3617873802107/9671406556917033397649408)), (6487/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78723451802117/37778931862957161709568), (1582455259577/302231454903657293676544)), (5677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889069015843491/75557863725914323419136), (1285403193201/18889465931478580854784)), (9229/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298496162196903/4722366482869645213696), (1927506886927/2361183241434822606848)), (6925/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811380966812945/295147905179352825856), (662337632449/73786976294838206464)), (4763/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825114409639151/73786976294838206464), (3310231269683/36893488147419103232)), (5957/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912249117305229/4611686018427387904), (7444014771049/9223372036854775808)), (13413/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398935614912123/288230376151711744), (7439009093765/1152921504606846976)), (13425/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196112977048633/144115188075855872), (50808620055/1125899906842624)), (11761/144115188075855872), by norm_num⟩
  | 4 => ⟨((746963059735793/18014398509481984), (4872000185521/18014398509481984)), (17669/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492101809257995/9007199254740992), (12160314923083/9007199254740992)), (11067/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116793089559265/2251799813685248), (6065403482287/1125899906842624)), (11103/1125899906842624), by norm_num⟩
  | 1 => ⟨((278054499871393/281474976710656), (4530628008593/281474976710656)), (2093/70368744177664), by norm_num⟩
  | 0 => ⟨((274612634012967/281474976710656), (35950661311657/1125899906842624)), (16925/281474976710656), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274612634012967/281474976710656), (35950661311657/1125899906842624)), (64563752294444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1070522452998449/1125899906842624), (35074186390113/562949953421312)), (17053/140737488355328), by norm_num⟩
  | 2 => ⟨((1013498199293841/1125899906842624), (133396241790495/1125899906842624)), (69107/281474976710656), by norm_num⟩
  | 3 => ⟨((896513123869651/1125899906842624), (240157850667857/1125899906842624)), (281583/562949953421312), by norm_num⟩
  | 4 => ⟨((662634381172747/1125899906842624), (95614478523159/281474976710656)), (2274215/2251799813685248), by norm_num⟩
  | 5 => ⟨((520135520538821/2251799813685248), (450181693220119/1125899906842624)), (4221983/2251799813685248), by norm_num⟩
  | 6 => ⟨((-479716948756653/4503599627370496), (415943704972389/2251799813685248)), (5326693/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-29235192683/536870912)), (1/268435456), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-901055955/536870912), (-31750387889/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-358254686302521/2251799813685248), (-109960599891693/1125899906842624)), (9424543/4503599627370496), by norm_num⟩
  | 1 => ⟨((21274762879/68719476736), (13059902791/68719476736)), (141/34359738368), by norm_num⟩
  | 2 => ⟨((-20699388503/68719476736), (-12706698693/68719476736)), (277/68719476736), by norm_num⟩
  | 3 => ⟨((13426383389/68719476736), (2060507829/17179869184)), (181/68719476736), by norm_num⟩
  | 4 => ⟨((-13063267851/137438953472), (-8019126193/137438953472)), (89/68719476736), by norm_num⟩
  | 5 => ⟨((20335956393/549755813888), (12483599237/549755813888)), (279/549755813888), by norm_num⟩
  | 6 => ⟨((-13190647979/1099511627776), (-8097320817/1099511627776)), (183/1099511627776), by norm_num⟩
  | 7 => ⟨((3666830825/1099511627776), (9003805005/4398046511104)), (205/4398046511104), by norm_num⟩
  | 8 => ⟨((-14270646635/17592186044416), (-4380148885/8796093022208)), (201/17592186044416), by norm_num⟩
  | 9 => ⟨((1542744229/8796093022208), (7576334373/70368744177664)), (11/4398046511104), by norm_num⟩
  | 10 => ⟨((-19213066577/562949953421312), (-11794292759/562949953421312)), (69/140737488355328), by norm_num⟩
  | 11 => ⟨((13595236817/2251799813685248), (2086421271/562949953421312)), (197/2251799813685248), by norm_num⟩
  | 12 => ⟨((-8818369767/9007199254740992), (-10826635537/18014398509481984)), (257/18014398509481984), by norm_num⟩
  | 13 => ⟨((10559849371/72057594037927936), (12964713829/144115188075855872)), (155/72057594037927936), by norm_num⟩
  | 14 => ⟨((-5871005161/288230376151711744), (-7208048063/576460752303423488)), (87/288230376151711744), by norm_num⟩
  | 15 => ⟨((6093039215/2305843009213693952), (7480647403/4611686018427387904)), (91/2305843009213693952), by norm_num⟩
  | 16 => ⟨((-11856506847/36893488147419103232), (-1819583463/9223372036854775808)), (179/36893488147419103232), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (-1687558288209/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((6950670418307/2475880078570760549798248448), (-1998443613263/316912650057057350374175801344)), (1447/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472604877666215/9903520314283042199192993792), (-4495812239315/39614081257132168796771975168)), (6513/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118139764968801/154742504910672534362390528), (-4775980150827/2475880078570760549798248448)), (3461/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885950851920023/77371252455336267181195264), (-4775057219473/154742504910672534362390528)), (1731/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193777396179433/1208925819614629174706176), (-139863611961/302231454903657293676544)), (6493/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629685188119853/302231454903657293676544), (-1957600317517/302231454903657293676544)), (1421/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944367866848099/37778931862957161709568), (-795045340473/9444732965739290427392)), (1155/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298245853830773/4722366482869645213696), (-4768663652647/4722366482869645213696)), (3467/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50700537399483/18446744073709551616), (-3277149565849/295147905179352825856)), (2385/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456170661361321/18446744073709551616), (-511809640989/4611686018427387904)), (11933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824011342389097/9223372036854775808), (-4603592351871/4611686018427387904)), (13437/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595254123269599/1152921504606846976), (-9200449710757/1152921504606846976)), (13451/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597842030889765/72057594037927936), (-502676130009/9007199254740992)), (11787/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493279514034511/36028797018963968), (-12049079933951/36028797018963968)), (8857/18014398509481984), by norm_num⟩
  | 3 => ⟨((46602747391457/281474976710656), (-15034850606651/9007199254740992)), (11101/4503599627370496), by norm_num⟩
  | 2 => ⟨((139496348108893/281474976710656), (-7497559158749/1125899906842624)), (22291/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110963659141185/1125899906842624), (-5598351445293/281474976710656)), (8415/281474976710656), by norm_num⟩
  | 0 => ⟨((273964799935587/281474976710656), (-5548760524491/140737488355328)), (68217/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((273964799935587/281474976710656), (-5548760524491/140737488355328)), (260227207664107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064869886566749/1125899906842624), (-337544451719/4398046511104)), (69087/562949953421312), by norm_num⟩
  | 2 => ⟨((500258034457249/562949953421312), (-10215925442857/70368744177664)), (282579/1125899906842624), by norm_num⟩
  | 3 => ⟨((865365494992337/1125899906842624), (-290503907206439/1125899906842624)), (584269/1125899906842624), by norm_num⟩
  | 4 => ⟨((1180326804865795/2251799813685248), (-893124001268959/2251799813685248)), (1199643/1125899906842624), by norm_num⟩
  | 5 => ⟨((33056939665711/281474976710656), (-234074581665743/562949953421312)), (276157/140737488355328), by norm_num⟩
  | 6 => ⟨((-358254686302521/2251799813685248), (-109960599891693/1125899906842624)), (9424543/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-31750387889/536870912)), (1/268435456), by norm_num⟩, -9, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-481443911/268435456), (-16964574539/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((87452909975143/562949953421312), (-536466694719731/9007199254740992)), (7950557/4503599627370496), by norm_num⟩
  | 1 => ⟨((-22198878655/68719476736), (531936231/4294967296)), (255/68719476736), by norm_num⟩
  | 2 => ⟨((23080635227/68719476736), (-4424521185/34359738368)), (67/17179869184), by norm_num⟩
  | 3 => ⟨((-15998277233/68719476736), (6133688769/68719476736)), (47/17179869184), by norm_num⟩
  | 4 => ⟨((16633741137/137438953472), (-6377323615/137438953472)), (197/137438953472), by norm_num⟩
  | 5 => ⟨((-6917778463/137438953472), (1326127165/68719476736)), (83/137438953472), by norm_num⟩
  | 6 => ⟨((9590077275/549755813888), (-1838402611/274877906944)), (233/1099511627776), by norm_num⟩
  | 7 => ⟨((-22790862941/4398046511104), (4368972297/2199023255552)), (35/549755813888), by norm_num⟩
  | 8 => ⟨((23696133585/17592186044416), (-9085022489/17592186044416)), (147/8796093022208), by norm_num⟩
  | 9 => ⟨((-5474969395/17592186044416), (8396343631/70368744177664)), (275/70368744177664), by norm_num⟩
  | 10 => ⟨((18215806079/281474976710656), (-3491941149/140737488355328)), (231/281474976710656), by norm_num⟩
  | 11 => ⟨((-13774074137/1125899906842624), (2640468177/562949953421312)), (177/1125899906842624), by norm_num⟩
  | 12 => ⟨((9547460653/4503599627370496), (-7320932289/9007199254740992)), (31/1125899906842624), by norm_num⟩
  | 13 => ⟨((-3054367123/9007199254740992), (4684138685/36028797018963968)), (5/1125899906842624), by norm_num⟩
  | 14 => ⟨((907339697/18014398509481984), (-5565938611/288230376151711744)), (3/4503599627370496), by norm_num⟩
  | 15 => ⟨((-16100350791/2305843009213693952), (6172823449/2305843009213693952)), (215/2305843009213693952), by norm_num⟩
  | 16 => ⟨((16739869135/18446744073709551616), (-6418012755/18446744073709551616)), (113/9223372036854775808), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395409877308005/2535301200456458802993406410752), (-238450797465/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779202353177125/633825300114114700748351602688), (-564650074151/633825300114114700748351602688)), (11533/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945114795008341/19807040628566084398385987584), (-635131250805/39614081257132168796771975168)), (12975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472508775631979/618970019642690137449562112), (-674703497553/2475880078570760549798248448)), (6893/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885850650944351/77371252455336267181195264), (-337282326057/77371252455336267181195264)), (13787/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550032073175095/9671406556917033397649408), (-19758027437/302231454903657293676544)), (6463/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259207447140783/604462909807314587353088), (-276538664881/302231454903657293676544)), (11311/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944236217858589/37778931862957161709568), (-898474309099/75557863725914323419136)), (18381/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649024829246381/2361183241434822606848), (-336807009685/2361183241434822606848)), (13787/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811074751714803/295147905179352825856), (-462913336287/295147905179352825856)), (9479/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456087784635667/18446744073709551616), (-1156694747151/73786976294838206464)), (5925/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911821334053895/4611686018427387904), (-1300472781941/9223372036854775808)), (13333/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594890780257955/1152921504606846976), (-1299462531979/1152921504606846976)), (13335/576460752303423488), by norm_num⟩
  | 5 => ⟨((597686062035945/72057594037927936), (-1135894229501/144115188075855872)), (23341/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492823556723215/36028797018963968), (-1701572982773/36028797018963968)), (35021/36028797018963968), by norm_num⟩
  | 3 => ⟨((186342352940635/1125899906842624), (-66343826949/281474976710656)), (43793/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230905714755613/4503599627370496), (-4234137056933/4503599627370496)), (21909/1125899906842624), by norm_num⟩
  | 1 => ⟨((2220528560077525/2251799813685248), (-197550555103/70368744177664)), (65791/1125899906842624), by norm_num⟩
  | 0 => ⟨((2189536171558247/2251799813685248), (-6262687025189/1125899906842624)), (263681/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2189536171558247/2251799813685248), (-6262687025189/1125899906842624)), (1005863198287200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2128924486285141/2251799813685248), (-24358079593867/2251799813685248)), (515715/2251799813685248), by norm_num⟩
  | 2 => ⟨((1006245343107659/1125899906842624), (-11514458738985/562949953421312)), (986305/2251799813685248), by norm_num⟩
  | 3 => ⟨((1797671983690995/2251799813685248), (-82326113815931/2251799813685248)), (225415/281474976710656), by norm_num⟩
  | 4 => ⟨((358029935913105/562949953421312), (-131446274605423/2251799813685248)), (1505569/1125899906842624), by norm_num⟩
  | 5 => ⟨((451569634363531/1125899906842624), (-41799187465049/562949953421312)), (4181645/2251799813685248), by norm_num⟩
  | 6 => ⟨((87452909975143/562949953421312), (-536466694719731/9007199254740992)), (7950557/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-481443911/268435456), (-16964574539/268435456)), (1/134217728), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨55,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile055Terms0
