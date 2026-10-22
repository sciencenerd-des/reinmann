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
namespace Reinmann.XiBand97.Tile003Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (9919/640)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (9919/640))
  have he : value ((69/80), (9919/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1441860553/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-77464118630237/562949953421312), (599549558758387/1125899906842624)), (51863671/2251799813685248), by norm_num⟩
  | 1 => ⟨((102413245/1073741824), (-24770265/67108864)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((-17746863/536870912), (549422059/4294967296)), (51/8589934592), by norm_num⟩
  | 3 => ⟨((262425345/34359738368), (-1015547603/34359738368)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((-45474847/34359738368), (351961979/68719476736)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((403465753/2199023255552), (-780676651/1099511627776)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((-93220383/4398046511104), (360749213/4398046511104)), (19/4398046511104), by norm_num⟩
  | 7 => ⟨((147692447/70368744177664), (-285774057/35184372088832)), (31/70368744177664), by norm_num⟩
  | 8 => ⟨((-409490413/2251799813685248), (1584667855/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 9 => ⟨((252299667/18014398509481984), (-244090679/4503599627370496)), (7/2251799813685248), by norm_num⟩
  | 10 => ⟨((-279809285/288230376151711744), (541410451/144115188075855872)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((282107661/4611686018427387904), (-68232205/288230376151711744)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-32590355/9223372036854775808), (504479579/36893488147419103232)), (1/1152921504606846976), by norm_num⟩
  | 13 => ⟨((55605939/295147905179352825856), (-430373659/590295810358705651712)), (7/147573952589676412928), by norm_num⟩
  | 14 => ⟨((-44049257/4722366482869645213696), (681856659/18889465931478580854784)), (91/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((260545009/604462909807314587353088), (-504135489/302231454903657293676544)), (69/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-361192077/19342813113834066795298816), (1397760371/19342813113834066795298816)), (49/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (2375536856083/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222630524155303/79228162514264337593543950336), (2818176208717/633825300114114700748351602688)), (1445/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((946150596208573/19807040628566084398385987584), (1585134883217/19807040628566084398385987584)), (13007/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892235610458247/2475880078570760549798248448), (1684102567907/1237940039285380274899124224)), (27645/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773901169105375/154742504910672534362390528), (1683986389403/77371252455336267181195264)), (27651/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552093768056833/9671406556917033397649408), (3157227553813/9671406556917033397649408)), (25929/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630505374834151/302231454903657293676544), (2762327130421/604462909807314587353088)), (11347/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472850381673849/18889465931478580854784), (280519899297/4722366482869645213696)), (36889/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300245360848285/4722366482869645213696), (3365833380969/4722366482869645213696)), (27677/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406291695355937/147573952589676412928), (2313680948199/295147905179352825856)), (4759/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828120017893453/73786976294838206464), (5783213499227/73786976294838206464)), (23807/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913939460758405/4611686018427387904), (3252377445871/4611686018427387904)), (1675/288230376151711744), by norm_num⟩
  | 6 => ⟨((799561183108847/576460752303423488), (6503053628651/1152921504606846976)), (26821/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199069514173477/144115188075855872), (5688256775575/144115188075855872)), (46985/144115188075855872), by norm_num⟩
  | 4 => ⟨((749179577408073/18014398509481984), (8528551797257/36028797018963968)), (70571/36028797018963968), by norm_num⟩
  | 3 => ⟨((46801249598731/281474976710656), (10653974466363/9007199254740992)), (88381/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122326556775245/2251799813685248), (665242987233/140737488355328)), (88631/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120506297080191/1125899906842624), (15940567020109/1125899906842624)), (133573/1125899906842624), by norm_num⟩
  | 0 => ⟨((278744690640269/281474976710656), (31779788398789/1125899906842624)), (269655/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278744690640269/281474976710656), (31779788398789/1125899906842624)), (1028652195457076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((551633266182153/562949953421312), (62943053690629/1125899906842624)), (549303/1125899906842624), by norm_num⟩
  | 2 => ⟨((1077569334586367/1125899906842624), (61677742541449/562949953421312)), (1137939/1125899906842624), by norm_num⟩
  | 3 => ⟨((127224796824351/140737488355328), (236120612801395/1125899906842624)), (2427533/1125899906842624), by norm_num⟩
  | 4 => ⟨((108819685211495/140737488355328), (26681232325475/70368744177664)), (2703553/562949953421312), by norm_num⟩
  | 5 => ⟨((255629722002623/562949953421312), (660166575178881/1125899906842624)), (3115503/281474976710656), by norm_num⟩
  | 6 => ⟨((-77464118630237/562949953421312), (599549558758387/1125899906842624)), (51863671/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1441860553/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-571323727/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-217662075340739/2251799813685248), (1690853976505213/4503599627370496)), (147009341/4503599627370496), by norm_num⟩
  | 1 => ⟨((228048545/2147483648), (-885769347/2147483648)), (79/2147483648), by norm_num⟩
  | 2 => ⟨((-125268467/2147483648), (486558545/2147483648)), (89/4294967296), by norm_num⟩
  | 3 => ⟨((183495303/8589934592), (-712718929/8589934592)), (133/17179869184), by norm_num⟩
  | 4 => ⟨((-201590195/34359738368), (391500887/17179869184)), (149/68719476736), by norm_num⟩
  | 5 => ⟨((354351145/274877906944), (-688172297/137438953472)), (133/274877906944), by norm_num⟩
  | 6 => ⟨((-129764841/549755813888), (1008046057/1099511627776)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((325854283/8796093022208), (-79103699/549755813888)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-5593555/1099511627776), (1390468733/70368744177664)), (143/70368744177664), by norm_num⟩
  | 9 => ⟨((349590657/562949953421312), (-84865891/35184372088832)), (71/281474976710656), by norm_num⟩
  | 10 => ⟨((-153625837/2251799813685248), (596702149/2251799813685248)), (127/4503599627370496), by norm_num⟩
  | 11 => ⟨((245491247/36028797018963968), (-476759501/18014398509481984)), (103/36028797018963968), by norm_num⟩
  | 12 => ⟨((-359599601/576460752303423488), (698365129/288230376151711744)), (153/576460752303423488), by norm_num⟩
  | 13 => ⟨((243114179/4611686018427387904), (-472143085/2305843009213693952)), (105/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-305243685/73786976294838206464), (592802509/36893488147419103232)), (67/36893488147419103232), by norm_num⟩
  | 15 => ⟨((357700761/1180591620717411303424), (-1389354925/1180591620717411303424)), (159/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((-98243613/4722366482869645213696), (763181197/9444732965739290427392)), (177/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (2374377097993/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780503929830801/633825300114114700748351602688), (1407589284379/316912650057057350374175801344)), (46239/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945846721418473/19807040628566084398385987584), (3166799825945/39614081257132168796771975168)), (52027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891589928289639/2475880078570760549798248448), (841099630681/618970019642690137449562112)), (27645/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110828471575391/9671406556917033397649408), (1682015706815/77371252455336267181195264)), (55301/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551488557595217/9671406556917033397649408), (1576694692077/4835703278458516698824704)), (51857/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260481252494715/604462909807314587353088), (1379412815355/302231454903657293676544)), (45387/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890541210078987/75557863725914323419136), (2241180109395/37778931862957161709568)), (73777/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299600225217827/4722366482869645213696), (3361130131629/4722366482869645213696)), (55353/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406069971388463/147573952589676412928), (2310256910853/295147905179352825856)), (76143/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827011646743011/73786976294838206464), (5774082014615/73786976294838206464)), (23807/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826632346329375/9223372036854775808), (3246848372949/4611686018427387904)), (53599/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597876219594035/1152921504606846976), (6491014606947/1152921504606846976)), (107283/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197979618860359/144115188075855872), (5676620048923/144115188075855872)), (5873/9007199254740992), by norm_num⟩
  | 4 => ⟨((11693166249447/281474976710656), (1063611724981/4503599627370496)), (70571/18014398509481984), by norm_num⟩
  | 3 => ⟨((747799671225557/4503599627370496), (5312775982547/4503599627370496)), (176761/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120288469906291/2251799813685248), (5304850231385/1125899906842624)), (177261/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117455594484819/1125899906842624), (15874909590383/1125899906842624)), (267145/1125899906842624), by norm_num⟩
  | 0 => ⟨((554451633027131/562949953421312), (15795590999683/562949953421312)), (539313/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554451633027131/562949953421312), (15795590999683/562949953421312)), (2057315830710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1091276802865419/1125899906842624), (31114279950383/562949953421312)), (1092609/1125899906842624), by norm_num⟩
  | 2 => ⟨((1054279034566761/1125899906842624), (30157469364157/281474976710656)), (1119399/562949953421312), by norm_num⟩
  | 3 => ⟨((243572432310617/281474976710656), (225912712083841/1125899906842624)), (4672501/1125899906842624), by norm_num⟩
  | 4 => ⟨((797765340921939/1125899906842624), (195492009325979/562949953421312)), (2490429/281474976710656), by norm_num⟩
  | 5 => ⟨((429488477080631/1125899906842624), (1108139354268577/2251799813685248)), (21035589/1125899906842624), by norm_num⟩
  | 6 => ⟨((-217662075340739/2251799813685248), (1690853976505213/4503599627370496)), (147009341/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-571323727/33554432)), (1/33554432), by norm_num⟩, -3, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1441860553/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-595891184763337/2251799813685248), (-660002941463703/4503599627370496)), (60373849/2251799813685248), by norm_num⟩
  | 1 => ⟨((787811841/2147483648), (218143071/1073741824)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-1092139113/4294967296), (-604821019/4294967296)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((1009350863/8589934592), (4366979/67108864)), (109/8589934592), by norm_num⟩
  | 4 => ⟨((-699628705/17179869184), (-387450775/17179869184)), (77/17179869184), by norm_num⟩
  | 5 => ⟨((775913063/68719476736), (107424165/17179869184)), (87/68719476736), by norm_num⟩
  | 6 => ⟨((-700289/268435456), (-198562019/137438953472)), (41/137438953472), by norm_num⟩
  | 7 => ⟨((1136121203/2199023255552), (314589037/1099511627776)), (33/549755813888), by norm_num⟩
  | 8 => ⟨((-787499209/8796093022208), (-27257063/549755813888)), (93/8796093022208), by norm_num⟩
  | 9 => ⟨((485202539/35184372088832), (537405337/70368744177664)), (29/17592186044416), by norm_num⟩
  | 10 => ⟨((-538106835/281474976710656), (-596001591/562949953421312)), (131/562949953421312), by norm_num⟩
  | 11 => ⟨((67815861/281474976710656), (150224299/1125899906842624)), (67/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1002802621/36028797018963968), (-277673465/18014398509481984)), (63/18014398509481984), by norm_num⟩
  | 13 => ⟨((427747575/144115188075855872), (473768811/288230376151711744)), (109/288230376151711744), by norm_num⟩
  | 14 => ⟨((-1355392117/4611686018427387904), (-750609179/4611686018427387904)), (175/4611686018427387904), by norm_num⟩
  | 15 => ⟨((1002118639/36893488147419103232), (554968145/36893488147419103232)), (33/9223372036854775808), by norm_num⟩
  | 16 => ⟨((-694615709/295147905179352825856), (-384674605/295147905179352825856)), (93/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-429184583965/1267650600228229401496703205376)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780116181150139/633825300114114700748351602688), (-4069235314123/633825300114114700748351602688)), (11575/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891256997795155/39614081257132168796771975168), (-4577379883057/39614081257132168796771975168)), (52101/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891125915650295/2475880078570760549798248448), (-4862870018651/2475880078570760549798248448)), (13843/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772791206707035/154742504910672534362390528), (-4862199250909/154742504910672534362390528)), (13847/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551052894194601/9671406556917033397649408), (-4557599028317/9671406556917033397649408)), (51945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260099701150991/604462909807314587353088), (-498398286481/75557863725914323419136)), (45469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889920541045081/75557863725914323419136), (-404865057989/4722366482869645213696)), (73921/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299134156757057/4722366482869645213696), (-4857210811511/4722366482869645213696)), (27735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811819060655605/295147905179352825856), (-6676763452915/590295810358705651712)), (38159/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826208062596547/73786976294838206464), (-4171550792107/36893488147419103232)), (95469/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825726420400865/9223372036854775808), (-4691032891521/4611686018427387904)), (26875/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596967929679009/1152921504606846976), (-1172144990553/144115188075855872)), (107623/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598591105062211/72057594037927936), (-8199493809001/144115188075855872)), (23577/36028797018963968), by norm_num⟩
  | 4 => ⟨((373880966941199/9007199254740992), (-1536024175153/4503599627370496)), (141737/36028797018963968), by norm_num⟩
  | 3 => ⟨((373522082192809/2251799813685248), (-239701525399/140737488355328)), (177655/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118763633268783/2251799813685248), (-7655929465197/1125899906842624)), (178381/2251799813685248), by norm_num⟩
  | 1 => ⟨((278783489057693/281474976710656), (-5723778393333/281474976710656)), (67347/281474976710656), by norm_num⟩
  | 0 => ⟨((552061750291959/562949953421312), (-45499064840637/1125899906842624)), (546065/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552061750291959/562949953421312), (-45499064840637/1125899906842624)), (2083072666648482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080929603283487/1125899906842624), (-89238104452851/1125899906842624)), (557571/562949953421312), by norm_num⟩
  | 2 => ⟨((515341266535189/562949953421312), (-171347574074315/1125899906842624)), (2317975/1125899906842624), by norm_num⟩
  | 3 => ⟨((917440783641171/1125899906842624), (-313713413792945/1125899906842624)), (4949421/1125899906842624), by norm_num⟩
  | 4 => ⟨((660166575178869/1125899906842624), (-511259444005223/1125899906842624)), (1353029/140737488355328), by norm_num⟩
  | 5 => ⟨((154928237260481/1125899906842624), (-599549558758349/1125899906842624)), (22523827/1125899906842624), by norm_num⟩
  | 6 => ⟨((-595891184763337/2251799813685248), (-660002941463703/4503599627370496)), (60373849/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1441860553/67108864)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1673948263/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((551908952577333/2251799813685248), (13194088765173/281474976710656)), (40884417/4503599627370496), by norm_num⟩
  | 1 => ⟨((-847113793/2147483648), (-324021403/4294967296)), (65/4294967296), by norm_num⟩
  | 2 => ⟨((1363377055/4294967296), (260746165/4294967296)), (27/2147483648), by norm_num⟩
  | 3 => ⟨((-365711787/2147483648), (-139884921/4294967296)), (15/2147483648), by norm_num⟩
  | 4 => ⟨((588590415/8589934592), (225136095/17179869184)), (25/8589934592), by norm_num⟩
  | 5 => ⟨((-757839783/34359738368), (-289874053/68719476736)), (67/68719476736), by norm_num⟩
  | 6 => ⟨((813130719/137438953472), (311022861/274877906944)), (37/137438953472), by norm_num⟩
  | 7 => ⟨((-373909545/274877906944), (-143020567/549755813888)), (35/549755813888), by norm_num⟩
  | 8 => ⟨((1203568395/4398046511104), (230182723/4398046511104)), (29/2199023255552), by norm_num⟩
  | 9 => ⟨((-215229845/4398046511104), (-164651023/17592186044416)), (43/17592186044416), by norm_num⟩
  | 10 => ⟨((138559629/17592186044416), (211996479/140737488355328)), (57/140737488355328), by norm_num⟩
  | 11 => ⟨((-1297472699/1125899906842624), (-124070971/562949953421312)), (69/1125899906842624), by norm_num⟩
  | 12 => ⟨((696067251/4503599627370496), (266246033/9007199254740992)), (19/2251799813685248), by norm_num⟩
  | 13 => ⟨((-1378802491/72057594037927936), (-263696283/72057594037927936)), (77/72057594037927936), by norm_num⟩
  | 14 => ⟨((634027715/288230376151711744), (242515883/576460752303423488)), (73/576460752303423488), by norm_num⟩
  | 15 => ⟨((-136057099/576460752303423488), (-208167603/4611686018427387904)), (65/4611686018427387904), by norm_num⟩
  | 16 => ⟨((1751803627/73786976294838206464), (654361/144115188075855872)), (107/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (246152350325/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779827897261165/633825300114114700748351602688), (145819272485/316912650057057350374175801344)), (46115/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472733308879511/9903520314283042199192993792), (10251656283/1237940039285380274899124224)), (6485/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890782613772123/2475880078570760549798248448), (1361355267/9671406556917033397649408)), (13781/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221556085881109/19342813113834066795298816), (348451425221/154742504910672534362390528)), (55125/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550732612827395/9671406556917033397649408), (163307115135/4835703278458516698824704)), (25841/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629910142716867/302231454903657293676544), (71432121155/151115727451828646838272)), (22611/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889468046944593/75557863725914323419136), (116049563599/18889465931478580854784)), (4593/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298796147358645/4722366482869645213696), (348052004075/4722366482869645213696)), (55119/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623175568973399/590295810358705651712), (478414445445/590295810358705651712)), (75791/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825633185728857/73786976294838206464), (298891282059/36893488147419103232)), (94743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825084236287985/9223372036854775808), (672181740627/9223372036854775808)), (53297/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399082857589925/288230376151711744), (335888711575/576460752303423488)), (53301/576460752303423488), by norm_num⟩
  | 5 => ⟨((598315830415511/72057594037927936), (293675357245/72057594037927936)), (11661/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494710799596595/36028797018963968), (880117825549/36028797018963968)), (139951/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493094272411119/9007199254740992), (1098559683905/9007199254740992)), (174973/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235605815425433/4503599627370496), (2192363896165/4503599627370496)), (175025/2251799813685248), by norm_num⟩
  | 1 => ⟨((2227551777789933/2251799813685248), (819170688637/562949953421312)), (262671/1125899906842624), by norm_num⟩
  | 0 => ⟨((275434403735853/281474976710656), (3253033186945/1125899906842624)), (1051757/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((275434403735853/281474976710656), (3253033186945/1125899906842624)), (4012134560591887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2156168914446757/2251799813685248), (12732886832781/2251799813685248)), (1032225/1125899906842624), by norm_num⟩
  | 2 => ⟨((2064527331855097/2251799813685248), (24384276624555/2251799813685248)), (3976899/2251799813685248), by norm_num⟩
  | 3 => ⟨((1892565442598403/2251799813685248), (44712682941847/2251799813685248)), (3689223/1125899906842624), by norm_num⟩
  | 4 => ⟨((794876327093037/1125899906842624), (2348723398593/70368744177664)), (6347857/1125899906842624), by norm_num⟩
  | 5 => ⟨((279961010357665/562949953421312), (106123515503843/2251799813685248)), (18773645/2251799813685248), by norm_num⟩
  | 6 => ⟨((551908952577333/2251799813685248), (13194088765173/281474976710656)), (40884417/4503599627370496), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1673948263/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-931788865/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-420244616146179/2251799813685248), (-464481285037025/4503599627370496)), (10696981/562949953421312), by norm_num⟩
  | 1 => ⟨((179523771/536870912), (99210589/536870912)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-1286653667/4294967296), (-711046049/4294967296)), (17/536870912), by norm_num⟩
  | 3 => ⟨((192114491/1073741824), (424674497/4294967296)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((-688445917/8589934592), (-760914551/17179869184)), (151/17179869184), by norm_num⟩
  | 5 => ⟨((986823593/34359738368), (545350341/34359738368)), (55/17179869184), by norm_num⟩
  | 6 => ⟨((-294691753/34359738368), (-651424425/137438953472)), (133/137438953472), by norm_num⟩
  | 7 => ⟨((301723851/137438953472), (166742269/137438953472)), (139/549755813888), by norm_num⟩
  | 8 => ⟨((-540616567/1099511627776), (-597524079/2199023255552)), (63/1099511627776), by norm_num⟩
  | 9 => ⟨((107628317/1099511627776), (59478857/1099511627776)), (51/4398046511104), by norm_num⟩
  | 10 => ⟨((-154275245/8796093022208), (-341029777/35184372088832)), (37/17592186044416), by norm_num⟩
  | 11 => ⟨((804142927/281474976710656), (444395151/281474976710656)), (49/140737488355328), by norm_num⟩
  | 12 => ⟨((-960553803/2251799813685248), (-530832813/2251799813685248)), (119/2251799813685248), by norm_num⟩
  | 13 => ⟨((529563499/9007199254740992), (4572715/140737488355328)), (133/18014398509481984), by norm_num⟩
  | 14 => ⟨((-1084400473/144115188075855872), (-149818613/36028797018963968)), (69/72057594037927936), by norm_num⟩
  | 15 => ⟨((1036258569/1152921504606846976), (572669693/1152921504606846976)), (67/576460752303423488), by norm_num⟩
  | 16 => ⟨((-232090763/2305843009213693952), (-513043173/9223372036854775808)), (61/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-3434636420105/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889788219775991/316912650057057350374175801344), (-4068263831859/633825300114114700748351602688)), (46301/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890649870957439/39614081257132168796771975168), (-4576149574133/39614081257132168796771975168)), (52101/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890480934228269/2475880078570760549798248448), (-1215347420023/618970019642690137449562112)), (13843/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221518290947063/19342813113834066795298816), (-2430262101457/77371252455336267181195264)), (55389/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550448428754785/9671406556917033397649408), (-1138955469881/2417851639229258349412352)), (51945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629785451352043/302231454903657293676544), (-996356148409/151115727451828646838272)), (22735/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472265361934299/18889465931478580854784), (-3237295413839/37778931862957161709568)), (73921/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298490015567349/4722366482869645213696), (-2427217261149/2361183241434822606848)), (27735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811376358990273/295147905179352825856), (-1668099009131/147573952589676412928)), (76319/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825101745111841/73786976294838206464), (-8336817971193/73786976294838206464)), (95469/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912241207213721/4611686018427387904), (-4686932180797/4611686018427387904)), (107501/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797862338172465/576460752303423488), (-1170943091067/144115188075855872)), (13453/144115188075855872), by norm_num⟩
  | 5 => ⟨((598047605872229/72057594037927936), (-4094746157601/72057594037927936)), (94309/144115188075855872), by norm_num⟩
  | 4 => ⟨((746947535339079/18014398509481984), (-12270020514195/36028797018963968)), (141739/36028797018963968), by norm_num⟩
  | 3 => ⟨((746027658510541/4503599627370496), (-3828161455841/2251799813685248)), (177657/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116735115875659/2251799813685248), (-15275329472493/2251799813685248)), (11149/140737488355328), by norm_num⟩
  | 1 => ⟨((1112102476731293/1125899906842624), (-5704928970465/281474976710656)), (67349/281474976710656), by norm_num⟩
  | 0 => ⟨((549053044630651/562949953421312), (-45266399554541/1125899906842624)), (273047/562949953421312), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549053044630651/562949953421312), (-45266399554541/1125899906842624)), (1041591646434593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1069178466956195/1125899906842624), (-88297918292171/1125899906842624)), (554569/562949953421312), by norm_num⟩
  | 2 => ⟨((1008389879888999/1125899906842624), (-10481197345041/70368744177664)), (1140245/562949953421312), by norm_num⟩
  | 3 => ⟨((109770763859697/140737488355328), (-37549104561161/140737488355328)), (4764295/1125899906842624), by norm_num⟩
  | 4 => ⟨((1209592181225657/2251799813685248), (-468593713085997/1125899906842624)), (19948497/2251799813685248), by norm_num⟩
  | 5 => ⟨((259700249353115/2251799813685248), (-1006852008914053/2251799813685248)), (19018133/1125899906842624), by norm_num⟩
  | 6 => ⟨((-420244616146179/2251799813685248), (-464481285037025/4503599627370496)), (10696981/562949953421312), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-931788865/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-252988395/8388608)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((64806415736471/1125899906842624), (199945161397037/1125899906842624)), (120312747/9007199254740992), by norm_num⟩
  | 1 => ⟨((-481061791/4294967296), (-1484204555/4294967296)), (113/4294967296), by norm_num⟩
  | 2 => ⟨((468051511/4294967296), (722032177/2147483648)), (7/268435456), by norm_num⟩
  | 3 => ⟨((-303595395/4294967296), (-936673161/4294967296)), (37/2147483648), by norm_num⟩
  | 4 => ⟨((36923085/1073741824), (911340905/8589934592)), (37/4294967296), by norm_num⟩
  | 5 => ⟨((-459833637/34359738368), (-1418710013/34359738368)), (117/34359738368), by norm_num⟩
  | 6 => ⟨((74566245/17179869184), (230056851/17179869184)), (39/34359738368), by norm_num⟩
  | 7 => ⟨((-20728459/17179869184), (-511622813/137438953472)), (11/34359738368), by norm_num⟩
  | 8 => ⟨((161342875/549755813888), (124446503/137438953472)), (87/1099511627776), by norm_num⟩
  | 9 => ⟨((-139537217/2199023255552), (-861019425/4398046511104)), (77/4398046511104), by norm_num⟩
  | 10 => ⟨((434443019/35184372088832), (670186575/17592186044416)), (61/17592186044416), by norm_num⟩
  | 11 => ⟨((-76853371/35184372088832), (-237113247/35184372088832)), (11/17592186044416), by norm_num⟩
  | 12 => ⟨((199399673/562949953421312), (76900179/70368744177664)), (29/281474976710656), by norm_num⟩
  | 13 => ⟨((-477555505/9007199254740992), (-46043335/281474976710656)), (141/9007199254740992), by norm_num⟩
  | 14 => ⟨((265508601/36028797018963968), (102395649/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 15 => ⟨((-275549803/288230376151711744), (-850144993/288230376151711744)), (85/288230376151711744), by norm_num⟩
  | 16 => ⟨((268097579/2305843009213693952), (827152885/2305843009213693952)), (21/576460752303423488), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (1637851398561/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779378156087115/633825300114114700748351602688), (1939579622125/633825300114114700748351602688)), (11549/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890427231749167/39614081257132168796771975168), (1090851123969/19807040628566084398385987584)), (6497/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890244923767189/2475880078570760549798248448), (1158830746493/1237940039285380274899124224)), (863/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1771910928496591/154742504910672534362390528), (144825925003/9671406556917033397649408)), (6905/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387557097854711/2417851639229258349412352), (2171914363051/9671406556917033397649408)), (12949/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259379019009469/604462909807314587353088), (1899950667315/604462909807314587353088)), (22665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888750852865251/75557863725914323419136), (771632642727/18889465931478580854784)), (73677/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649129066416901/2361183241434822606848), (2314120059775/4722366482869645213696)), (6909/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622435605977411/590295810358705651712), (3180651490559/590295810358705651712)), (38011/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824707942962085/73786976294838206464), (496739969183/9223372036854775808)), (23765/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456010735401519/2305843009213693952), (4468055897651/9223372036854775808)), (53495/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595289641218391/1152921504606846976), (4464803010797/1152921504606846976)), (13381/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195719540785261/144115188075855872), (3903045740401/144115188075855872)), (93733/144115188075855872), by norm_num⟩
  | 4 => ⟨((746670757363375/18014398509481984), (5847261328299/36028797018963968)), (70365/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491380742563849/9007199254740992), (7296303545093/9007199254740992)), (176143/9007199254740992), by norm_num⟩
  | 2 => ⟨((558043255733471/1125899906842624), (3638586553241/1125899906842624)), (352979/4503599627370496), by norm_num⟩
  | 1 => ⟨((277798548920637/281474976710656), (10868035778907/1125899906842624)), (531203/2251799813685248), by norm_num⟩
  | 0 => ⟨((2193092469042833/2251799813685248), (43091576987317/2251799813685248)), (1069369/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2193092469042833/2251799813685248), (43091576987317/2251799813685248)), (4079319008834075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((266886384867889/281474976710656), (20984061814847/562949953421312)), (2123907/2251799813685248), by norm_num⟩
  | 2 => ⟨((2021302512823941/2251799813685248), (39792953981595/562949953421312)), (4185993/2251799813685248), by norm_num⟩
  | 3 => ⟨((1803147933793471/2251799813685248), (285757543408087/2251799813685248)), (4053403/1125899906842624), by norm_num⟩
  | 4 => ⟨((703811475217595/1125899906842624), (57205698396311/281474976710656)), (15040727/2251799813685248), by norm_num⟩
  | 5 => ⟨((98363699803941/281474976710656), (572157815940393/2251799813685248)), (12458921/1125899906842624), by norm_num⟩
  | 6 => ⟨((64806415736471/1125899906842624), (199945161397037/1125899906842624)), (120312747/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-252988395/8388608)), (1/33554432), by norm_num⟩, -5, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-540697707/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1030900214488243/9007199254740992), (-1087626857032707/9007199254740992)), (21547827/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1022194257/4294967296), (1078441843/4294967296)), (87/2147483648), by norm_num⟩
  | 2 => ⟨((132849575/536870912), (-70079899/268435456)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-736674467/4294967296), (777210951/4294967296)), (131/4294967296), by norm_num⟩
  | 4 => ⟨((765935745/8589934592), (-808082369/8589934592)), (139/8589934592), by norm_num⟩
  | 5 => ⟨((-637087443/17179869184), (672144019/17179869184)), (59/8589934592), by norm_num⟩
  | 6 => ⟨((441595365/34359738368), (-931789463/68719476736)), (83/34359738368), by norm_num⟩
  | 7 => ⟨((-65590839/17179869184), (553600491/137438953472)), (101/137438953472), by norm_num⟩
  | 8 => ⟨((272784631/274877906944), (-575589929/549755813888)), (107/549755813888), by norm_num⟩
  | 9 => ⟨((-504213061/2199023255552), (1063916097/4398046511104)), (25/549755813888), by norm_num⟩
  | 10 => ⟨((209696317/4398046511104), (-221235133/4398046511104)), (169/17592186044416), by norm_num⟩
  | 11 => ⟨((-634256339/70368744177664), (669157129/70368744177664)), (65/35184372088832), by norm_num⟩
  | 12 => ⟨((439632993/281474976710656), (-927648755/562949953421312)), (183/562949953421312), by norm_num⟩
  | 13 => ⟨((-70322393/281474976710656), (296767901/1125899906842624)), (119/2251799813685248), by norm_num⟩
  | 14 => ⟨((668485967/18014398509481984), (-44079393/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 15 => ⟨((-741374661/144115188075855872), (782169779/144115188075855872)), (81/72057594037927936), by norm_num⟩
  | 16 => ⟨((385411317/576460752303423488), (-406619083/576460752303423488)), (171/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-528969893261/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779201684591559/633825300114114700748351602688), (-313149392481/158456325028528675187087900672)), (92323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472557199896175/9903520314283042199192993792), (-704474858273/19807040628566084398385987584)), (1623/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1890034213500105/2475880078570760549798248448), (-1496735140367/2475880078570760549798248448)), (110373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442925089389093/38685626227668133590597632), (-1496427053061/154742504910672534362390528)), (110383/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550031129134773/9671406556917033397649408), (-1402573103187/9671406556917033397649408)), (103495/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259206562413077/604462909807314587353088), (-1226924300401/604462909807314587353088)), (45285/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472117722015885/18889465931478580854784), (-996569377019/37778931862957161709568)), (36799/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298048401604939/4722366482869645213696), (-747158842829/2361183241434822606848)), (110415/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622147619113535/590295810358705651712), (-2053815575301/590295810358705651712)), (75925/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912174274628669/36893488147419103232), (-641490815257/18446744073709551616)), (5933/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1823639433973029/9223372036854775808), (-721228424337/2305843009213693952)), (13353/576460752303423488), by norm_num⟩
  | 6 => ⟨((99680446578255/72057594037927936), (-2882671579469/1152921504606846976)), (53431/288230376151711744), by norm_num⟩
  | 5 => ⟨((149421061663265/18014398509481984), (-2519817442685/144115188075855872)), (187093/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492817212411145/36028797018963968), (-471836407965/4503599627370496)), (280811/36028797018963968), by norm_num⟩
  | 3 => ⟨((745364663041579/4503599627370496), (-4709565317395/9007199254740992)), (21957/562949953421312), by norm_num⟩
  | 2 => ⟨((2230882037610399/4503599627370496), (-9392783535729/4503599627370496)), (21985/140737488355328), by norm_num⟩
  | 1 => ⟨((2220481404645121/2251799813685248), (-14023479418789/2251799813685248)), (264383/562949953421312), by norm_num⟩
  | 0 => ⟨((547348923986713/562949953421312), (-27785204126047/2251799813685248)), (1062051/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547348923986713/562949953421312), (-27785204126047/2251799813685248)), (4051403049949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064189069280247/1125899906842624), (-27015192893641/1125899906842624)), (2091447/1125899906842624), by norm_num⟩
  | 2 => ⟨((2010424812454797/2251799813685248), (-51068967689201/1125899906842624)), (8107989/2251799813685248), by norm_num⟩
  | 3 => ⟨((223786309965809/281474976710656), (-182379124760285/2251799813685248)), (15213285/2251799813685248), by norm_num⟩
  | 4 => ⟨((704298365550507/1125899906842624), (-290000566457835/2251799813685248)), (26654933/2251799813685248), by norm_num⟩
  | 5 => ⟨((843789226189261/2251799813685248), (-181407711044001/1125899906842624)), (40213165/2251799813685248), by norm_num⟩
  | 6 => ⟨((1030900214488243/9007199254740992), (-1087626857032707/9007199254740992)), (21547827/1125899906842624), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-540697707/16777216)), (1/16777216), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile003Terms0
